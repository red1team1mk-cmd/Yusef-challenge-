#!/usr/bin/env python3
"""
IRAQ AIR TRAFFIC MONITOR
========================
Telegram bot (long polling) + free community ADS-B feeds + SQLite.
Designed to run as a single Railway worker service (no HTTP port, no API key).

Data sources (tried in the order given by ADSB_PROVIDERS):
    adsb.fi         https://github.com/adsbfi/opendata  (official README)
                    GET /api/v3/lat/{lat}/lon/{lon}/dist/{nm}, max 250 NM,
                    1 request/second, personal non-commercial use, attribution.
    adsb.lol        https://github.com/adsblol/api  (ADSBExchange-v2 compatible)
    airplanes.live  https://airplanes.live/api-guide/
All three return readsb-style aircraft objects (hex, flight, r, t, desc,
alt_baro, gs, track, baro_rate, lat, lon, seen_pos, dbFlags, ownOp).

These feeds carry live positions only.  Route and aircraft details are added
from free lookup databases (class Enricher):
    adsbdb.com   GET https://api.adsbdb.com/v0/aircraft/{mode_s}?callsign={cs}
                 GET https://api.adsbdb.com/v0/callsign/{cs}
    hexdb.io     GET https://hexdb.io/api/v1/route/icao/{cs}   (route fallback)
A route found this way is the route usually flown under that callsign, taken
from a community database.  It is NOT a live flight plan and can be wrong or
missing.  Actual departure/arrival times are not available from any of these
sources and are shown as N/A.  There is no historical query: the archive is
whatever this bot has collected itself.

Crossing evidence policy
------------------------
A flight is stored only if at least one airborne position observation lies
inside the Iraq boundary polygon.  It is labelled CONFIRMED only when two or
more such observations at least 60 s apart exist.  A single observation is
labelled SINGLE_OBS and is never counted as a crossing in statistics.

Aircraft seen only outside the polygon (inside the three query circles, i.e.
up to ~250 NM around Iraq) are stored as NEARBY.  They appear in the
"AROUND IRAQ" view and in search, never in crossing lists or statistics, and
are deleted after NEARBY_RETENTION_DAYS.

Worldwide, on demand only: /world looks up one aircraft anywhere by callsign,
registration or ICAO24 hex, and /near (or a shared Telegram location) lists
aircraft around any point.  These use the feeds' per-aircraft and point
endpoints (adsb.fi: /v2/callsign, /v2/registration, /v2/hex, verified in its
README; the adsb.lol and airplanes.live paths are unverified).  Results are
stored as WORLD and deleted on the same schedule as NEARBY.
"""
from __future__ import annotations

import asyncio
import csv
import fcntl
import hashlib
import hmac
import html
import io
import json
import logging
import math
import os
import platform
import random
import re
import signal
import sqlite3
import sys
import time
import urllib.parse
from datetime import datetime, timedelta, timezone
from typing import Any, Optional
from zoneinfo import ZoneInfo

import aiosqlite
import httpx
from aiohttp import web
from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    LinkPreviewOptions,
    MenuButtonWebApp,
    Update,
    WebAppInfo,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest, Conflict, Forbidden, RetryAfter, TelegramError
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    TypeHandler,
    filters,
)

try:  # optional, local development only
    from dotenv import load_dotenv

    load_dotenv()
except Exception:  # pragma: no cover
    pass

# --------------------------------------------------------------------------
# CONSTANTS
# --------------------------------------------------------------------------
# provider id -> (display name, home page, URL template)
PROVIDERS = {
    "adsbfi": ("adsb.fi", "https://adsb.fi",
               "https://opendata.adsb.fi/api/v3/lat/{lat}/lon/{lon}/dist/{dist}"),
    "adsblol": ("adsb.lol", "https://adsb.lol",
                "https://api.adsb.lol/v2/lat/{lat}/lon/{lon}/dist/{dist}"),
    "airplaneslive": ("airplanes.live", "https://airplanes.live",
                      "https://api.airplanes.live/v2/point/{lat}/{lon}/{dist}"),
    # OpenSky is a separate receiver network with a different API (see AdsbClient._opensky).
    "opensky": ("OpenSky", "https://opensky-network.org", ""),
}
OPENSKY_URL = "https://opensky-network.org/api/states/all"
OPENSKY_MIN_GAP = 600  # seconds between calls: keeps anonymous use inside the daily credit allowance
EMERGENCY_SQUAWKS = {"7500": "HIJACK", "7600": "RADIO", "7700": "EMERGENCY"}
# Three 250 NM circles (the maximum radius the feeds allow) that together cover Iraq.
QUERY_RADIUS_NM = 250
QUERY_CIRCLES = [(33.0, 41.6), (35.2, 44.6), (31.2, 46.0)]
# Per-aircraft lookup URLs for the worldwide on-demand search.
LOOKUP_URLS = {
    "adsbfi": {"callsign": "https://opendata.adsb.fi/api/v2/callsign/{q}",
               "reg": "https://opendata.adsb.fi/api/v2/registration/{q}",
               "hex": "https://opendata.adsb.fi/api/v2/hex/{q}"},
    "adsblol": {"callsign": "https://api.adsb.lol/v2/callsign/{q}",
                "reg": "https://api.adsb.lol/v2/reg/{q}",
                "hex": "https://api.adsb.lol/v2/hex/{q}"},
    "airplaneslive": {"callsign": "https://api.airplanes.live/v2/callsign/{q}",
                      "reg": "https://api.airplanes.live/v2/reg/{q}",
                      "hex": "https://api.airplanes.live/v2/hex/{q}"},
}
WORLD_LIST_LIMIT = 40
MAX_POSITION_AGE = 300  # seconds; older positions are ignored. Each position is
                        # stored with its own true timestamp (feed time - age).
APP_NAME = "IRAQ AIR TRAFFIC MONITOR"
APP_VERSION = "4.0.0"

# Simplified Iraq land-boundary polygon (lon, lat), clockwise from the
# Turkey/Syria/Iraq tripoint.  Accuracy is roughly 10-20 km: flights that only
# graze the border may be classified either way.
IRAQ_POLYGON: list[tuple[float, float]] = [
    (42.36, 37.11), (42.78, 37.38), (43.90, 37.25), (44.79, 37.15),
    (45.40, 36.00), (46.35, 35.80), (46.00, 35.20), (45.65, 34.55),
    (45.50, 33.95), (46.17, 33.12), (47.30, 32.47), (47.85, 31.70),
    (47.70, 31.00), (48.03, 30.46), (48.57, 29.93), (47.97, 30.00),
    (47.70, 30.10), (47.11, 29.96), (46.55, 29.10), (44.72, 29.20),
    (42.08, 31.11), (40.40, 31.95), (39.20, 32.16), (38.79, 33.38),
    (41.00, 34.42), (41.20, 35.20), (41.38, 35.63), (41.29, 36.36),
    (41.84, 36.60),
]
BBOX = {
    "minLatitude": min(p[1] for p in IRAQ_POLYGON),
    "maxLatitude": max(p[1] for p in IRAQ_POLYGON),
    "minLongitude": min(p[0] for p in IRAQ_POLYGON),
    "maxLongitude": max(p[0] for p in IRAQ_POLYGON),
}

SAME_CROSSING_GAP = timedelta(hours=3)   # same aircraft+callsign within gap = same crossing
CONFIRM_MIN_SECONDS = 60                 # min spread between observations to confirm
PAGE_SIZE = 8                            # flights per Telegram list page
NOT_AIRBORNE = {"ON_GROUND", "LANDED", "SCHEDULED", "CANCELLED"}
NA = "N/A"
SEP = "━" * 28
SUB = "─" * 28

log = logging.getLogger("iatm")


# --------------------------------------------------------------------------
# LOGGING (structured JSON on stdout -> Railway logs)
# --------------------------------------------------------------------------
class JsonFormatter(logging.Formatter):
    def format(self, record: logging.LogRecord) -> str:
        payload = {
            "ts": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "level": record.levelname,
            "logger": record.name,
            "msg": record.getMessage(),
        }
        extra = getattr(record, "data", None)
        if isinstance(extra, dict):
            payload.update(extra)
        if record.exc_info:
            payload["exc"] = self.formatException(record.exc_info)
        return json.dumps(payload, ensure_ascii=False, default=str)


def setup_logging() -> None:
    handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(JsonFormatter())
    root = logging.getLogger()
    root.handlers[:] = [handler]
    root.setLevel(os.getenv("LOG_LEVEL", "INFO").upper())
    # httpx logs full request URLs at INFO; Telegram URLs contain the bot token.
    for noisy in ("httpx", "httpcore", "telegram", "telegram.ext", "aiosqlite"):
        logging.getLogger(noisy).setLevel(logging.WARNING)


def ev(msg: str, **data: Any) -> None:
    log.info(msg, extra={"data": data})


# --------------------------------------------------------------------------
# CONFIG
# --------------------------------------------------------------------------
class ConfigError(Exception):
    pass


class Config:
    def __init__(self) -> None:
        errors: list[str] = []
        self.bot_token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
        if not self.bot_token:
            errors.append("TELEGRAM_BOT_TOKEN is missing")
        raw = os.getenv("ADSB_PROVIDERS", "").strip() or "adsbfi,adsblol,airplaneslive,opensky"
        self.providers = [x.strip().lower() for x in raw.split(",") if x.strip()]
        for name in self.providers:
            if name not in PROVIDERS:
                errors.append(f"ADSB_PROVIDERS: unknown provider {name!r} "
                              f"(valid: {', '.join(PROVIDERS)})")

        self.admin_ids: set[int] = set()
        for part in os.getenv("ADMIN_IDS", "").replace(";", ",").split(","):
            part = part.strip()
            if not part:
                continue
            if part.lstrip("-").isdigit():
                self.admin_ids.add(int(part))
            else:
                errors.append(f"ADMIN_IDS contains a non-numeric value: {part!r}")

        self.db_path = os.getenv("DATABASE_PATH", "/data/iraq_air_traffic.db").strip()
        self.sync_interval = self._int("SYNC_INTERVAL", 300, 60, errors)
        tz_name = os.getenv("TIMEZONE", "Asia/Baghdad").strip() or "Asia/Baghdad"
        try:
            self.tz = ZoneInfo(tz_name)
        except Exception:
            errors.append(f"TIMEZONE {tz_name!r} is not a valid IANA zone")
            self.tz = timezone.utc  # type: ignore[assignment]
        self.tz_name = tz_name

        # Optional tuning (all have safe defaults)
        self.track_retention_days = self._int("TRACK_RETENTION_DAYS", 90, 0, errors)
        self.nearby_retention_days = self._int("NEARBY_RETENTION_DAYS", 3, 1, errors)

        # Branding and mandatory channel subscription
        self.dev_username = (os.getenv("DEV_USERNAME", "").strip() or "krofullpower").lstrip("@")
        self.channel = (os.getenv("REQUIRED_CHANNEL", "").strip() or "dlxfullpower").lstrip("@")
        self.force_sub = os.getenv("FORCE_SUBSCRIBE", "true").strip().lower() in ("1", "true", "yes", "on")

        # Mini App (web console).  Railway sets PORT and, once a domain is generated,
        # RAILWAY_PUBLIC_DOMAIN (https://docs.railway.com/reference/variables).
        self.webapp_enabled = os.getenv("WEBAPP_ENABLED", "true").strip().lower() in ("1", "true", "yes", "on")
        self.port = self._int("PORT", 8080, 1, errors)
        url = os.getenv("WEBAPP_URL", "").strip().rstrip("/")
        domain = os.getenv("RAILWAY_PUBLIC_DOMAIN", "").strip()
        if not url and domain:
            url = f"https://{domain}"
        if url and not url.startswith("https://"):
            errors.append("WEBAPP_URL must start with https:// (Telegram opens Mini Apps over HTTPS only)")
        self.webapp_url = (url + "/") if url else ""

        if errors:
            raise ConfigError("; ".join(errors))

    @staticmethod
    def _int(name: str, default: int, minimum: int, errors: list[str]) -> int:
        raw = os.getenv(name, "").strip()
        if not raw:
            return default
        try:
            value = int(raw)
        except ValueError:
            errors.append(f"{name} must be an integer")
            return default
        if value < minimum:
            errors.append(f"{name} must be >= {minimum}")
        return value

    def check_storage(self) -> None:
        """Refuse to start if history would be written to ephemeral storage."""
        directory = os.path.dirname(os.path.abspath(self.db_path)) or "."
        on_railway = bool(os.getenv("RAILWAY_ENVIRONMENT") or os.getenv("RAILWAY_PROJECT_ID"))
        mount = os.getenv("RAILWAY_VOLUME_MOUNT_PATH", "").rstrip("/")
        if on_railway:
            if not mount:
                raise ConfigError(
                    "No Railway Volume is attached to this service. Attach a volume "
                    f"mounted at {directory} so the SQLite archive survives restarts."
                )
            if not (os.path.abspath(self.db_path) + "/").startswith(mount + "/"):
                raise ConfigError(
                    f"DATABASE_PATH ({self.db_path}) is not inside the Railway Volume "
                    f"mount ({mount}). Historical records would be lost on redeploy."
                )
        if not os.path.isdir(directory):
            raise ConfigError(
                f"Database directory {directory} does not exist. On Railway, attach a "
                f"Volume mounted at {directory}. Locally, create it or set DATABASE_PATH."
            )
        if not os.access(directory, os.W_OK):
            raise ConfigError(f"Database directory {directory} is not writable.")


# --------------------------------------------------------------------------
# TIME / PARSE HELPERS
# --------------------------------------------------------------------------
def now_utc() -> datetime:
    return datetime.now(timezone.utc).replace(microsecond=0)


def iso(dt: datetime) -> str:
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def parse_dt(value: Any) -> Optional[datetime]:
    """Parse an API timestamp (ISO-8601 string, or epoch seconds/milliseconds)."""
    if value is None or value == "":
        return None
    try:
        if isinstance(value, (int, float)):
            v = float(value)
            if v > 1e11:
                v /= 1000.0
            return datetime.fromtimestamp(v, timezone.utc).replace(microsecond=0)
        text = str(value).strip()
        if text.isdigit():
            return parse_dt(int(text))
        dt = datetime.fromisoformat(text.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc).replace(microsecond=0)
    except Exception:
        return None


def clean_str(value: Any) -> Optional[str]:
    if value is None:
        return None
    text = str(value).strip()
    return text or None


def clean_num(value: Any) -> Optional[float]:
    if value is None or isinstance(value, bool):
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def dist_nm(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    la1, lo1, la2, lo2 = map(math.radians, (lat1, lon1, lat2, lon2))
    h = math.sin((la2 - la1) / 2) ** 2 + math.cos(la1) * math.cos(la2) * math.sin((lo2 - lo1) / 2) ** 2
    return 2 * 3440.065 * math.asin(min(1.0, math.sqrt(h)))


def in_region(lat: float, lon: float) -> bool:
    """Inside the area the bot monitors continuously (Iraq and ~250 NM around it)."""
    return any(dist_nm(lat, lon, c[0], c[1]) <= QUERY_RADIUS_NM for c in QUERY_CIRCLES)


def point_in_iraq(lat: float, lon: float) -> bool:
    if not (BBOX["minLatitude"] <= lat <= BBOX["maxLatitude"]
            and BBOX["minLongitude"] <= lon <= BBOX["maxLongitude"]):
        return False
    inside = False
    n = len(IRAQ_POLYGON)
    j = n - 1
    for i in range(n):
        xi, yi = IRAQ_POLYGON[i]
        xj, yj = IRAQ_POLYGON[j]
        if (yi > lat) != (yj > lat):
            x_cross = (xj - xi) * (lat - yi) / (yj - yi) + xi
            if lon < x_cross:
                inside = not inside
        j = i
    return inside


# --------------------------------------------------------------------------
# ADS-B FEED CLIENT
# --------------------------------------------------------------------------
class ApiError(Exception):
    pass


class ApiRateLimited(ApiError):
    pass


AIRLINE_CALLSIGN = re.compile(r"^[A-Z]{3}[0-9]")


class AdsbClient:
    MAX_ATTEMPTS = 3
    MIN_REQUEST_GAP = 1.2  # feeds allow 1 request/second; stay under it

    def __init__(self, providers: list[str]) -> None:
        self.providers = providers
        self._client = httpx.AsyncClient(
            headers={"Accept": "application/json",
                     "User-Agent": f"iraq-air-traffic-monitor/{APP_VERSION}"},
            timeout=httpx.Timeout(25.0, connect=10.0), follow_redirects=True)
        self._gate = asyncio.Lock()
        self._last_request = 0.0
        self.last_ok: Optional[datetime] = None
        self.last_error: Optional[str] = None
        self.last_latency_ms: Optional[int] = None
        self.last_provider: Optional[str] = None
        self._os_last = -1e9
        self._os_ok_at = -1e9

    async def close(self) -> None:
        await self._client.aclose()

    async def _get(self, url: str) -> dict:
        last_exc: Exception = ApiError("no attempt made")
        for attempt in range(1, self.MAX_ATTEMPTS + 1):
            async with self._gate:
                wait = self.MIN_REQUEST_GAP - (time.monotonic() - self._last_request)
                if wait > 0:
                    await asyncio.sleep(wait)
                started = time.monotonic()
                try:
                    resp = await self._client.get(url)
                except (httpx.TimeoutException, httpx.TransportError) as exc:
                    resp = None
                    last_exc = ApiError(f"network error: {type(exc).__name__}")
                finally:
                    self._last_request = time.monotonic()
            delay = min(30.0, 2.0 ** attempt) + random.uniform(0, 1)
            if resp is not None:
                self.last_latency_ms = int((time.monotonic() - started) * 1000)
                if resp.status_code == 429:
                    last_exc = ApiRateLimited("rate limited (HTTP 429)")
                    retry_after = resp.headers.get("Retry-After", "")
                    if retry_after.isdigit():
                        delay = min(60.0, float(retry_after))
                elif resp.status_code >= 500:
                    last_exc = ApiError(f"server error (HTTP {resp.status_code})")
                elif resp.status_code >= 400:
                    # 4xx means the request itself is refused: do not hammer the feed.
                    raise ApiError(f"request refused (HTTP {resp.status_code})")
                else:
                    try:
                        data = resp.json()
                    except ValueError:
                        raise ApiError("invalid JSON in feed response")
                    if not isinstance(data, dict):
                        raise ApiError("unexpected feed response shape")
                    return data
            if attempt < self.MAX_ATTEMPTS:
                log.warning("feed retry", extra={"data": {
                    "attempt": attempt, "delay": round(delay, 1), "reason": str(last_exc)}})
                await asyncio.sleep(delay)
        raise last_exc

    @staticmethod
    def normalize(ac: dict, feed_now: datetime, provider: str) -> Optional[dict]:
        """Convert one readsb aircraft object to the record shape Database.ingest expects.
        Returns None when there is no fresh position."""
        lat, lon = clean_num(ac.get("lat")), clean_num(ac.get("lon"))
        if lat is None or lon is None:
            return None
        age = clean_num(ac.get("seen_pos"))
        if age is None:
            age = clean_num(ac.get("seen")) or 0.0
        if age > MAX_POSITION_AGE:
            return None
        baro = ac.get("alt_baro")
        on_ground = isinstance(baro, str) and baro.strip().lower() == "ground"
        altitude = 0.0 if on_ground else clean_num(baro)
        if altitude is None:
            altitude = clean_num(ac.get("alt_geom"))
        callsign = (clean_str(ac.get("flight")) or "").upper() or None
        hex_code = (clean_str(ac.get("hex")) or "").upper() or None
        flags = clean_num(ac.get("dbFlags"))
        rate = clean_num(ac.get("baro_rate"))
        nav_alt = clean_num(ac.get("nav_altitude_mcp"))
        return {
            "callsign": callsign,
            "aircraftModeS": hex_code,
            "aircraftRegistration": clean_str(ac.get("r")),
            "aircraftType": clean_str(ac.get("t")),
            "aircraftTypeDescription": clean_str(ac.get("desc")),
            # ICAO convention: airline callsigns start with the 3-letter operator
            # designator.  This is an inference from the callsign, not feed data.
            "airlineIcao": callsign[:3] if callsign and AIRLINE_CALLSIGN.match(callsign) else None,
            "aircraftClasses": ["MILITARY"] if flags is not None and int(flags) & 1 else None,
            "ownerOperator": clean_str(ac.get("ownOp")),
            "latitude": lat, "longitude": lon, "altitude": altitude,
            "groundSpeed": clean_num(ac.get("gs")), "heading": clean_num(ac.get("track")),
            "verticalRate": rate if rate is not None else clean_num(ac.get("geom_rate")),
            "status": "ON_GROUND" if on_ground else "IN_FLIGHT",
            "updated": iso(feed_now - timedelta(seconds=max(0.0, age))),
            "source": provider,
            # Extended telemetry (present only when the aircraft broadcasts it)
            "squawk": clean_str(ac.get("squawk")),
            "emergency": None if (clean_str(ac.get("emergency")) or "none").lower() == "none"
            else clean_str(ac.get("emergency")),
            "category": clean_str(ac.get("category")),
            "altGeom": clean_num(ac.get("alt_geom")),
            "mach": clean_num(ac.get("mach")), "ias": clean_num(ac.get("ias")),
            "tas": clean_num(ac.get("tas")),
            "navAltitude": nav_alt if nav_alt is not None else clean_num(ac.get("nav_altitude_fms")),
            "navHeading": clean_num(ac.get("nav_heading")),
            "windDir": clean_num(ac.get("wd")), "windSpeed": clean_num(ac.get("ws")),
            "oat": clean_num(ac.get("oat")),
            "posSource": clean_str(ac.get("type")),
            "originCountry": None,
        }

    async def _snapshot_from(self, provider: str) -> tuple[list[dict], int]:
        """Returns (records with a usable position, raw aircraft count)."""
        template = PROVIDERS[provider][2]
        merged: dict[str, dict] = {}
        raw_count = 0
        for lat, lon in QUERY_CIRCLES:
            data = await self._get(template.format(lat=lat, lon=lon, dist=QUERY_RADIUS_NM))
            aircraft = data.get("ac")
            if aircraft is None:
                aircraft = data.get("aircraft")
            if not isinstance(aircraft, list):
                keys = ",".join(sorted(str(k) for k in data.keys()))[:80]
                raise ApiError(f"no aircraft list in response (keys: {keys})")
            raw_count += len(aircraft)
            feed_now = parse_dt(data.get("now")) or now_utc()
            if abs((feed_now - now_utc()).total_seconds()) > 120:
                feed_now = now_utc()
            for ac in aircraft:
                if not isinstance(ac, dict):
                    continue
                try:
                    record = self.normalize(ac, feed_now, provider)
                except Exception:
                    record = None
                if not record:
                    continue
                key = record["aircraftModeS"] or record["aircraftRegistration"] or record["callsign"]
                if key and (key not in merged or record["updated"] > merged[key]["updated"]):
                    merged[key] = record
        return list(merged.values()), raw_count

    @staticmethod
    def _merge(merged: dict[str, dict], record: dict) -> None:
        """Keep the freshest record per aircraft, filling its gaps from the other source."""
        key = record["aircraftModeS"] or record["aircraftRegistration"] or record["callsign"]
        if not key:
            return
        current = merged.get(key)
        if current is None:
            merged[key] = record
            return
        newer, older = (record, current) if record["updated"] > current["updated"] else (current, record)
        for field, value in older.items():
            if newer.get(field) is None and value is not None:
                newer[field] = value
        merged[key] = newer

    async def _opensky(self) -> tuple[list[dict], int]:
        """OpenSky Network state vectors for the Iraq bounding box (anonymous access).
        State vector layout: 0 icao24, 1 callsign, 2 origin_country, 3 time_position,
        5 longitude, 6 latitude, 7 baro_altitude m, 8 on_ground, 9 velocity m/s,
        10 true_track, 11 vertical_rate m/s, 13 geo_altitude m, 14 squawk."""
        self._os_last = time.monotonic()
        params = {"lamin": BBOX["minLatitude"], "lomin": BBOX["minLongitude"],
                  "lamax": BBOX["maxLatitude"], "lomax": BBOX["maxLongitude"]}
        try:
            resp = await self._client.get(OPENSKY_URL, params=params)
        except (httpx.TimeoutException, httpx.TransportError) as exc:
            raise ApiError(f"network error: {type(exc).__name__}")
        if resp.status_code != 200:
            # Rate limited or refused (OpenSky blocks some hosting providers): rest for an hour.
            self._os_last = time.monotonic() + 3600 - OPENSKY_MIN_GAP
            raise ApiError(f"HTTP {resp.status_code}; paused 1h")
        try:
            data = resp.json()
        except ValueError:
            raise ApiError("invalid JSON")
        states = data.get("states") if isinstance(data, dict) else None
        states = states if isinstance(states, list) else []
        now = now_utc()
        out: list[dict] = []
        for st in states:
            try:
                if not isinstance(st, list) or len(st) < 15:
                    continue
                lat, lon, ts = clean_num(st[6]), clean_num(st[5]), parse_dt(st[3])
                if lat is None or lon is None or ts is None:
                    continue
                if (now - ts).total_seconds() > MAX_POSITION_AGE:
                    continue
                callsign = (clean_str(st[1]) or "").upper() or None
                on_ground = bool(st[8])
                baro, geo = clean_num(st[7]), clean_num(st[13])
                speed, vrate = clean_num(st[9]), clean_num(st[11])
                out.append({
                    "callsign": callsign, "aircraftModeS": (clean_str(st[0]) or "").upper() or None,
                    "aircraftRegistration": None, "aircraftType": None, "aircraftTypeDescription": None,
                    "airlineIcao": callsign[:3] if callsign and AIRLINE_CALLSIGN.match(callsign) else None,
                    "aircraftClasses": None, "ownerOperator": None,
                    "latitude": lat, "longitude": lon,
                    "altitude": 0.0 if on_ground else (baro * 3.28084 if baro is not None else
                                                       (geo * 3.28084 if geo is not None else None)),
                    "groundSpeed": speed * 1.94384 if speed is not None else None,
                    "heading": clean_num(st[10]),
                    "verticalRate": vrate * 196.85 if vrate is not None else None,
                    "status": "ON_GROUND" if on_ground else "IN_FLIGHT",
                    "updated": iso(ts), "source": "opensky",
                    "squawk": clean_str(st[14]), "emergency": None, "category": None,
                    "altGeom": geo * 3.28084 if geo is not None else None,
                    "mach": None, "ias": None, "tas": None, "navAltitude": None, "navHeading": None,
                    "windDir": None, "windSpeed": None, "oat": None, "posSource": "opensky",
                    "originCountry": clean_str(st[2]),
                })
            except Exception:
                continue
        return out, len(states)

    def _records(self, data: dict, provider: str) -> list[dict]:
        aircraft = data.get("ac")
        if aircraft is None:
            aircraft = data.get("aircraft")
        if not isinstance(aircraft, list):
            raise ApiError("no aircraft list in response")
        feed_now = parse_dt(data.get("now")) or now_utc()
        if abs((feed_now - now_utc()).total_seconds()) > 120:
            feed_now = now_utc()
        out = []
        for ac in aircraft:
            if isinstance(ac, dict):
                try:
                    record = self.normalize(ac, feed_now, provider)
                except Exception:
                    record = None
                if record:
                    out.append(record)
        return out

    async def _first(self, urls: list[tuple[str, str]]) -> tuple[list[dict], str, int]:
        """Ask providers in turn; return the first non-empty answer.
        Returns (records, provider name, providers that answered)."""
        answered = 0
        for provider, url in urls:
            try:
                records = self._records(await self._get(url), provider)
            except ApiError as exc:
                log.warning("world lookup failed", extra={"data": {"provider": provider, "error": str(exc)}})
                continue
            answered += 1
            if records:
                return records, PROVIDERS[provider][0], answered
        return [], "", answered

    async def find(self, kind: str, query: str) -> tuple[list[dict], str, int]:
        """One aircraft anywhere in the world by callsign / registration / hex."""
        return await self._first([(p, LOOKUP_URLS[p][kind].format(q=query))
                                  for p in self.providers if p in LOOKUP_URLS])

    async def around(self, lat: float, lon: float, radius_nm: int) -> tuple[list[dict], str, int]:
        """Aircraft within radius_nm (max 250) of any point on Earth."""
        radius_nm = max(1, min(QUERY_RADIUS_NM, radius_nm))
        return await self._first([
            (p, PROVIDERS[p][2].format(lat=round(lat, 4), lon=round(lon, 4), dist=radius_nm))
            for p in self.providers if PROVIDERS[p][2]])

    async def snapshot(self) -> tuple[list[dict], str, str]:
        """Current aircraft around Iraq, merged from every configured provider so
        that one feed's coverage gaps are filled by the others.
        Returns (records, providers that answered, per-provider note)."""
        merged: dict[str, dict] = {}
        notes: list[str] = []
        errors: list[str] = []
        answered: list[str] = []
        recent: list[str] = []   # sources polled less often that answered a moment ago
        for provider in self.providers:
            name = PROVIDERS[provider][0]
            try:
                if provider == "opensky":
                    if time.monotonic() - self._os_last < OPENSKY_MIN_GAP:
                        notes.append(f"{name} (not due)")
                        if time.monotonic() - self._os_ok_at < 2 * OPENSKY_MIN_GAP:
                            recent.append(name)
                        continue
                    records, raw_count = await self._opensky()
                    self._os_ok_at = time.monotonic()
                else:
                    records, raw_count = await self._snapshot_from(provider)
            except ApiError as exc:
                errors.append(f"{name}: {exc}")
                notes.append(f"{name} ERR {str(exc)[:60]}")
                log.warning("feed failed", extra={"data": {"provider": provider, "error": str(exc)}})
                continue
            answered.append(name)
            notes.append(f"{name} {len(records)}/{raw_count}")
            for record in records:
                self._merge(merged, record)
        if not answered:
            self.last_error = "; ".join(errors)[:300]
            if errors and all("429" in e for e in errors):
                raise ApiRateLimited(self.last_error)
            raise ApiError(self.last_error)
        self.last_ok = now_utc()
        self.last_error = "; ".join(errors)[:300] or None
        self.last_provider = ", ".join(answered + recent)
        return list(merged.values()), self.last_provider, "; ".join(notes)


# --------------------------------------------------------------------------
# ROUTE / AIRCRAFT ENRICHMENT (adsbdb.com, hexdb.io)
# --------------------------------------------------------------------------
def traffic_type(dep_country: Optional[str], arr_country: Optional[str]) -> str:
    if not (dep_country and arr_country):
        return "UNKNOWN"
    if dep_country == "IQ" and arr_country == "IQ":
        return "DOMESTIC"
    if dep_country == "IQ":
        return "DEPARTURE"
    if arr_country == "IQ":
        return "ARRIVAL"
    return "OVERFLIGHT"


ROUTE_COLS = ["airline_name", "airline_iata", "callsign_iata", "dep_icao", "dep_iata", "dep_name",
              "dep_city", "dep_country", "arr_icao", "arr_iata", "arr_name", "arr_city", "arr_country",
              "dep_lat", "dep_lon", "arr_lat", "arr_lon"]


class Enricher:
    """Looks up the usual route of a callsign and the registry details of an
    aircraft.  Every answer (including "unknown") is cached in SQLite, so each
    callsign/aircraft costs at most one lookup per cache period."""
    ADSBDB = "https://api.adsbdb.com/v0"
    HEXDB = "https://hexdb.io/api/v1"
    ROUTESET = "https://api.adsb.lol/api/0/routeset"
    PHOTOS = "https://api.planespotters.net/pub/photos/hex"
    ROUTE_TTL = timedelta(days=30)
    ROUTE_MISS_TTL = timedelta(days=3)
    AIRCRAFT_TTL = timedelta(days=60)

    def __init__(self, db: "Database") -> None:
        self.db = db
        self._client = httpx.AsyncClient(
            headers={"Accept": "application/json",
                     "User-Agent": f"iraq-air-traffic-monitor/{APP_VERSION}"},
            timeout=httpx.Timeout(12.0, connect=6.0), follow_redirects=True)
        self._gate = asyncio.Lock()
        self._last_request = 0.0
        self.paused: dict[str, datetime] = {}   # host -> paused until
        self.lookups = 0
        self.last_error: Optional[str] = None

    async def close(self) -> None:
        await self._client.aclose()

    async def _get(self, url: str, body: Any = None) -> tuple[int, Any]:
        """One polite request (POST when body is given). Returns (status, json-or-None);
        0 = not attempted or network failure."""
        host = httpx.URL(url).host
        until = self.paused.get(host)
        if until and now_utc() < until:
            return 0, None
        async with self._gate:
            wait = 1.0 - (time.monotonic() - self._last_request)
            if wait > 0:
                await asyncio.sleep(wait)
            try:
                if body is None:
                    resp = await self._client.get(url)
                else:
                    resp = await self._client.post(url, json=body)
            except (httpx.TimeoutException, httpx.TransportError) as exc:
                self.last_error = f"{host}: network error {type(exc).__name__}"
                return 0, None
            finally:
                self._last_request = time.monotonic()
        self.lookups += 1
        if resp.status_code in (401, 403, 429) or resp.status_code >= 500:
            # Back off instead of pressing a busy, limiting or refusing service.
            self.paused[host] = now_utc() + timedelta(minutes=15)
            self.last_error = f"{host}: HTTP {resp.status_code}; paused 15 min"
            return resp.status_code, None
        try:
            return resp.status_code, resp.json()
        except ValueError:
            return resp.status_code, None

    @property
    def all_paused(self) -> bool:
        until = self.paused.get(httpx.URL(self.ADSBDB).host)
        return bool(until and now_utc() < until)

    @staticmethod
    def _airport(a: Any, prefix: str) -> dict:
        a = a if isinstance(a, dict) else {}
        country = clean_str(a.get("country_iso_name"))
        return {f"{prefix}_icao": clean_str(a.get("icao_code")), f"{prefix}_iata": clean_str(a.get("iata_code")),
                f"{prefix}_name": clean_str(a.get("name")), f"{prefix}_city": clean_str(a.get("municipality")),
                f"{prefix}_country": country.upper() if country else None,
                f"{prefix}_lat": clean_num(a.get("latitude")), f"{prefix}_lon": clean_num(a.get("longitude"))}

    def _parse_route(self, fr: Any) -> Optional[dict]:
        if not isinstance(fr, dict):
            return None
        route = {**self._airport(fr.get("origin"), "dep"), **self._airport(fr.get("destination"), "arr")}
        if not (route["dep_icao"] or route["dep_iata"]) or not (route["arr_icao"] or route["arr_iata"]):
            return None
        airline = fr.get("airline") if isinstance(fr.get("airline"), dict) else {}
        route.update({"airline_name": clean_str(airline.get("name")),
                      "airline_iata": clean_str(airline.get("iata")),
                      "callsign_iata": clean_str(fr.get("callsign_iata")), "source": "adsbdb"})
        return route

    async def _route_adsblol(self, row: sqlite3.Row) -> Optional[dict]:
        """adsb.lol route database (the one used by the tar1090 map). The service also
        says whether the route is plausible for the aircraft's current position."""
        if row["latitude"] is None:
            return None
        status, data = await self._get(self.ROUTESET, {"planes": [
            {"callsign": row["callsign"], "lat": row["latitude"], "lng": row["longitude"]}]})
        item = data[0] if status == 200 and isinstance(data, list) and data and isinstance(data[0], dict) else None
        if not item or item.get("plausible") in (False, 0):
            return None
        airports = item.get("_airports")
        if not isinstance(airports, list) or len(airports) < 2:
            return None

        def side(a: Any, prefix: str) -> dict:
            a = a if isinstance(a, dict) else {}
            country = clean_str(a.get("countryiso2"))
            return {f"{prefix}_icao": clean_str(a.get("icao")), f"{prefix}_iata": clean_str(a.get("iata")),
                    f"{prefix}_name": clean_str(a.get("name")), f"{prefix}_city": clean_str(a.get("location")),
                    f"{prefix}_country": country.upper() if country else None,
                    f"{prefix}_lat": clean_num(a.get("lat")), f"{prefix}_lon": clean_num(a.get("lon"))}
        route = {c: None for c in ROUTE_COLS}
        route.update(side(airports[0], "dep"))
        route.update(side(airports[-1], "arr"))
        if not route["dep_icao"] or not route["arr_icao"]:
            return None
        route["source"] = "adsb.lol"
        return route

    async def _route_hexdb(self, callsign: str) -> tuple[Optional[dict], bool]:
        status, data = await self._get(f"{self.HEXDB}/route/icao/{callsign}")
        text = clean_str(data.get("route")) if isinstance(data, dict) else None
        if not (status == 200 and text):
            return None, status in (200, 404)
        parts = [x.strip().upper() for x in text.split("-") if x.strip()]
        if len(parts) < 2:
            return None, True
        route = {c: None for c in ROUTE_COLS}
        route.update({"dep_icao": parts[0], "arr_icao": parts[-1], "source": "hexdb"})
        for prefix in ("dep", "arr"):   # airport names and coordinates
            st, ap = await self._get(f"{self.HEXDB}/airport/icao/{route[prefix + '_icao']}")
            if st == 200 and isinstance(ap, dict):
                country = clean_str(ap.get("country_code"))
                route.update({f"{prefix}_iata": clean_str(ap.get("iata")),
                              f"{prefix}_name": clean_str(ap.get("airport")),
                              f"{prefix}_city": clean_str(ap.get("region_name")),
                              f"{prefix}_country": country.upper() if country else None,
                              f"{prefix}_lat": clean_num(ap.get("latitude")),
                              f"{prefix}_lon": clean_num(ap.get("longitude"))})
        return route, True

    async def _aircraft_fallback(self, ac_key: str, row: sqlite3.Row) -> None:
        """hexdb.io registry record and a planespotters.net photo page for one aircraft."""
        hex_code = row["mode_s"] if row["mode_s"] and not row["mode_s"].startswith("~") else None
        if not hex_code:
            return
        known = await self.db.one("SELECT type_icao, manufacturer, photo_url FROM aircraft WHERE key=?",
                                  (ac_key,))
        if not known or not known["manufacturer"]:
            status, data = await self._get(f"{self.HEXDB}/aircraft/{hex_code}")
            if status == 200 and isinstance(data, dict) and data.get("Registration"):
                await self._save_aircraft(ac_key, row, {
                    "registration": data.get("Registration"), "icao_type": data.get("ICAOTypeCode"),
                    "type": data.get("Type"), "registered_owner": data.get("RegisteredOwners"),
                    "manufacturer": data.get("Manufacturer")})
        if not known or not known["photo_url"]:
            status, data = await self._get(f"{self.PHOTOS}/{hex_code}")
            photos = data.get("photos") if isinstance(data, dict) else None
            if status == 200 and isinstance(photos, list) and photos and isinstance(photos[0], dict):
                link = clean_str(photos[0].get("link"))
                if link and link.startswith("https://"):
                    await self.db.run("UPDATE aircraft SET photo_url=?, photo_credit=? WHERE key=?",
                                      (link, clean_str(photos[0].get("photographer")), ac_key))

    async def _save_route(self, callsign: str, route: Optional[dict]) -> None:
        values = [(route or {}).get(c) for c in ROUTE_COLS]
        await self.db.run(
            f"INSERT OR REPLACE INTO route_cache(callsign, found, source, {','.join(ROUTE_COLS)}, fetched_utc) "
            f"VALUES(?,?,?,{','.join('?' * len(ROUTE_COLS))},?)",
            (callsign, 1 if route else 0, (route or {}).get("source"), *values, iso(now_utc())))

    async def _save_aircraft(self, key: str, row: sqlite3.Row, ac: Any) -> None:
        ac = ac if isinstance(ac, dict) else {}
        stamp = iso(now_utc())
        await self.db.run(
            "INSERT INTO aircraft(key, registration, mode_s, type_icao, type_desc, operator_name, "
            "manufacturer, owner_country, photo_url, detail_fetched_utc, first_seen_utc, last_seen_utc) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(key) DO UPDATE SET "
            "registration=COALESCE(excluded.registration, registration), "
            "mode_s=COALESCE(excluded.mode_s, mode_s), "
            "type_icao=COALESCE(excluded.type_icao, type_icao), "
            "type_desc=COALESCE(excluded.type_desc, type_desc), "
            "operator_name=COALESCE(excluded.operator_name, operator_name), "
            "manufacturer=COALESCE(excluded.manufacturer, manufacturer), "
            "owner_country=COALESCE(excluded.owner_country, owner_country), "
            "photo_url=COALESCE(excluded.photo_url, photo_url), "
            "detail_fetched_utc=excluded.detail_fetched_utc",
            (key, clean_str(ac.get("registration")) or row["registration"],
             (clean_str(ac.get("mode_s")) or row["mode_s"] or "").upper() or None,
             clean_str(ac.get("icao_type")), clean_str(ac.get("type")),
             clean_str(ac.get("registered_owner")), clean_str(ac.get("manufacturer")),
             clean_str(ac.get("registered_owner_country_name")),
             clean_str(ac.get("url_photo")), stamp, stamp, stamp))

    async def enrich(self, flight_id: int) -> None:
        """Fill route and aircraft details for one flight. Never raises."""
        try:
            await self._enrich(flight_id)
        except Exception:
            log.exception("enrichment failed")

    async def _enrich(self, flight_id: int) -> None:
        row = await self.db.one("SELECT * FROM flights WHERE id=?", (flight_id,))
        if not row:
            return
        now = now_utc()
        callsign = row["callsign"]
        # Only airline-style callsigns (3 letters + digit) have database routes.
        want_route = bool(callsign and AIRLINE_CALLSIGN.match(callsign) and not row["route_checked_utc"])
        if not want_route and not row["route_checked_utc"]:
            # Nothing to look up (no callsign, or not an airline callsign): settle it.
            await self.db.run("UPDATE flights SET route_checked_utc=? WHERE id=?", (iso(now), flight_id))
        route: Optional[dict] = None
        route_done = not want_route
        if want_route:
            cached = await self.db.one("SELECT * FROM route_cache WHERE callsign=?", (callsign,))
            if cached:
                ttl = self.ROUTE_TTL if cached["found"] else self.ROUTE_MISS_TTL
                if now - parse_dt(cached["fetched_utc"]) < ttl:  # type: ignore[operator]
                    route_done = True
                    if cached["found"]:
                        route = {c: cached[c] for c in ROUTE_COLS}
                        route["source"] = cached["source"]

        ac_id = row["mode_s"] if row["mode_s"] and not row["mode_s"].startswith("~") else row["registration"]
        ac_key = row["registration"] or row["mode_s"]
        want_aircraft = False
        if ac_id and ac_key:
            fetched = parse_dt(await self.db.scalar(
                "SELECT detail_fetched_utc FROM aircraft WHERE key=?", (ac_key,)))
            want_aircraft = fetched is None or now - fetched > self.AIRCRAFT_TTL
        elif ac_key and not ac_id:
            # Non-ICAO address and no registration: no registry lookup is possible.
            if not await self.db.scalar("SELECT detail_fetched_utc FROM aircraft WHERE key=?", (ac_key,)):
                await self._save_aircraft(ac_key, row, None)

        asked = False  # True once a lookup service actually answered about the route
        if want_aircraft:
            url = f"{self.ADSBDB}/aircraft/{ac_id}"
            if not route_done:
                url += f"?callsign={callsign}"
            status, data = await self._get(url)
            resp = data.get("response") if isinstance(data, dict) else None
            if status == 200 and isinstance(resp, dict):
                await self._save_aircraft(ac_key, row, resp.get("aircraft"))
                if not route_done:
                    route = self._parse_route(resp.get("flightroute"))
                    route_done = route is not None
                    if route:
                        await self._save_route(callsign, route)
            elif status == 404:
                await self._save_aircraft(ac_key, row, None)  # remember "unknown"
            if status in (200, 404):
                await self._aircraft_fallback(ac_key, row)
        if not route_done:
            status, data = await self._get(f"{self.ADSBDB}/callsign/{callsign}")
            resp = data.get("response") if isinstance(data, dict) else None
            if status == 200 and isinstance(resp, dict):
                route = self._parse_route(resp.get("flightroute"))
            asked = status in (200, 404)
            if route is None:
                route = await self._route_adsblol(row)
            if route is None:
                route, answered = await self._route_hexdb(callsign)
                asked = asked or answered
            if route is not None or asked:
                await self._save_route(callsign, route)
                route_done = True

        if want_route and route_done:
            if route:
                dep_c, arr_c = route.get("dep_country"), route.get("arr_country")
                await self.db.run(
                    "UPDATE flights SET airline_name=COALESCE(?, airline_name), "
                    "airline_iata=COALESCE(?, airline_iata), flight_number_iata=COALESCE(?, flight_number_iata), "
                    "dep_icao=?, dep_iata=?, dep_name=?, dep_city=?, dep_country=?, "
                    "arr_icao=?, arr_iata=?, arr_name=?, arr_city=?, arr_country=?, "
                    "dep_lat=?, dep_lon=?, arr_lat=?, arr_lon=?, "
                    "traffic_type=?, route_source=?, route_checked_utc=? WHERE id=?",
                    (*[route.get(c) for c in ROUTE_COLS], traffic_type(dep_c, arr_c),
                     route.get("source"), iso(now), flight_id))
                if route.get("airline_name") and row["airline_icao"]:
                    await self.db.run("UPDATE airlines SET name=COALESCE(name, ?), iata=COALESCE(iata, ?) "
                                      "WHERE icao=?", (route["airline_name"], route.get("airline_iata"),
                                                       row["airline_icao"]))
            else:
                await self.db.run("UPDATE flights SET route_checked_utc=? WHERE id=?", (iso(now), flight_id))

    async def background(self, limit: int, stop: asyncio.Event) -> int:
        """Enrich recent flights seen inside Iraq that have not been looked up yet."""
        rows = await self.db.q(
            "SELECT f.id FROM flights f LEFT JOIN aircraft a ON a.key=COALESCE(f.registration, f.mode_s) "
            "WHERE f.crossing_status IN ('CONFIRMED','SINGLE_OBS') AND f.last_seen_utc>=? AND "
            "(f.route_checked_utc IS NULL OR "
            " (a.key IS NOT NULL AND a.detail_fetched_utc IS NULL)) "
            "ORDER BY f.last_seen_utc DESC LIMIT ?",
            (iso(now_utc() - timedelta(hours=6)), limit))
        done = 0
        for r in rows:
            if stop.is_set() or self.all_paused:
                break
            await self.enrich(r["id"])
            done += 1
        return done


# --------------------------------------------------------------------------
# DATABASE
# --------------------------------------------------------------------------
SCHEMA = """
CREATE TABLE IF NOT EXISTS flights (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ident_key TEXT NOT NULL,
    callsign TEXT, flight_number_iata TEXT, flight_number_icao TEXT,
    airline_icao TEXT, airline_iata TEXT, airline_name TEXT,
    aircraft_type TEXT, aircraft_type_desc TEXT, aircraft_classes TEXT,
    registration TEXT, mode_s TEXT,
    dep_icao TEXT, dep_iata TEXT, dep_name TEXT, dep_city TEXT, dep_country TEXT,
    arr_icao TEXT, arr_iata TEXT, arr_name TEXT, arr_city TEXT, arr_country TEXT,
    dep_time_utc TEXT, dep_time_kind TEXT,
    arr_time_utc TEXT, arr_time_kind TEXT,
    api_status TEXT,
    first_seen_utc TEXT NOT NULL,
    last_seen_utc TEXT NOT NULL,
    obs_count INTEGER NOT NULL DEFAULT 0,
    altitude_ft REAL, ground_speed_kt REAL, heading REAL,
    latitude REAL, longitude REAL,
    crossing_status TEXT NOT NULL DEFAULT 'SINGLE_OBS',
    traffic_type TEXT NOT NULL DEFAULT 'UNKNOWN',
    data_source TEXT,
    created_utc TEXT NOT NULL,
    updated_utc TEXT NOT NULL
);
CREATE UNIQUE INDEX IF NOT EXISTS ux_flights_identity
    ON flights(ident_key, COALESCE(callsign, ''), first_seen_utc);
CREATE INDEX IF NOT EXISTS ix_flights_last_seen ON flights(last_seen_utc);
CREATE INDEX IF NOT EXISTS ix_flights_ident ON flights(ident_key, last_seen_utc);
CREATE INDEX IF NOT EXISTS ix_flights_callsign ON flights(callsign);
CREATE INDEX IF NOT EXISTS ix_flights_reg ON flights(registration);
CREATE INDEX IF NOT EXISTS ix_flights_airline ON flights(airline_icao);
CREATE INDEX IF NOT EXISTS ix_flights_type ON flights(aircraft_type);

CREATE TABLE IF NOT EXISTS track_observations (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    flight_id INTEGER NOT NULL REFERENCES flights(id) ON DELETE CASCADE,
    ts_utc TEXT NOT NULL,
    latitude REAL NOT NULL, longitude REAL NOT NULL,
    altitude_ft REAL, ground_speed_kt REAL, heading REAL, vertical_rate REAL,
    on_ground INTEGER, in_iraq INTEGER NOT NULL, source TEXT,
    UNIQUE(flight_id, ts_utc)
);
CREATE INDEX IF NOT EXISTS ix_obs_ts ON track_observations(ts_utc);

CREATE TABLE IF NOT EXISTS aircraft (
    key TEXT PRIMARY KEY,
    registration TEXT, mode_s TEXT, serial_number TEXT,
    type_icao TEXT, type_desc TEXT, class_desc TEXT,
    operator_icao TEXT, operator_name TEXT,
    first_flight TEXT, decommissioned INTEGER,
    detail_fetched_utc TEXT,
    first_seen_utc TEXT NOT NULL, last_seen_utc TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS airlines (
    icao TEXT PRIMARY KEY, iata TEXT, name TEXT,
    first_seen_utc TEXT NOT NULL, last_seen_utc TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS sync_history (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    kind TEXT NOT NULL, trigger TEXT NOT NULL,
    started_utc TEXT NOT NULL, finished_utc TEXT,
    status TEXT NOT NULL,
    received INTEGER DEFAULT 0, in_iraq INTEGER DEFAULT 0,
    inserted INTEGER DEFAULT 0, updated INTEGER DEFAULT 0, skipped INTEGER DEFAULT 0,
    detail TEXT
);
CREATE INDEX IF NOT EXISTS ix_sync_started ON sync_history(started_utc);

CREATE TABLE IF NOT EXISTS api_status (
    key TEXT PRIMARY KEY, value TEXT, updated_utc TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS route_cache (
    callsign TEXT PRIMARY KEY, found INTEGER NOT NULL, source TEXT,
    airline_name TEXT, airline_iata TEXT, callsign_iata TEXT,
    dep_icao TEXT, dep_iata TEXT, dep_name TEXT, dep_city TEXT, dep_country TEXT,
    arr_icao TEXT, arr_iata TEXT, arr_name TEXT, arr_city TEXT, arr_country TEXT,
    fetched_utc TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS users (
    user_id INTEGER PRIMARY KEY, username TEXT, lang TEXT NOT NULL DEFAULT 'en',
    alerts INTEGER NOT NULL DEFAULT 0,
    first_seen_utc TEXT NOT NULL, last_seen_utc TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS watch (
    user_id INTEGER NOT NULL, ident TEXT NOT NULL, created_utc TEXT NOT NULL,
    PRIMARY KEY(user_id, ident)
);

CREATE TABLE IF NOT EXISTS notified (
    user_id INTEGER NOT NULL, flight_id INTEGER NOT NULL, kind TEXT NOT NULL,
    PRIMARY KEY(user_id, flight_id, kind)
);

CREATE TABLE IF NOT EXISTS runs (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    started_utc TEXT NOT NULL, stopped_utc TEXT, stop_reason TEXT, deployment TEXT
);
"""

# db column -> normalized record field (see AdsbClient.normalize). Airport and time
# fields are kept in the schema but the ADS-B feeds do not provide them.
FLIGHT_TEXT_FIELDS = {
    "callsign": "callsign",
    "flight_number_iata": "flightNumberIata",
    "flight_number_icao": "flightNumberIcao",
    "airline_icao": "airlineIcao",
    "airline_iata": "airlineIata",
    "airline_name": "airlineName",
    "aircraft_type": "aircraftType",
    "aircraft_type_desc": "aircraftTypeDescription",
    "registration": "aircraftRegistration",
    "mode_s": "aircraftModeS",
    "dep_icao": "depAirportIcao", "dep_iata": "depAirportIata",
    "dep_name": "depAirportName", "dep_city": "depAirportCity",
    "dep_country": "depAirportCountryIso2",
    "arr_icao": "arrAirportIcao", "arr_iata": "arrAirportIata",
    "arr_name": "arrAirportName", "arr_city": "arrAirportCity",
    "arr_country": "arrAirportCountryIso2",
    "api_status": "status",
}
UPPER_COLS = {"callsign", "flight_number_iata", "flight_number_icao", "airline_icao",
              "airline_iata", "aircraft_type", "registration", "mode_s", "dep_icao",
              "dep_iata", "arr_icao", "arr_iata", "dep_country", "arr_country", "api_status"}
# db column -> normalized record key: latest broadcast telemetry kept on the flight row
EXTRA_FIELDS = {
    "squawk": "squawk", "emergency": "emergency", "category": "category",
    "alt_geom_ft": "altGeom", "vertical_rate": "verticalRate", "mach": "mach", "ias_kt": "ias",
    "tas_kt": "tas", "nav_altitude_ft": "navAltitude", "nav_heading": "navHeading",
    "wind_dir": "windDir", "wind_kt": "windSpeed", "oat_c": "oat", "pos_source": "posSource",
    "origin_country": "originCountry",
}
DEP_TIME_FIELDS = [("actualDeparture", "ACTUAL"), ("actualTakeoff", "ACTUAL"),
                   ("estimatedDeparture", "ESTIMATED"), ("scheduledDeparture", "SCHEDULED")]
ARR_TIME_FIELDS = [("actualArrival", "ACTUAL"), ("actualLanding", "ACTUAL"),
                   ("estimatedArrival", "ESTIMATED"), ("scheduledArrival", "SCHEDULED")]


class Database:
    def __init__(self, path: str) -> None:
        self.path = path
        self.conn: Optional[aiosqlite.Connection] = None
        self.write_lock = asyncio.Lock()

    async def open(self) -> None:
        self.conn = await aiosqlite.connect(self.path, isolation_level=None)
        self.conn.row_factory = sqlite3.Row
        await self.conn.execute("PRAGMA journal_mode=WAL")
        await self.conn.execute("PRAGMA synchronous=NORMAL")
        await self.conn.execute("PRAGMA foreign_keys=ON")
        await self.conn.execute("PRAGMA busy_timeout=10000")
        await self.conn.executescript(SCHEMA)
        # Columns added after the first release (existing databases are upgraded in place).
        for table, column in (("flights", "route_source TEXT"), ("flights", "route_checked_utc TEXT"),
                              ("aircraft", "manufacturer TEXT"), ("aircraft", "owner_country TEXT"),
                              ("aircraft", "photo_url TEXT"), ("aircraft", "photo_credit TEXT"),
                              *[("flights", f"{c} TEXT") for c in (
                                  "squawk", "emergency", "category", "pos_source", "origin_country")],
                              *[("flights", f"{c} REAL") for c in (
                                  "alt_geom_ft", "vertical_rate", "mach", "ias_kt", "tas_kt",
                                  "nav_altitude_ft", "nav_heading", "wind_dir", "wind_kt", "oat_c",
                                  "dep_lat", "dep_lon", "arr_lat", "arr_lon")],
                              *[("route_cache", f"{c} REAL") for c in (
                                  "dep_lat", "dep_lon", "arr_lat", "arr_lon")]):
            async with self.conn.execute(f"PRAGMA table_info({table})") as cur:
                present = {row[1] for row in await cur.fetchall()}
            if column.split()[0] not in present:
                await self.conn.execute(f"ALTER TABLE {table} ADD COLUMN {column}")

    async def close(self) -> None:
        if self.conn:
            try:
                await self.conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
            except Exception:
                pass
            await self.conn.close()
            self.conn = None

    async def q(self, sql: str, args: tuple = ()) -> list[sqlite3.Row]:
        assert self.conn
        async with self.conn.execute(sql, args) as cur:
            return list(await cur.fetchall())

    async def one(self, sql: str, args: tuple = ()) -> Optional[sqlite3.Row]:
        rows = await self.q(sql, args)
        return rows[0] if rows else None

    async def scalar(self, sql: str, args: tuple = ()) -> Any:
        row = await self.one(sql, args)
        return row[0] if row else None

    async def run(self, sql: str, args: tuple = ()) -> int:
        assert self.conn
        async with self.write_lock:
            cur = await self.conn.execute(sql, args)
            rowid = cur.lastrowid or 0
            await cur.close()
            return rowid

    async def set_status(self, key: str, value: str) -> None:
        await self.run(
            "INSERT INTO api_status(key, value, updated_utc) VALUES(?,?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value, updated_utc=excluded.updated_utc",
            (key, value, iso(now_utc())))

    async def get_status(self, key: str) -> Optional[str]:
        return await self.scalar("SELECT value FROM api_status WHERE key=?", (key,))

    # ---------------------------------------------------------------- ingest
    async def ingest(self, flights: list[dict], source: str, now: datetime) -> dict:
        """Store a batch of ApiFlight objects. One bad record never aborts the batch."""
        assert self.conn
        res = {"received": len(flights), "in_iraq": 0, "nearby": 0, "inserted": 0, "updated": 0,
               "skipped": 0, "no_evidence": 0, "ids": []}
        async with self.write_lock:
            await self.conn.execute("BEGIN IMMEDIATE")
            try:
                for raw in flights:
                    await self.conn.execute("SAVEPOINT flight")
                    try:
                        outcome, zone = await self._ingest_one(raw, source, now)
                        await self.conn.execute("RELEASE flight")
                    except Exception as exc:
                        await self.conn.execute("ROLLBACK TO flight")
                        await self.conn.execute("RELEASE flight")
                        outcome, zone = "skipped", ""
                        log.warning("flight record skipped", extra={"data": {
                            "error": f"{type(exc).__name__}: {exc}"}})
                    if outcome in ("inserted", "updated"):
                        res["in_iraq" if zone == "IRAQ" else "nearby"] += 1
                        res["ids"].append(self._last_id)
                    if outcome in res:
                        res[outcome] += 1
                await self.conn.execute("COMMIT")
            except Exception:
                await self.conn.execute("ROLLBACK")
                raise
        return res

    @staticmethod
    def _observations(raw: dict, source: str, now: datetime) -> list[dict]:
        obs: list[dict] = []
        status = (clean_str(raw.get("status")) or "").upper()
        positions = raw.get("positions")
        if isinstance(positions, list):
            for p in positions:
                if not isinstance(p, dict):
                    continue
                ts = parse_dt(p.get("timestamp"))
                lat, lon = clean_num(p.get("latitude")), clean_num(p.get("longitude"))
                if ts is None or lat is None or lon is None or ts > now + timedelta(minutes=5):
                    continue
                on_ground = p.get("onGround") if isinstance(p.get("onGround"), bool) else None
                obs.append({
                    "ts": ts, "lat": lat, "lon": lon,
                    "alt": clean_num(p.get("altitude")), "gs": clean_num(p.get("groundSpeed")),
                    "hdg": clean_num(p.get("heading")), "vr": clean_num(p.get("verticalRate")),
                    "ground": on_ground, "src": clean_str(p.get("source")),
                })
        if source in ("LIVE", "WORLD"):
            # The top-level position of a live flight is its current position.
            lat, lon = clean_num(raw.get("latitude")), clean_num(raw.get("longitude"))
            if lat is not None and lon is not None:
                ts = parse_dt(raw.get("updated"))
                if ts is None or ts > now:
                    ts = now
                if now - ts <= timedelta(minutes=30):  # ignore stale last-known positions
                    obs.append({
                        "ts": ts, "lat": lat, "lon": lon,
                        "alt": clean_num(raw.get("altitude")), "gs": clean_num(raw.get("groundSpeed")),
                        "hdg": clean_num(raw.get("heading")), "vr": clean_num(raw.get("verticalRate")),
                        "ground": True if status in NOT_AIRBORNE else None,
                        "src": clean_str(raw.get("source")),
                    })
        for o in obs:
            airborne = o["ground"] is not True
            o["in_iraq"] = bool(airborne and -90 <= o["lat"] <= 90 and point_in_iraq(o["lat"], o["lon"]))
        return obs

    async def _ingest_one(self, raw: dict, source: str, now: datetime) -> tuple[str, str]:
        assert self.conn
        # Aircraft on the ground are not air traffic: ignore those positions.
        obs = [o for o in self._observations(raw, source, now) if o["ground"] is not True]
        if not obs:
            return "no_evidence", ""
        inside = [o for o in obs if o["in_iraq"]]
        span = inside or obs  # nearby-only aircraft are matched on all their positions

        fields: dict[str, Optional[str]] = {}
        for col, api_field in FLIGHT_TEXT_FIELDS.items():
            value = clean_str(raw.get(api_field))
            if value and col in UPPER_COLS:
                value = value.upper()
            fields[col] = value
        classes = raw.get("aircraftClasses")
        fields["aircraft_classes"] = (
            ",".join(sorted(str(c) for c in classes if c)) or None
            if isinstance(classes, list) else None)
        for prefix, candidates in (("dep", DEP_TIME_FIELDS), ("arr", ARR_TIME_FIELDS)):
            fields[f"{prefix}_time_utc"] = None
            fields[f"{prefix}_time_kind"] = None
            for api_field, kind in candidates:
                dt = parse_dt(raw.get(api_field))
                if dt:
                    fields[f"{prefix}_time_utc"] = iso(dt)
                    fields[f"{prefix}_time_kind"] = kind
                    break

        for col, key in EXTRA_FIELDS.items():
            fields[col] = raw.get(key)

        if fields["mode_s"]:
            ident = "H:" + fields["mode_s"]
        elif fields["registration"]:
            ident = "R:" + fields["registration"]
        elif fields["callsign"]:
            ident = "C:" + fields["callsign"]
        else:
            return "skipped", ""  # no usable identity at all

        t_min = min(o["ts"] for o in span)
        t_max = max(o["ts"] for o in span)
        async with self.conn.execute(
            "SELECT * FROM flights WHERE ident_key=? AND last_seen_utc>=? AND first_seen_utc<=? "
            "AND (callsign IS NULL OR ? IS NULL OR callsign=?) ORDER BY last_seen_utc DESC LIMIT 1",
            (ident, iso(t_min - SAME_CROSSING_GAP), iso(t_max + SAME_CROSSING_GAP),
             fields["callsign"], fields["callsign"])) as cur:
            existing = await cur.fetchone()

        stamp = iso(now)
        if existing is None:
            cols = ["ident_key", *fields.keys(), "first_seen_utc", "last_seen_utc",
                    "data_source", "created_utc", "updated_utc"]
            vals = [ident, *fields.values(), iso(t_min), iso(t_max), source, stamp, stamp]
            cur = await self.conn.execute(
                f"INSERT INTO flights({','.join(cols)}) VALUES({','.join('?' * len(cols))})", vals)
            flight_id = cur.lastrowid
            await cur.close()
            outcome = "inserted"
        else:
            flight_id = existing["id"]
            # Newer non-empty values replace stored ones; missing values never erase data.
            sets = ", ".join(f"{c}=COALESCE(?, {c})" for c in fields)
            await self.conn.execute(
                f"UPDATE flights SET {sets}, updated_utc=? WHERE id=?",
                (*fields.values(), stamp, flight_id))
            outcome = "updated"

        for o in obs:
            await self.conn.execute(
                "INSERT OR IGNORE INTO track_observations(flight_id, ts_utc, latitude, longitude, "
                "altitude_ft, ground_speed_kt, heading, vertical_rate, on_ground, in_iraq, source) "
                "VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                (flight_id, iso(o["ts"]), o["lat"], o["lon"], o["alt"], o["gs"], o["hdg"], o["vr"],
                 None if o["ground"] is None else int(o["ground"]), int(o["in_iraq"]), o["src"]))

        async with self.conn.execute(
            "SELECT MIN(ts_utc), MAX(ts_utc), COUNT(*) FROM track_observations "
            "WHERE flight_id=? AND in_iraq=1", (flight_id,)) as cur:
            first, last, count = await cur.fetchone()
        if count:
            zone = "IRAQ"
            spread = (parse_dt(last) - parse_dt(first)).total_seconds()  # type: ignore[operator]
            crossing = "CONFIRMED" if count >= 2 and spread >= CONFIRM_MIN_SECONDS else "SINGLE_OBS"
            pos_filter = "AND in_iraq=1"
        else:
            # Never observed inside Iraq: NEARBY if within the monitored region,
            # otherwise WORLD (found by an on-demand worldwide lookup).
            pos_filter = ""
            async with self.conn.execute(
                "SELECT MIN(ts_utc), MAX(ts_utc) FROM track_observations WHERE flight_id=?",
                (flight_id,)) as cur:
                first, last = await cur.fetchone()
            newest = max(obs, key=lambda o: o["ts"])
            zone = crossing = "NEARBY" if in_region(newest["lat"], newest["lon"]) else "WORLD"
        async with self.conn.execute(
            "SELECT latitude, longitude, altitude_ft, ground_speed_kt, heading FROM track_observations "
            f"WHERE flight_id=? {pos_filter} ORDER BY ts_utc DESC LIMIT 1", (flight_id,)) as cur:
            latest = await cur.fetchone()

        dep_c = fields["dep_country"] or (existing["dep_country"] if existing else None)
        arr_c = fields["arr_country"] or (existing["arr_country"] if existing else None)
        traffic = traffic_type(dep_c, arr_c)

        await self.conn.execute(
            "UPDATE flights SET first_seen_utc=?, last_seen_utc=?, obs_count=?, crossing_status=?, "
            "traffic_type=?, latitude=?, longitude=?, altitude_ft=?, ground_speed_kt=?, heading=? "
            "WHERE id=?",
            (first, last, count, crossing, traffic, latest[0], latest[1], latest[2], latest[3],
             latest[4], flight_id))

        if fields["airline_icao"]:
            await self.conn.execute(
                "INSERT INTO airlines(icao, iata, name, first_seen_utc, last_seen_utc) VALUES(?,?,?,?,?) "
                "ON CONFLICT(icao) DO UPDATE SET iata=COALESCE(excluded.iata, iata), "
                "name=COALESCE(excluded.name, name), last_seen_utc=excluded.last_seen_utc",
                (fields["airline_icao"], fields["airline_iata"], fields["airline_name"], stamp, stamp))
        ac_key = fields["registration"] or fields["mode_s"]
        if ac_key:
            await self.conn.execute(
                "INSERT INTO aircraft(key, registration, mode_s, type_icao, type_desc, operator_icao, "
                "operator_name, first_seen_utc, last_seen_utc) VALUES(?,?,?,?,?,?,?,?,?) "
                "ON CONFLICT(key) DO UPDATE SET registration=COALESCE(excluded.registration, registration), "
                "mode_s=COALESCE(excluded.mode_s, mode_s), type_icao=COALESCE(excluded.type_icao, type_icao), "
                "type_desc=COALESCE(excluded.type_desc, type_desc), "
                "operator_name=COALESCE(excluded.operator_name, operator_name), "
                "last_seen_utc=excluded.last_seen_utc",
                (ac_key, fields["registration"], fields["mode_s"], fields["aircraft_type"],
                 fields["aircraft_type_desc"], None, clean_str(raw.get("ownerOperator")),
                 stamp, stamp))
        self._last_id = flight_id
        return outcome, zone


# --------------------------------------------------------------------------
# SYNCHRONISATION SERVICE
# --------------------------------------------------------------------------
class SyncService:
    def __init__(self, cfg: Config, db: Database, api: AdsbClient) -> None:
        self.cfg, self.db, self.api = cfg, db, api
        self.lock = asyncio.Lock()
        self.stop = asyncio.Event()
        self.next_run: Optional[datetime] = None
        self.cycles = 0
        self.enricher: Optional[Enricher] = None
        self.after_sync: Any = None   # async callable: sends alerts / watchlist notifications

    async def _record(self, trigger: str, started: datetime, status: str,
                      res: Optional[dict] = None, detail: str = "") -> dict:
        res = res or {}
        row = {
            "kind": "LIVE", "trigger": trigger, "status": status,
            "received": res.get("received", 0), "in_iraq": res.get("in_iraq", 0),
            "nearby": res.get("nearby", 0),
            "inserted": res.get("inserted", 0), "updated": res.get("updated", 0),
            "skipped": res.get("skipped", 0) + res.get("no_evidence", 0), "detail": detail[:500],
        }
        try:
            await self.db.run(
                "INSERT INTO sync_history(kind, trigger, started_utc, finished_utc, status, received, "
                "in_iraq, inserted, updated, skipped, detail) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                ("LIVE", trigger, iso(started), iso(now_utc()), status, row["received"], row["in_iraq"],
                 row["inserted"], row["updated"], row["skipped"], row["detail"]))
        except Exception:
            log.exception("could not record sync result")
        ev("sync finished", **row)
        return row

    async def sync_live(self, trigger: str = "auto") -> dict:
        async with self.lock:
            started = now_utc()
            try:
                flights, provider, note = await self.api.snapshot()
            except ApiRateLimited as exc:
                await self.db.set_status("live_access", "RATE LIMITED")
                return await self._record(trigger, started, "RATE_LIMITED", detail=str(exc))
            except ApiError as exc:
                await self.db.set_status("live_access", "UNAVAILABLE")
                return await self._record(trigger, started, "API_ERROR", detail=str(exc))
            try:
                res = await self.db.ingest(flights, "LIVE", now_utc())
            except Exception as exc:
                log.exception("database error during live sync")
                return await self._record(trigger, started, "DB_ERROR",
                                          detail=f"{type(exc).__name__}: {exc}")
            await self.db.set_status("live_access", "OK")
            await self.db.set_status("provider", provider)
            return await self._record(trigger, started, "OK", res, note)

    async def _maintenance(self) -> None:
        days = self.cfg.track_retention_days
        if days > 0:
            cutoff = iso(now_utc() - timedelta(days=days))
            await self.db.run("DELETE FROM track_observations WHERE ts_utc<?", (cutoff,))
        # Aircraft that never entered Iraq are short-lived context, not archive.
        near_cut = iso(now_utc() - timedelta(days=self.cfg.nearby_retention_days))
        await self.db.run(
            "DELETE FROM flights WHERE crossing_status IN ('NEARBY','WORLD') AND last_seen_utc<?", (near_cut,))
        await self.db.run(
            "DELETE FROM track_observations WHERE in_iraq=0 AND ts_utc<?", (near_cut,))
        await self.db.run("DELETE FROM sync_history WHERE started_utc<?",
                          (iso(now_utc() - timedelta(days=60)),))

    async def run_forever(self) -> None:
        ev("sync loop started", interval=self.cfg.sync_interval, providers=self.cfg.providers)
        while not self.stop.is_set():
            try:
                await self.sync_live("auto")
                if self.enricher:
                    done = await self.enricher.background(25, self.stop)
                    if done:
                        ev("enrichment", flights=done, lookups_total=self.enricher.lookups)
                if self.after_sync:
                    await self.after_sync()
                self.cycles += 1
                if self.cycles % 50 == 1:
                    await self._maintenance()
            except asyncio.CancelledError:
                raise
            except Exception:
                log.exception("unexpected error in sync loop")
            self.next_run = now_utc() + timedelta(seconds=self.cfg.sync_interval)
            try:
                await asyncio.wait_for(self.stop.wait(), timeout=self.cfg.sync_interval)
            except asyncio.TimeoutError:
                pass
        ev("sync loop stopped")


# --------------------------------------------------------------------------
# TELEGRAM UI: SHARED STATE, TRANSLATIONS, FORMAT HELPERS
# --------------------------------------------------------------------------
class Ctx:
    """Shared runtime objects (set in amain())."""
    cfg: Config
    db: Database
    api: AdsbClient
    enrich: Enricher
    sync: SyncService
    started: datetime
    sub_error: Optional[str] = None      # last problem checking channel membership
    sub_error_logged: float = 0.0


RULE = "═" * 24
THIN = "─" * 24
RLM = "‏"   # right-to-left mark: keeps Arabic lines right-aligned when they hold Latin values
IRAQ_ZONE = "crossing_status IN ('CONFIRMED','SINGLE_OBS')"
REGION_ZONE = "crossing_status IN ('CONFIRMED','SINGLE_OBS','NEARBY')"
EM_SQL = "squawk IN ('7500','7600','7700')"
WATCH_LIMIT = 20

# key -> (English, Arabic)
TXT: dict[str, tuple[str, str]] = {
    "app": ("IRAQ AIR TRAFFIC MONITOR", "مرصد الحركة الجوية العراقية"),
    "tagline": ("Airspace surveillance terminal",
        "منظومة مراقبة المجال الجوي"),
    # main menu
    "m_over": ("Over Iraq now", "فوق العراق الآن"),
    "m_near": ("Around Iraq now", "حول العراق الآن"),
    "m_em": ("Emergency squawks (24h)", "نداءات الطوارئ (24 ساعة)"),
    "m_logged": ("Crossings logged", "عمليات العبور المسجَّلة"),
    "m_time": ("Local time", "الوقت المحلي"),
    "m_data": ("Last update", "آخر تحديث"),
    "m_sources": ("Live sources", "المصادر المباشرة"),
    "m_never": ("no successful sync yet", "لم تكتمل أي مزامنة بعد"),
    "m_stale": ("STALE", "قديمة"),
    "m_choose": ("Select a module.",
        "اختر وحدة."),
    "none_yet": ("none yet", "لا يوجد بعد"),
    # buttons
    "b_live": ("AIRSPACE · LIVE",
        "الأجواء العراقية · مباشر"),
    "b_near": ("PERIMETER",
        "محيط العراق"),
    "b_24h": ("LAST 24H",
        "آخر 24 ساعة"),
    "b_archive": ("ARCHIVE",
        "الأرشيف"),
    "b_search": ("QUERY",
        "استعلام"),
    "b_world": ("GLOBAL TRACE",
        "تتبّع عالمي"),
    "b_airlines": ("OPERATORS",
        "شركات الطيران"),
    "b_types": ("AIRFRAMES",
        "أنواع الطائرات"),
    "b_stats": ("ANALYTICS",
        "التحليلات"),
    "b_alerts": ("SQUAWK ALERTS",
        "إنذارات الطوارئ"),
    "b_watch": ("WATCHLIST",
        "قائمة المتابعة"),
    "b_settings": ("CONFIG",
        "الإعدادات"),
    "b_status": ("SYSTEM",
        "حالة النظام"),
    "b_help": ("MANUAL",
        "الدليل"),
    "b_about": ("ABOUT",
        "حول النظام"),
    "b_lang": ("LANG · اللغة",
        "اللغة · LANG"),
    "b_dev": ("DEVELOPER",
        "المطوّر"),
    "b_channel": ("CHANNEL",
        "القناة"),
    "b_menu": ("MAIN MENU",
        "القائمة الرئيسية"),
    "b_console": ("OPEN CONSOLE", "فتح المنظومة"),
    "console_txt": ("Live scope, target files and traffic analytics in one console.",
                    "الرادار الحي وملفات الأهداف وتحليلات الحركة في واجهة واحدة."),
    "console_off": ("The web console is not configured on this server.",
                    "الواجهة غير مفعّلة على هذا الخادم."),
    "dev": ("Developer", "المطوّر"),
    "channel": ("Channel", "القناة"),
    "b_back": ("‹ BACK",
        "رجوع ›"),
    "b_prev": ("‹ PREV",
        "‹ السابق"),
    "b_next": ("NEXT ›",
        "التالي ›"),
    "b_refresh": ("REFRESH",
        "تحديث"),
    "b_map": ("OPEN MAP",
        "فتح الخريطة"),
    "b_pin": ("SEND POSITION",
        "إرسال الموقع"),
    "b_track": ("TRACK LOG",
        "سجل المسار"),
    "b_aircraft": ("AIRFRAME",
        "ملف الطائرة"),
    "b_follow": ("+ WATCH",
        "+ متابعة"),
    "b_unfollow": ("WATCHING ×",
        "تتم المتابعة ×"),
    "b_liveupd": ("LIVE UPDATE",
        "تحديث مباشر"),
    "b_photo": ("AIRCRAFT PHOTO",
        "صورة الطائرة"),
    "b_flight": ("‹ FLIGHT RECORD",
        "سجل الرحلة ›"),
    "b_export": ("EXPORT CSV",
        "تصدير CSV"),
    "b_join": ("JOIN CHANNEL",
        "الاشتراك في القناة"),
    "b_joined": ("VERIFY ACCESS",
        "تحقّق من الاشتراك"),
    "b_worldthis": ("RUN GLOBAL TRACE",
        "تتبّع عالمي لهذا الاستعلام"),
    "b_newworld": ("NEW GLOBAL TRACE",
        "تتبّع عالمي جديد"),
    "b_p24": ("LAST 24 HOURS",
        "آخر 24 ساعة"),
    "b_p7": ("LAST 7 DAYS",
        "آخر 7 أيام"),
    "b_p30": ("LAST 30 DAYS",
        "آخر 30 يوماً"),
    "b_custom": ("CUSTOM RANGE",
        "فترة مخصّصة"),
    "b_all": ("ALL",
        "الكل"),
    "b_alerts_on": ("ALERTS: ON",
        "التنبيهات: مفعّلة"),
    "b_alerts_off": ("ALERTS: OFF",
        "التنبيهات: متوقفة"),
    "b_remove": ("× {x}",
        "× {x}"),
    "b_add_watch": ("+ ADD IDENTIFIER",
        "+ إضافة معرّف"),
    "b_open": ("OPEN RECORD",
        "فتح السجل"),
    # language / subscription
    "lang_pick": ("<b>SELECT LANGUAGE</b>  /  <b>اختر اللغة</b>",
        "<b>اختر اللغة</b>  /  <b>SELECT LANGUAGE</b>"),
    "lang_note": ("You can change it any time from the main menu.",
                  "يمكنك تغييرها في أي وقت من القائمة الرئيسية."),
    "lang_set": ("Language: English",
        "اللغة: العربية"),
    "join_title": ("Access restricted",
        "الوصول مقيَّد"),
    "join_body": ("Channel subscription is required to use this system:",
        "يتطلب استخدام النظام الاشتراك في القناة:"),
    "join_then": ("Join, then press VERIFY ACCESS.",
        "اشترك ثم اضغط «تحقّق من الاشتراك»."),
    "join_no": ("Not verified: you have not joined the channel.",
        "لم يتم التحقق: لم تشترك في القناة بعد."),
    "join_ok": ("Access verified.",
        "تم التحقق من الاشتراك."),
    # generic labels
    "na": ("N/A", "غير متوفر"),
    "records": ("Records", "السجلات"),
    "page": ("Page", "الصفحة"),
    "empty": ("No records for this view.", "لا توجد سجلات في هذا القسم."),
    "empty_live": ("No aircraft were observed in this zone in the last update.",
                   "لم تُرصد أي طائرة في هذه المنطقة في آخر تحديث."),
    "legend": ("CNF confirmed crossing · 1OB single observation · PRM perimeter · GLB global · EMG emergency squawk",
        "CNF عبور مؤكَّد · 1OB رصد واحد · PRM محيط العراق · GLB عالمي · EMG نداء طوارئ"),
    "tz_note": ("Times in {tz}.", "الأوقات بتوقيت {tz}."),
    "not_found": ("Record not found.", "السجل غير موجود."),
    "ago_s": ("{n}s ago", "قبل {n} ث"), "ago_m": ("{n}m ago", "قبل {n} د"),
    "ago_h": ("{n}h ago", "قبل {n} س"), "ago_d": ("{n}d ago", "قبل {n} يوم"),
    # list titles
    "t_24h": ("Last 24h · Iraq",
        "آخر 24 ساعة · العراق"),
    "t_live": ("Airspace live",
        "الأجواء العراقية · مباشر"),
    "t_near": ("Perimeter live",
        "محيط العراق · مباشر"),
    "t_archive": ("Archive · {p}", "الأرشيف · {p}"),
    "t_airline": ("Airline · {a}", "شركة الطيران · {a}"),
    "t_type": ("Aircraft type · {a}", "نوع الطائرة · {a}"),
    "t_search": ("Query · {q}",
        "استعلام · {q}"),
    "t_em": ("Squawk alerts · 24h",
        "إنذارات الطوارئ · 24 ساعة"),
    "t_world": ("Global trace · {q}",
        "تتبّع عالمي · {q}"),
    "t_nearpt": ("Near {lat},{lon} · {r} NM", "قرب {lat},{lon} · {r} ميل بحري"),
    "unknown": ("Unknown", "غير معروف"),
    "days": ("{n} days", "{n} أيام"),
    # flight page
    "s_flight": ("FLIGHT", "الرحلة"),
    "s_aircraft": ("AIRFRAME",
        "الطائرة"),
    "s_livedata": ("TELEMETRY",
        "القياسات الحيّة"),
    "s_iraq": ("IRAQ AIRSPACE", "الأجواء العراقية"),
    "s_observed": ("OBSERVATION", "الرصد"),
    "f_callsign": ("Callsign", "رمز النداء"),
    "f_flightno": ("Flight number", "رقم الرحلة"),
    "f_airline": ("Airline", "شركة الطيران"),
    "f_from_callsign": ("from callsign", "من رمز النداء"),
    "f_from": ("From", "من"),
    "f_to": ("To", "إلى"),
    "f_progress": ("Progress", "التقدّم"),
    "f_flown": ("Flown", "المقطوع"),
    "f_remaining": ("Remaining", "المتبقّي"),
    "f_eta": ("Est. arrival", "الوصول التقديري"),
    "f_eta_note": ("estimate from current speed", "تقدير من السرعة الحالية"),
    "f_traffic": ("Traffic", "نوع الحركة"),
    "f_route_src": ("Route: {s} database, by callsign - the usual route, not a live flight plan.",
                    "المسار: قاعدة بيانات {s} حسب رمز النداء - المسار المعتاد وليس خطة الرحلة الحيّة."),
    "f_route_none": ("Route: not found in the route databases.",
                     "المسار: غير موجود في قواعد بيانات المسارات."),
    "f_route_pending": ("Route: not looked up (no airline callsign, or lookup service busy).",
                        "المسار: لم يُبحث عنه (لا يوجد رمز شركة طيران أو خدمة البحث مشغولة)."),
    "f_times": ("Departure/arrival times: not available from free sources.",
                "أوقات الإقلاع والوصول: غير متوفرة من المصادر المجانية."),
    "f_type": ("Type", "النوع"),
    "f_model": ("Model", "الموديل"),
    "f_maker": ("Manufacturer", "المصنّع"),
    "f_reg": ("Registration", "التسجيل"),
    "f_hex": ("ICAO24", "ICAO24"),
    "f_owner": ("Owner / operator", "المالك / المشغّل"),
    "f_country": ("Country", "الدولة"),
    "f_category": ("Category", "الفئة"),
    "f_class": ("Class", "التصنيف"),
    "f_alt": ("Altitude", "الارتفاع"),
    "f_altgeo": ("GPS altitude", "ارتفاع GPS"),
    "f_speed": ("Ground speed", "السرعة الأرضية"),
    "f_heading": ("Heading", "الاتجاه"),
    "f_vrate": ("Vertical rate", "معدّل الصعود/الهبوط"),
    "f_level": ("LEVEL", "مستوٍ"),
    "f_squawk": ("Squawk", "رمز Squawk"),
    "f_mach": ("Mach", "ماخ"),
    "f_ias": ("Airspeed IAS / TAS", "السرعة الجوية IAS / TAS"),
    "f_selalt": ("Selected altitude", "الارتفاع المُختار"),
    "f_selhdg": ("Selected heading", "الاتجاه المُختار"),
    "f_wind": ("Wind", "الرياح"),
    "f_oat": ("Outside temp.", "الحرارة الخارجية"),
    "f_pos": ("Position", "الموقع"),
    "f_nearcity": ("Nearest city", "أقرب مدينة"),
    "f_of": ("{d} NM {dir} of {city}", "{d} ميل بحري {dir} {city}"),
    "f_source": ("Signal source", "مصدر الإشارة"),
    "f_seen": ("Last seen", "آخر رصد"),
    "f_first": ("First observed", "أول رصد"),
    "f_last": ("Last observed", "آخر رصد"),
    "f_duration": ("Duration over Iraq", "المدة فوق العراق"),
    "f_dur_val": ("≥ {n} min (observed)", "≥ {n} دقيقة (مرصودة)"),
    "f_dur_na": ("needs 2+ observations", "تحتاج رصدين أو أكثر"),
    "f_obs": ("Observations", "عدد مرات الرصد"),
    "f_status": ("Status", "الحالة"),
    "pin_sent": ("Position sent.",
        "تم إرسال الموقع."),
    "pin_none": ("No position stored.", "لا يوجد موقع محفوظ."),
    # aircraft page
    "a_title": ("Aircraft {k}", "الطائرة {k}"),
    "a_noid": ("No registration or ICAO24 on this record.", "لا يوجد تسجيل أو ICAO24 لهذا السجل."),
    "a_firstseen": ("First seen by bot", "أول رصد في البوت"),
    "a_lastseen": ("Last seen by bot", "آخر رصد في البوت"),
    "a_records": ("Flights in archive", "الرحلات في الأرشيف"),
    "a_recent": ("RECENT FLIGHTS", "أحدث الرحلات"),
    "a_photo_by": ("Photo page: planespotters.net / adsbdb", "صفحة الصورة: planespotters.net / adsbdb"),
    "a_src": ("Sources: ADS-B feed, adsbdb, hexdb registries.", "المصادر: بث ADS-B وسجلات adsbdb و hexdb."),
    # track
    "tr_title": ("Track {k}", "مسار {k}"),
    "tr_points": ("Points", "النقاط"),
    "tr_none": ("No stored track points (not provided, or past retention).",
                "لا توجد نقاط مسار محفوظة (غير متوفرة أو تجاوزت مدة الحفظ)."),
    "tr_profile": ("Altitude profile", "منحنى الارتفاع"),
    "tr_outside": ("· = outside Iraq boundary", "· = خارج حدود العراق"),
    # groups
    "g_airlines": ("Airlines over Iraq", "شركات الطيران فوق العراق"),
    "g_types": ("Aircraft types over Iraq", "أنواع الطائرات فوق العراق"),
    "g_distinct": ("Distinct", "العدد"),
    "g_none": ("No records yet.", "لا توجد سجلات بعد."),
    # stats
    "st_title": ("Analytics · {p}",
        "التحليلات · {p}"),
    "st_alltime": ("all time", "كل الفترة"),
    "st_24h": ("24 hours", "24 ساعة"),
    "st_confirmed": ("Confirmed crossings", "عبور مؤكَّد"),
    "st_single": ("Seen once (not counted)", "رُصدت مرة (لا تُحتسب)"),
    "st_airlines": ("Airlines", "شركات الطيران"),
    "st_types": ("Aircraft types", "أنواع الطائرات"),
    "st_mix": ("TRAFFIC MIX", "أنواع الحركة"),
    "st_top_al": ("TOP AIRLINES", "أكثر الشركات"),
    "st_top_ac": ("TOP AIRCRAFT", "أكثر الطائرات"),
    "st_top_dep": ("TOP ORIGINS", "أكثر مطارات الإقلاع"),
    "st_top_arr": ("TOP DESTINATIONS", "أكثر مطارات الوصول"),
    "st_hourly": ("HOURLY ENTRIES ({tz})", "الدخول حسب الساعة ({tz})"),
    "st_avg_alt": ("Average altitude", "متوسط الارتفاع"),
    "st_avg_gs": ("Average speed", "متوسط السرعة"),
    "st_from_obs": ("from {n} observations", "من {n} رصد"),
    "st_complete": ("DATA COMPLETENESS", "اكتمال البيانات"),
    "st_c_airline": ("airline", "الشركة"), "st_c_type": ("type", "النوع"),
    "st_c_route": ("route", "المسار"),
    "st_starts": ("Archive starts", "بداية الأرشيف"),
    "st_partial": ("Archive covers only part of this period.",
        "الأرشيف يغطي جزءاً من هذه الفترة فقط."),
    "st_note": ("Based on sampled observations: very short crossings can be missed. "
                "Routes come from callsign databases.",
                "مبنية على عيّنات رصد دورية: قد تفوت العبورات القصيرة جداً. "
                "المسارات من قواعد بيانات رموز النداء."),
    "st_nodata": ("no data", "لا توجد بيانات"),
    # archive
    "ar_title": ("Flight archive", "أرشيف الرحلات"),
    "ar_note": ("Only flights collected by this bot are available.",
                "تتوفر فقط الرحلات التي جمعها هذا البوت."),
    "ar_pick": ("Choose a period ", "اختر الفترة "),
    "ar_range": ("Send two dates (start end), for example:", "أرسل تاريخين (البداية ثم النهاية)، مثال:"),
    "ar_bad": ("Invalid range. Format: 2026-11-01 2026-11-10",
               "الفترة غير صحيحة. الصيغة: 2026-11-01 2026-11-10"),
    # search
    "se_title": ("Archive query",
        "استعلام الأرشيف"),
    "se_send": ("Send a query term:",
        "أرسل عبارة الاستعلام:"),
    "se_ex": ("callsign QTR8K · registration A7-ALA · airline Emirates / UAE · type B77W · "
              "airport ORBI / BGW / Dubai · ICAO24 06A1E5",
              "رمز النداء QTR8K · التسجيل A7-ALA · الشركة Emirates / UAE · النوع B77W · "
              "المطار ORBI / BGW / Dubai · ICAO24 06A1E5"),
    "se_short": ("Search term too short (minimum 2 characters).", "كلمة البحث قصيرة (حرفان على الأقل)."),
    # world
    "w_title": ("Global trace · live",
        "التتبّع العالمي · مباشر"),
    "w_one": ("Locate one aircraft anywhere: send its callsign, registration or ICAO24 hex.",
        "لتحديد موقع أي طائرة في العالم أرسل رمز النداء أو التسجيل أو ICAO24."),
    "w_area": ("Scan around any point: send a Telegram location, or type:",
        "لمسح محيط أي نقطة أرسل موقعاً من تيليغرام أو اكتب:"),
    "w_live": ("Live only: the aircraft must be airborne and in range of a receiver.",
               "مباشر فقط: يجب أن تكون الطائرة في الجو وضمن تغطية جهاز استقبال."),
    "w_invalid": ("Invalid identifier. Use letters, digits and \"-\", 2 to 10 characters.",
                  "المعرّف غير صحيح. استخدم حروفاً وأرقاماً و«-» من 2 إلى 10 خانات."),
    "w_wait": ("Rate limit: wait a few seconds between global traces.",
        "حدّ الطلبات: انتظر بضع ثوانٍ بين عمليات التتبّع."),
    "w_nofeed": ("No data source answered. Try again later.", "لم يُجب أي مصدر بيانات. حاول لاحقاً."),
    "w_notfound": ("Not found live. Possible reasons:\n- not flying right now\n"
                   "- outside receiver coverage\n- a different callsign is in use",
                   "غير موجودة حالياً. الأسباب المحتملة:\n- ليست في الجو الآن\n"
                   "- خارج تغطية أجهزة الاستقبال\n- تستخدم رمز نداء مختلفاً"),
    "w_ground": ("Found, but not airborne: the aircraft is on the ground or has no recent position.",
                 "وُجدت لكنها ليست في الجو: الطائرة على الأرض أو لا يوجد لها موقع حديث."),
    "w_badcoord": ("Invalid coordinates. Example: /near 51.47 -0.45",
                   "الإحداثيات غير صحيحة. مثال: /near 51.47 -0.45"),
    "w_noarea": ("No aircraft seen in this area.", "لم تُرصد طائرات في هذه المنطقة."),
    # alerts / watchlist / settings
    "al_title": ("Squawk alerts",
        "إنذارات الطوارئ"),
    "al_body": ("Aircraft in or around Iraq that broadcast an emergency transponder code in the "
                "last 24 hours:\n7700 general emergency · 7600 radio failure · 7500 unlawful interference.\n"
                "A code can be set by mistake; it is not proof of an incident.",
                "الطائرات داخل العراق أو حوله التي أرسلت رمز طوارئ خلال آخر 24 ساعة:\n"
                "7700 طوارئ عامة · 7600 عطل اللاسلكي · 7500 تدخّل غير مشروع.\n"
                "قد يُضبط الرمز بالخطأ؛ وهو ليس دليلاً على وقوع حادث."),
    "al_push": ("<code>[EMG]</code> <b>SQUAWK {sq}</b> · {mean}\n<code>{id}</code> {type}\n{where}",
        "<code>[EMG]</code> <b>رمز {sq}</b> · {mean}\n<code>{id}</code> {type}\n{where}"),
    "al_in": ("inside Iraqi airspace", "داخل الأجواء العراقية"),
    "al_near": ("around Iraq", "حول العراق"),
    "sq_7500": ("unlawful interference", "تدخّل غير مشروع"),
    "sq_7600": ("radio failure", "عطل اللاسلكي"),
    "sq_7700": ("general emergency", "طوارئ عامة"),
    "sq_vfr": ("VFR", "طيران بصري"),
    "wl_title": ("Watchlist",
        "قائمة المتابعة"),
    "wl_body": ("You are notified when a followed callsign, registration or ICAO24 is seen inside "
                "Iraqi airspace.", "يصلك تنبيه عند رصد رمز نداء أو تسجيل أو ICAO24 تتابعه داخل الأجواء العراقية."),
    "wl_empty": ("Your watchlist is empty.", "قائمة المتابعة فارغة."),
    "wl_how": ("Add: /watch QTR8K, or press + WATCH on a flight record.",
        "للإضافة: /watch QTR8K أو اضغط «+ متابعة» في سجل الرحلة."),
    "wl_send": ("Send the callsign, registration or ICAO24 to follow:",
                "أرسل رمز النداء أو التسجيل أو ICAO24 للمتابعة:"),
    "wl_added": ("Watching {x}",
        "تمت متابعة {x}"),
    "wl_removed": ("Removed {x}", "أُزيلت {x}"),
    "wl_full": ("Watchlist is full ({n} entries). Remove one first.",
                "قائمة المتابعة ممتلئة ({n}). احذف عنصراً أولاً."),
    "wl_push": ("<code>[WATCH]</code> <b>{x}</b> entered Iraqi airspace",
        "<code>[WATCH]</code> <b>{x}</b> دخلت الأجواء العراقية"),
    "set_title": ("Config",
        "الإعدادات"),
    "set_lang": ("Language", "اللغة"),
    "set_lang_v": ("English", "العربية"),
    "set_alerts": ("Emergency alerts", "تنبيهات الطوارئ"),
    "set_on": ("ON", "مفعّلة"), "set_off": ("OFF", "متوقفة"),
    "set_watch": ("Followed", "المتابَعة"),
    "set_alerts_note": ("When ON, the bot messages you if an aircraft in or around Iraq broadcasts "
                        "an emergency code.", "عند التفعيل يراسلك البوت إذا أرسلت طائرة داخل العراق "
                        "أو حوله رمز طوارئ."),
    # status / about / help
    "ss_title": ("System status", "حالة النظام"),
    "ss_bot": ("Bot", "البوت"), "ss_online": ("online", "يعمل"),
    "ss_uptime": ("Uptime", "مدة التشغيل"),
    "ss_feed": ("Live feed", "البث المباشر"),
    "ss_lastsync": ("Last sync", "آخر مزامنة"),
    "ss_result": ("Result", "النتيجة"),
    "ss_received": ("Aircraft received", "الطائرات المستلمة"),
    "ss_iniraq": ("Inside Iraq", "داخل العراق"),
    "ss_around": ("Around Iraq", "حول العراق"),
    "ss_next": ("Next sync", "المزامنة القادمة"),
    "ss_interval": ("Interval", "الفاصل"),
    "ss_flights": ("Iraq flights stored", "رحلات العراق المحفوظة"),
    "ss_points": ("Track points", "نقاط المسار"),
    "ss_feeds": ("FEEDS (with position / total)", "المصادر (بموقع / الإجمالي)"),
    "ss_serving": ("Live feed unavailable: serving stored records.",
        "البث المباشر غير متاح: تُعرض السجلات المحفوظة."),
    "ab_title": ("About", "حول البوت"),
    "ab_body": ("Tracks aircraft over Iraq and around it, keeps its own archive, and can find any "
                "airborne aircraft in the world on demand.",
                "يرصد الطائرات فوق العراق وحوله، ويحتفظ بأرشيفه الخاص، ويستطيع إيجاد أي طائرة "
                "في الجو حول العالم عند الطلب."),
    "ab_version": ("Version", "الإصدار"),
    "ab_data": ("DATA SOURCES", "مصادر البيانات"),
    "ab_data_note": ("Community data, provided as-is, without any guarantee of completeness.",
                     "بيانات مجتمعية تُقدَّم كما هي دون ضمان لاكتمالها."),
    "h_title": ("Manual",
        "الدليل"),
    "h_body": (
        "/start - main menu\n/live - aircraft over Iraq now\n/around - aircraft around Iraq\n"
        "/last24 - Iraq flights, last 24 hours\n/archive - browse history\n/search - search the archive\n"
        "/flight QTR8K - open one flight\n/world QTR8K - find any aircraft worldwide\n"
        "/near 25.25 55.36 - aircraft near a point\n/airlines · /aircraft - rankings\n"
        "/stats - statistics\n/alerts - emergency squawks\n/watch QTR8K - follow · /unwatch QTR8K\n"
        "/watchlist - followed list\n/settings - language and alerts\n/lang - change language\n"
        "/status - system status\n/about - about and credits",
        "/start - القائمة الرئيسية\n/live - الطائرات فوق العراق الآن\n/around - الطائرات حول العراق\n"
        "/last24 - رحلات العراق خلال 24 ساعة\n/archive - تصفّح الأرشيف\n/search - البحث في الأرشيف\n"
        "/flight QTR8K - فتح رحلة\n/world QTR8K - إيجاد أي طائرة في العالم\n"
        "/near 25.25 55.36 - الطائرات قرب نقطة\n/airlines · /aircraft - الترتيب\n"
        "/stats - الإحصائيات\n/alerts - نداءات الطوارئ\n/watch QTR8K - متابعة · /unwatch QTR8K\n"
        "/watchlist - قائمة المتابعة\n/settings - اللغة والتنبيهات\n/lang - تغيير اللغة\n"
        "/status - حالة النظام\n/about - حول البوت"),
    "h_marks": ("CNF = two or more positions inside Iraq at least 60 seconds apart.\n1OB = one position only; never counted as a crossing.",
        "CNF = موقعان أو أكثر داخل العراق بفارق 60 ثانية على الأقل.\n1OB = موقع واحد فقط؛ لا يُحتسب عبوراً."),
    "unknown_cmd": ("ERR_CMD: unknown command. Send /help.",
        "ERR_CMD: أمر غير معروف. أرسل /help."),
    "err_db": ("ERR_DB: database error. Try again.",
        "ERR_DB: خطأ في قاعدة البيانات. حاول مجدداً."),
    "err_int": ("ERR_INT: request failed. Try again or send /start.",
        "ERR_INT: تعذّر تنفيذ الطلب. حاول مجدداً أو أرسل /start."),
    "denied": ("ACCESS DENIED: administrators only.",
        "رُفض الوصول: للمشرفين فقط."),
}

TRAFFIC = {"OVERFLIGHT": ("Overflight", "عبور"), "ARRIVAL": ("Arrival to Iraq", "قادمة إلى العراق"),
           "DEPARTURE": ("Departure from Iraq", "مغادرة من العراق"), "DOMESTIC": ("Domestic", "داخلية"),
           "UNKNOWN": ("Unknown", "غير معروف")}
STATUS_TXT = {
    "CONFIRMED": ("Confirmed crossing of Iraqi airspace", "عبور مؤكَّد للأجواء العراقية"),
    "SINGLE_OBS": ("Single observation inside Iraq (unconfirmed)", "رصد واحد داخل العراق (غير مؤكَّد)"),
    "NEARBY": ("Perimeter: around Iraq, not inside", "المحيط: حول العراق وليست داخله"),
    "WORLD": ("Global trace result", "نتيجة تتبّع عالمي"),
}
# Three-letter record classification shown in lists and on flight records
TAGS = {"CONFIRMED": "CNF", "SINGLE_OBS": "1OB", "NEARBY": "PRM", "WORLD": "GLB"}
COMPASS = (("N", "NE", "E", "SE", "S", "SW", "W", "NW"),
           ("شمال", "شمال شرق", "شرق", "جنوب شرق", "جنوب", "جنوب غرب", "غرب", "شمال غرب"))
# ADS-B emitter categories (DO-260B)
CATEGORIES = {
    "A1": ("Light (< 7 t)", "خفيفة (أقل من 7 طن)"), "A2": ("Small (7–34 t)", "صغيرة (7–34 طن)"),
    "A3": ("Large (34–136 t)", "كبيرة (34–136 طن)"), "A4": ("High-vortex large", "كبيرة عالية الدوّامات"),
    "A5": ("Heavy (> 136 t)", "ثقيلة (أكثر من 136 طن)"), "A6": ("High performance", "عالية الأداء"),
    "A7": ("Rotorcraft", "مروحية"), "B1": ("Glider", "طائرة شراعية"),
    "B2": ("Lighter than air", "أخف من الهواء"), "B4": ("Ultralight", "خفيفة جداً"),
    "B6": ("Unmanned aircraft", "طائرة بدون طيار"),
}
POS_SOURCES = {"adsb_icao": "ADS-B", "adsb_icao_nt": "ADS-B", "adsr_icao": "ADS-R", "tisb_icao": "TIS-B",
               "adsc": "ADS-C (satellite)", "mlat": "MLAT", "mode_s": "Mode S", "adsb_other": "ADS-B",
               "opensky": "OpenSky"}
# Reference cities (name en, name ar, lat, lon); coordinates are approximate city centres.
IRAQ_CITIES = [
    ("Baghdad", "بغداد", 33.31, 44.37), ("Basra", "البصرة", 30.51, 47.78), ("Mosul", "الموصل", 36.34, 43.13),
    ("Erbil", "أربيل", 36.19, 44.01), ("Sulaymaniyah", "السليمانية", 35.56, 45.44),
    ("Kirkuk", "كركوك", 35.47, 44.39), ("Najaf", "النجف", 32.00, 44.34), ("Karbala", "كربلاء", 32.61, 44.02),
    ("Nasiriyah", "الناصرية", 31.04, 46.26), ("Ramadi", "الرمادي", 33.42, 43.30),
    ("Duhok", "دهوك", 36.87, 42.99), ("Amarah", "العمارة", 31.84, 47.14), ("Tikrit", "تكريت", 34.61, 43.68),
    ("Rutba", "الرطبة", 33.04, 40.28), ("Kut", "الكوت", 32.51, 45.82), ("Samawah", "السماوة", 31.31, 45.28),
    ("Diwaniyah", "الديوانية", 31.99, 44.93), ("Hillah", "الحلة", 32.48, 44.43),
    ("Baqubah", "بعقوبة", 33.75, 44.64),
]


def tr(lang: str, key: str, **kw: Any) -> str:
    pair = TXT.get(key)
    if pair is None:
        return key
    text = pair[1] if lang == "ar" else pair[0]
    return text.format(**kw) if kw else text


def pick(lang: str, pair: tuple[str, str]) -> str:
    return pair[1] if lang == "ar" else pair[0]


def lg(context: ContextTypes.DEFAULT_TYPE) -> str:
    return (context.user_data or {}).get("lang") or "en"


def esc(value: Any) -> str:
    return html.escape(str(value), quote=False)


def pre(lines: list[str]) -> str:
    text = "\n".join(lines)
    if len(text) > 3900:
        text = text[:3900] + "\n… (truncated)"
    return f"<pre>{esc(text)}</pre>"


def head(tag: str, title: str) -> str:
    """Screen header: module tag, title, rule.  [IATM:FLT] FLIGHT QTR8K"""
    return f"<code>[IATM:{esc(tag)}]</code> <b>{esc(str(title).upper())}</b>\n<code>{RULE}</code>"


def sect(title: str) -> str:
    return f"\n<code>┌─</code> <b>{esc(title)}</b>"


def row(lang: str, label: str, value: Any) -> str:
    """One key/value line of a record.  │ ALTITUDE: 38,000 ft"""
    mark = RLM if lang == "ar" else ""
    return f"{mark}<code>│</code> {esc(label.upper() if lang == 'en' else label)}: <code>{esc(value)}</code>"


def note(lang: str, text: str) -> str:
    """Remark line, written like a source-code comment."""
    return f"{RLM if lang == 'ar' else ''}<code>//</code> <i>{esc(text)}</i>"


def line(lang: str, text: str) -> str:
    return f"{RLM if lang == 'ar' else ''}{esc(text)}"


def num(value: Any) -> str:
    return f"{int(round(float(value))):,}"


def bearing(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    la1, la2, dlo = math.radians(lat1), math.radians(lat2), math.radians(lon2 - lon1)
    y = math.sin(dlo) * math.cos(la2)
    x = math.cos(la1) * math.sin(la2) - math.sin(la1) * math.cos(la2) * math.cos(dlo)
    return (math.degrees(math.atan2(y, x)) + 360) % 360


def compass(lang: str, degrees: float) -> str:
    return COMPASS[1 if lang == "ar" else 0][int((degrees % 360 + 22.5) // 45) % 8]


def local(iso_value: Optional[str], fmt: str = "%d %b %H:%M") -> str:
    dt = parse_dt(iso_value)
    return dt.astimezone(Ctx.cfg.tz).strftime(fmt) if dt else NA


def lt(lang: str, iso_value: Optional[str], fmt: str = "%d/%m %H:%M") -> str:
    dt = parse_dt(iso_value)
    return dt.astimezone(Ctx.cfg.tz).strftime(fmt) if dt else tr(lang, "na")


def val(value: Any, suffix: str = "") -> str:
    if value is None or value == "":
        return NA
    if isinstance(value, float):
        value = int(round(value))
    return f"{value}{suffix}"


def ago(iso_value: Optional[str], lang: str = "en") -> str:
    dt = parse_dt(iso_value)
    if not dt:
        return tr(lang, "na")
    secs = max(0, int((now_utc() - dt).total_seconds()))
    if secs < 90:
        return tr(lang, "ago_s", n=secs)
    if secs < 5400:
        return tr(lang, "ago_m", n=secs // 60)
    if secs < 172800:
        return tr(lang, "ago_h", n=secs // 3600)
    return tr(lang, "ago_d", n=secs // 86400)


def header(title: str) -> list[str]:
    return [SEP, f" {title}", SEP]


def is_admin(update: Update) -> bool:
    user = update.effective_user
    return bool(user and user.id in Ctx.cfg.admin_ids)


def btn(text: str, data: str, style: Optional[str] = None) -> InlineKeyboardButton:
    """Callback button. style: "primary" (blue), "success" (green), "danger" (red);
    Telegram clients released before February 2026 show the default colour."""
    return InlineKeyboardButton(text, callback_data=data, style=style)


def url_btn(text: str, url: str, style: Optional[str] = None) -> InlineKeyboardButton:
    return InlineKeyboardButton(text, url=url, style=style)


def menu_row(lang: str = "en") -> list[InlineKeyboardButton]:
    return [btn(tr(lang, "b_menu"), "M|main")]


def credit_row(lang: str) -> list[InlineKeyboardButton]:
    return [url_btn(tr(lang, "b_dev"), f"https://t.me/{Ctx.cfg.dev_username}"),
            url_btn(tr(lang, "b_channel"), f"https://t.me/{Ctx.cfg.channel}")]


def console_btn(lang: str) -> Optional[InlineKeyboardButton]:
    url = Ctx.cfg.webapp_url if Ctx.cfg.webapp_enabled else ""
    return InlineKeyboardButton(tr(lang, "b_console"), web_app=WebAppInfo(url), style="primary") if url else None


def main_menu_kb(lang: str) -> InlineKeyboardMarkup:
    def b(key: str, data: str, style: Optional[str] = None) -> InlineKeyboardButton:
        return btn(tr(lang, key), data, style)
    console = console_btn(lang)
    return InlineKeyboardMarkup(([[console]] if console else []) + [
        [b("b_live", "L|live|-|0", "primary"), b("b_near", "L|near|-|0", "primary")],
        [b("b_24h", "L|24h|-|0"), b("b_archive", "M|archive")],
        [b("b_search", "M|search"), b("b_world", "M|world")],
        [b("b_airlines", "AL|0"), b("b_types", "AC|0")],
        [b("b_stats", "S|1"), b("b_alerts", "M|alerts", "danger")],
        [b("b_watch", "M|watch"), b("b_settings", "M|settings")],
        [b("b_status", "M|status"), b("b_help", "M|help")],
        [b("b_lang", "M|lang"), b("b_about", "M|about")],
        credit_row(lang),
    ])


NO_PREVIEW = LinkPreviewOptions(is_disabled=True)


async def respond(update: Update, text: str, kb: Optional[InlineKeyboardMarkup] = None) -> None:
    if len(text) > 4000:
        text = text[:3990] + "…"
    query = update.callback_query
    try:
        if query and query.message:
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb,
                                          link_preview_options=NO_PREVIEW)
        elif update.effective_message:
            await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb,
                                                      link_preview_options=NO_PREVIEW)
    except BadRequest as exc:
        if "not modified" in str(exc).lower():
            return
        if update.effective_chat:
            await update.get_bot().send_message(
                update.effective_chat.id, text, parse_mode=ParseMode.HTML, reply_markup=kb,
                link_preview_options=NO_PREVIEW)


def ident(r: sqlite3.Row) -> str:
    return r["callsign"] or r["flight_number_icao"] or r["registration"] or r["mode_s"] or "UNKNOWN"


def route(r: sqlite3.Row) -> str:
    dep = r["dep_iata"] or r["dep_icao"]
    arr = r["arr_iata"] or r["arr_icao"]
    return f"{dep}→{arr}" if dep and arr else ""


def is_emergency(r: sqlite3.Row) -> bool:
    return (r["squawk"] or "") in EMERGENCY_SQUAWKS


def nearest_city(lang: str, lat: float, lon: float) -> str:
    name_en, name_ar, clat, clon = min(IRAQ_CITIES, key=lambda c: dist_nm(lat, lon, c[2], c[3]))
    d = dist_nm(lat, lon, clat, clon)
    city = name_ar if lang == "ar" else name_en
    if d < 5:
        return city
    return tr(lang, "f_of", d=num(d), dir=compass(lang, bearing(clat, clon, lat, lon)), city=city)


# --------------------------------------------------------------------------
# ACCESS GATE: USER RECORD, LANGUAGE QUESTION, MANDATORY CHANNEL SUBSCRIPTION
# --------------------------------------------------------------------------
async def member_ok(bot: Any, user_id: int, cache: dict) -> bool:
    """True if the user is in the required channel. The bot must be an administrator
    of that channel for Telegram to answer; if it is not, access is allowed and the
    problem is reported in the logs and in /system instead of locking everyone out.
    `cache` is a per-user dict (the bot's user_data, or the web console's own)."""
    cfg = Ctx.cfg
    if not (cfg.force_sub and cfg.channel) or user_id in cfg.admin_ids:
        return True
    now = time.monotonic()
    if cache.get("sub_ok_until", 0) > now:
        return True
    if cache.get("sub_no_until", 0) > now:
        return False
    try:
        member = await bot.get_chat_member(f"@{cfg.channel}", user_id)
    except (BadRequest, Forbidden) as exc:
        Ctx.sub_error = f"{type(exc).__name__}: {exc}"
        if now - Ctx.sub_error_logged > 600:
            Ctx.sub_error_logged = now
            log.error("subscription check impossible: make the bot an administrator of the channel",
                      extra={"data": {"channel": cfg.channel, "error": Ctx.sub_error}})
        return True
    except TelegramError:
        return True   # temporary network problem: do not lock users out
    Ctx.sub_error = None
    status = getattr(member, "status", "")
    ok = status in ("member", "administrator", "creator", "owner") or (
        status == "restricted" and bool(getattr(member, "is_member", False)))
    if ok:
        cache["sub_ok_until"] = now + 600
    else:
        cache["sub_no_until"] = now + 3
    return ok


async def is_subscribed(context: ContextTypes.DEFAULT_TYPE, user_id: int) -> bool:
    return await member_ok(context.bot, user_id, context.user_data)


async def view_lang(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    text = "\n".join([head("LANG", "LANGUAGE / اللغة"), tr(lang, "lang_pick"), "",
                      note(lang, tr(lang, "lang_note"))])
    kb = InlineKeyboardMarkup([[btn("العربية", "LG|ar", "primary"), btn("ENGLISH", "LG|en", "primary")]])
    await respond(update, text, kb)


async def view_join(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    channel = Ctx.cfg.channel
    text = "\n".join([
        head("AUTH", tr(lang, "join_title")),
        pre(["STATUS   LOCKED", "REASON   SUBSCRIPTION_REQUIRED", f"CHANNEL  @{channel}"]),
        line(lang, tr(lang, "join_body")),
        f"<b>@{esc(channel)}</b>",
        "",
        note(lang, tr(lang, "join_then")),
    ])
    kb = InlineKeyboardMarkup([
        [url_btn(tr(lang, "b_join"), f"https://t.me/{channel}", "primary")],
        [btn(tr(lang, "b_joined"), "J|check", "success")],
        [btn(tr(lang, "b_lang"), "M|lang")],
    ])
    await respond(update, text, kb)


async def gate(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Runs before every handler: private chats only, loads the user, asks the
    language on first contact and enforces the channel subscription."""
    user = update.effective_user
    chat = update.effective_chat
    if user is None or user.is_bot or chat is None or chat.type != "private":
        raise ApplicationHandlerStop
    ud = context.user_data
    stamp = iso(now_utc())
    if "lang" not in ud:
        saved = await Ctx.db.one("SELECT lang, alerts FROM users WHERE user_id=?", (user.id,))
        if saved:
            ud["lang"] = saved["lang"] if saved["lang"] in ("ar", "en") else "en"
        else:
            ud["lang"] = "ar" if (user.language_code or "").lower().startswith("ar") else "en"
            ud["need_lang"] = True
            await Ctx.db.run(
                "INSERT OR IGNORE INTO users(user_id, username, lang, first_seen_utc, last_seen_utc) "
                "VALUES(?,?,?,?,?)", (user.id, user.username, ud["lang"], stamp, stamp))
            ev("new user", user=user.id)
        ud["touch"] = time.monotonic()
    elif time.monotonic() - ud.get("touch", 0) > 600:
        ud["touch"] = time.monotonic()
        await Ctx.db.run("UPDATE users SET last_seen_utc=?, username=? WHERE user_id=?",
                         (stamp, user.username, user.id))

    query = update.callback_query
    data = (query.data or "") if query else ""
    if data.startswith("LG|") or data == "M|lang":
        return   # choosing a language is always allowed
    if ud.get("need_lang"):
        if query:
            try:
                await query.answer()
            except TelegramError:
                pass
        await view_lang(update, context)
        raise ApplicationHandlerStop
    if not await is_subscribed(context, user.id):
        if query:
            try:
                if data == "J|check":
                    await query.answer(tr(lg(context), "join_no"), show_alert=True)
                else:
                    await query.answer()
            except TelegramError:
                pass
        await view_join(update, context)
        raise ApplicationHandlerStop


async def set_language(update: Update, context: ContextTypes.DEFAULT_TYPE, lang: str) -> None:
    lang = lang if lang in ("ar", "en") else "en"
    context.user_data["lang"] = lang
    context.user_data.pop("need_lang", None)
    user = update.effective_user
    if user:
        await Ctx.db.run("UPDATE users SET lang=? WHERE user_id=?", (lang, user.id))
        if not await is_subscribed(context, user.id):
            await view_join(update, context)
            return
    await view_main(update, context)


# --------------------------------------------------------------------------
# VIEWS
# --------------------------------------------------------------------------
async def data_age(lang: str) -> str:
    last = await Ctx.db.scalar("SELECT MAX(finished_utc) FROM sync_history WHERE status='OK'")
    if not last:
        return tr(lang, "m_never")
    stale = (now_utc() - parse_dt(last)).total_seconds() > 3 * Ctx.cfg.sync_interval  # type: ignore[operator]
    return ago(last, lang) + (f"  [{tr(lang, 'm_stale')}]" if stale else "")


def live_cut() -> str:
    return iso(now_utc() - timedelta(seconds=max(600, 2 * Ctx.cfg.sync_interval)))


async def view_main(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    db = Ctx.db
    cut = live_cut()
    over = await db.scalar(f"SELECT COUNT(*) FROM flights WHERE last_seen_utc>=? AND {IRAQ_ZONE}", (cut,)) or 0
    near = await db.scalar(
        "SELECT COUNT(*) FROM flights WHERE last_seen_utc>=? AND crossing_status='NEARBY'", (cut,)) or 0
    emerg = await db.scalar(
        f"SELECT COUNT(*) FROM flights WHERE last_seen_utc>=? AND {EM_SQL} AND {REGION_ZONE}",
        (iso(now_utc() - timedelta(hours=24)),)) or 0
    logged = await db.scalar("SELECT COUNT(*) FROM flights WHERE crossing_status='CONFIRMED'") or 0
    sources = [x for x in (await db.get_status("provider") or "").split(",") if x.strip()]
    last_ok = await db.scalar("SELECT MAX(finished_utc) FROM sync_history WHERE status='OK'")
    stale = bool(last_ok) and (now_utc() - parse_dt(last_ok)).total_seconds() > 3 * Ctx.cfg.sync_interval  # type: ignore[operator]
    console = pre([
        f"SYS   ONLINE   v{APP_VERSION}",
        "FIR   ORBB / BAGHDAD",
        f"TIME  {now_utc().astimezone(Ctx.cfg.tz).strftime('%d/%m/%Y %H:%M')}",
        f"SYNC  {(ago(last_ok, 'en') + ('  STALE' if stale else '')) if last_ok else 'PENDING'}",
        f"FEED  {len(sources)} SOURCE{'S' if len(sources) != 1 else ''} LINKED",
    ])
    text = "\n".join([
        head("ROOT", tr(lang, "app")),
        note(lang, tr(lang, "tagline")),
        console,
        row(lang, tr(lang, "m_over"), num(over)),
        row(lang, tr(lang, "m_near"), num(near)),
        row(lang, tr(lang, "m_em"), num(emerg)),
        row(lang, tr(lang, "m_logged"), num(logged)),
        f"<code>{THIN}</code>",
        note(lang, tr(lang, "m_choose")),
    ])
    await respond(update, text, main_menu_kb(lang))


def like_escape(text: str) -> str:
    return text.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


SEARCH_COLS = ["callsign", "flight_number_iata", "flight_number_icao", "registration", "mode_s",
               "airline_name", "airline_icao", "airline_iata", "aircraft_type", "aircraft_type_desc",
               "dep_icao", "dep_iata", "dep_city", "dep_name", "arr_icao", "arr_iata", "arr_city",
               "arr_name"]


def list_filter(kind: str, arg: str, user_data: dict, lang: str) -> tuple[str, str, tuple]:
    """Return (title, where-clause, args) for a flight list context."""
    now = now_utc()
    if kind == "24h":
        return tr(lang, "t_24h"), f"last_seen_utc>=? AND {IRAQ_ZONE}", (iso(now - timedelta(hours=24)),)
    if kind == "live":
        return tr(lang, "t_live"), f"last_seen_utc>=? AND {IRAQ_ZONE}", (live_cut(),)
    if kind == "near":
        return tr(lang, "t_near"), "last_seen_utc>=? AND crossing_status='NEARBY'", (live_cut(),)
    if kind == "em":
        return (tr(lang, "t_em"), f"last_seen_utc>=? AND {EM_SQL} AND {REGION_ZONE}",
                (iso(now - timedelta(hours=24)),))
    if kind == "ar":
        if arg == "c":
            rng = user_data.get("range")
            if not rng:
                return tr(lang, "t_archive", p="?"), "0", ()
            return (tr(lang, "t_archive", p=rng[2]),
                    f"last_seen_utc>=? AND first_seen_utc<? AND {IRAQ_ZONE}", (rng[0], rng[1]))
        days = int(arg)
        label = tr(lang, "st_24h") if days == 1 else tr(lang, "days", n=days)
        return (tr(lang, "t_archive", p=label), f"last_seen_utc>=? AND {IRAQ_ZONE}",
                (iso(now - timedelta(days=days)),))
    if kind == "al":
        if arg == "-":
            return tr(lang, "t_airline", a=tr(lang, "unknown")), f"airline_icao IS NULL AND {IRAQ_ZONE}", ()
        return tr(lang, "t_airline", a=arg), f"airline_icao=? AND {IRAQ_ZONE}", (arg,)
    if kind == "ac":
        if arg == "-":
            return tr(lang, "t_type", a=tr(lang, "unknown")), f"aircraft_type IS NULL AND {IRAQ_ZONE}", ()
        return tr(lang, "t_type", a=arg), f"aircraft_type=? AND {IRAQ_ZONE}", (arg,)
    if kind == "w":
        ids = [int(i) for i in (user_data.get("world_ids") or [])][:WORLD_LIST_LIMIT]
        if not ids:
            return tr(lang, "b_world"), "0", ()
        return (user_data.get("world_title") or tr(lang, "b_world")), f"id IN ({','.join(map(str, ids))})", ()
    if kind == "s":
        query = (user_data.get("query") or "").strip()
        if not query:
            return tr(lang, "t_search", q="?"), "0", ()
        pattern = f"%{like_escape(query.upper())}%"
        where = " OR ".join(f"UPPER({c}) LIKE ? ESCAPE '\\'" for c in SEARCH_COLS)
        return tr(lang, "t_search", q=query[:18].upper()), f"({where})", tuple([pattern] * len(SEARCH_COLS))
    return "?", "0", ()


LIST_TAGS = {"24h": "24H", "live": "LIVE", "near": "PRM", "em": "EMG", "ar": "ARC", "al": "OPR",
             "ac": "TYP", "w": "GLB", "s": "QRY"}

async def view_list(update: Update, context: ContextTypes.DEFAULT_TYPE, kind: str, arg: str,
                    page: int) -> None:
    lang = lg(context)
    title, where, args = list_filter(kind, arg, context.user_data, lang)
    total = await Ctx.db.scalar(f"SELECT COUNT(*) FROM flights WHERE {where}", args) or 0
    pages = max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, pages - 1))
    rows = await Ctx.db.q(
        f"SELECT * FROM flights WHERE {where} ORDER BY last_seen_utc DESC LIMIT ? OFFSET ?",
        (*args, PAGE_SIZE, page * PAGE_SIZE))
    context.user_data["back"] = f"L|{kind}|{arg}|{page}"

    out = [head(LIST_TAGS.get(kind, "FLT"), title),
           row(lang, tr(lang, "records"), f"{num(total)} · {tr(lang, 'page')} {page + 1}/{pages}"),
           row(lang, tr(lang, "m_data"), await data_age(lang))]
    if kind == "em":
        out.insert(1, note(lang, tr(lang, "al_body")))
    if not rows:
        out.append(note(lang, tr(lang, "empty_live" if kind in ("live", "near") else "empty")))
    buttons: list[list[InlineKeyboardButton]] = []
    buf: list[InlineKeyboardButton] = []
    table: list[str] = []
    for i, r in enumerate(rows, start=page * PAGE_SIZE + 1):
        tag = "EMG" if is_emergency(r) else TAGS.get(r["crossing_status"], "1OB")
        table.append(f"{i:02d} {tag} {ident(r):<8} {r['aircraft_type'] or '----':<4} "
                     f"{route(r) or r['registration'] or ''}".rstrip())
        alt = f"{int(r['altitude_ft']):>5}ft" if r["altitude_ft"] is not None else "   --- "
        gs = f"{int(r['ground_speed_kt']):>3}kt" if r["ground_speed_kt"] is not None else " --  "
        table.append(f"       {alt} {gs}  {lt(lang, r['last_seen_utc'])}")
        buf.append(btn(f"{i:02d} · {ident(r)}", f"F|{r['id']}", "danger" if tag == "EMG" else None))
        if len(buf) == 2:
            buttons.append(buf)
            buf = []
    if buf:
        buttons.append(buf)
    if rows:
        out += [pre(table), note(lang, tr(lang, "legend"))]
    nav: list[InlineKeyboardButton] = []
    if page > 0:
        nav.append(btn(tr(lang, "b_prev"), f"L|{kind}|{arg}|{page - 1}"))
    nav.append(btn(tr(lang, "b_refresh"), f"L|{kind}|{arg}|{page}"))
    if page < pages - 1:
        nav.append(btn(tr(lang, "b_next"), f"L|{kind}|{arg}|{page + 1}"))
    buttons.append(nav)
    if kind == "s" and context.user_data.get("query"):
        buttons.append([btn(tr(lang, "b_worldthis"), "W|q", "primary")])
    if kind == "em":
        buttons.append([btn(tr(lang, "b_settings"), "M|settings")])
    if kind == "ar" and is_admin(update) and arg != "c":
        buttons.append([btn(tr(lang, "b_export"), f"X|{arg}", "primary")])
    buttons.append(menu_row(lang))
    await respond(update, "\n".join(out), InlineKeyboardMarkup(buttons))


def progress_block(lang: str, r: sqlite3.Row) -> list[str]:
    """Great-circle progress between the database route's airports and the last position."""
    if None in (r["dep_lat"], r["dep_lon"], r["arr_lat"], r["arr_lon"], r["latitude"], r["longitude"]):
        return []
    flown = dist_nm(r["dep_lat"], r["dep_lon"], r["latitude"], r["longitude"])
    remaining = dist_nm(r["latitude"], r["longitude"], r["arr_lat"], r["arr_lon"])
    total = flown + remaining
    if total < 20:
        return []
    pct = max(0.0, min(1.0, flown / total))
    cells = 12
    pos = min(cells - 1, int(pct * cells))
    bar = "▓" * pos + "►" + "░" * (cells - 1 - pos)
    dep = r["dep_iata"] or r["dep_icao"]
    arr = r["arr_iata"] or r["arr_icao"]
    out = [f"<code>{esc(dep)} {bar} {esc(arr)}  {int(pct * 100)}%</code>",
           row(lang, tr(lang, "f_flown"), f"{num(flown)} NM · {num(flown * 1.852)} km"),
           row(lang, tr(lang, "f_remaining"), f"{num(remaining)} NM · {num(remaining * 1.852)} km")]
    speed = r["ground_speed_kt"]
    seen = parse_dt(r["last_seen_utc"])
    if speed and speed > 80 and seen and (now_utc() - seen).total_seconds() < 1800:
        eta = seen + timedelta(hours=remaining / speed)
        out.append(row(lang, tr(lang, "f_eta"),
                       f"≈ {eta.astimezone(Ctx.cfg.tz).strftime('%d/%m %H:%M')} ({tr(lang, 'f_eta_note')})"))
    return out


async def quick_enrich(flight_id: int, seconds: float = 7.0) -> None:
    """Route/aircraft lookup for a page being opened, bounded so the user never waits
    long.  Whatever was fetched is cached; the rest is picked up on the next open."""
    try:
        await asyncio.wait_for(Ctx.enrich.enrich(flight_id), timeout=seconds)
    except asyncio.TimeoutError:
        pass


async def view_flight(update: Update, context: ContextTypes.DEFAULT_TYPE, flight_id: int) -> None:
    lang = lg(context)
    await quick_enrich(flight_id)   # cached after the first time
    r = await Ctx.db.one("SELECT * FROM flights WHERE id=?", (flight_id,))
    if not r:
        await respond(update, head("FLT", tr(lang, "not_found")), InlineKeyboardMarkup([menu_row(lang)]))
        return
    ac_key = r["registration"] or r["mode_s"]
    ac = await Ctx.db.one("SELECT * FROM aircraft WHERE key=?", (ac_key,)) if ac_key else None
    na = tr(lang, "na")
    in_iraq = r["crossing_status"] in ("CONFIRMED", "SINGLE_OBS")
    R = lambda key, value: row(lang, tr(lang, key), value)   # noqa: E731

    title = f"{tr(lang, 's_flight')} {ident(r)}" + (f" · {r['flight_number_iata']}" if r["flight_number_iata"] else "")
    tag = TAGS.get(r["crossing_status"], "1OB")
    out = [head("FLT", title),
           f"{RLM if lang == 'ar' else ''}<code>[{tag}]</code> "
           f"{esc(pick(lang, STATUS_TXT.get(r['crossing_status'], STATUS_TXT['SINGLE_OBS'])))}"]
    if is_emergency(r):
        out.append(f"{RLM if lang == 'ar' else ''}<code>[EMG]</code> <b>SQUAWK {esc(r['squawk'])} · "
                   f"{esc(tr(lang, 'sq_' + r['squawk']))}</b>")

    # ---- flight
    out.append(sect(tr(lang, "s_flight")))
    out.append(R("f_callsign", r["callsign"] or na))
    if r["flight_number_iata"]:
        out.append(R("f_flightno", r["flight_number_iata"]))
    if r["airline_name"]:
        airline = f"{r['airline_name']} ({r['airline_icao'] or r['airline_iata'] or '?'})"
    elif r["airline_icao"]:
        airline = f"{r['airline_icao']} ({tr(lang, 'f_from_callsign')})"
    else:
        airline = na

    def airport(prefix: str) -> str:
        code = " / ".join(x for x in (r[f"{prefix}_iata"], r[f"{prefix}_icao"]) if x)
        place = r[f"{prefix}_city"] or r[f"{prefix}_name"]
        if not code:
            return na
        text = f"{code} · {place}" if place else code
        return f"{text} [{r[f'{prefix}_country']}]" if r[f"{prefix}_country"] else text

    out.append(R("f_airline", airline))
    out.append(R("f_from", airport("dep")))
    out.append(R("f_to", airport("arr")))
    out += progress_block(lang, r)
    if in_iraq and r["route_source"]:
        out.append(R("f_traffic", pick(lang, TRAFFIC.get(r["traffic_type"], TRAFFIC["UNKNOWN"]))))
    if r["route_source"]:
        out.append(note(lang, tr(lang, "f_route_src", s=r["route_source"])))
    elif r["route_checked_utc"]:
        out.append(note(lang, tr(lang, "f_route_none")))
    else:
        out.append(note(lang, tr(lang, "f_route_pending")))

    # ---- aircraft
    out.append(sect(tr(lang, "s_aircraft")))
    model = (ac["type_desc"] if ac and ac["type_desc"] else None) or r["aircraft_type_desc"]
    out.append(R("f_type", r["aircraft_type"] or (ac["type_icao"] if ac and ac["type_icao"] else na)))
    if model:
        out.append(R("f_model", model[:40]))
    if ac and ac["manufacturer"]:
        out.append(R("f_maker", ac["manufacturer"][:40]))
    out.append(R("f_reg", r["registration"] or na))
    out.append(R("f_hex", r["mode_s"] or na))
    if ac and ac["operator_name"]:
        out.append(R("f_owner", ac["operator_name"][:40]))
    country = (ac["owner_country"] if ac and ac["owner_country"] else None) or r["origin_country"]
    if country:
        out.append(R("f_country", country))
    if r["category"]:
        cat = CATEGORIES.get(r["category"].upper())
        out.append(R("f_category", f"{r['category']} · {pick(lang, cat)}" if cat else r["category"]))
    if r["aircraft_classes"]:
        out.append(R("f_class", r["aircraft_classes"]))

    # ---- live data
    out.append(sect(tr(lang, "s_livedata")))
    if r["altitude_ft"] is not None:
        alt = r["altitude_ft"]
        out.append(R("f_alt", f"{num(alt)} ft · FL{int(round(alt / 100)):03d} · {num(alt * 0.3048)} m"))
    else:
        out.append(R("f_alt", na))
    if r["alt_geom_ft"] is not None:
        out.append(R("f_altgeo", f"{num(r['alt_geom_ft'])} ft"))
    if r["ground_speed_kt"] is not None:
        gs = r["ground_speed_kt"]
        out.append(R("f_speed", f"{num(gs)} kt · {num(gs * 1.852)} km/h"))
    else:
        out.append(R("f_speed", na))
    if r["heading"] is not None:
        out.append(R("f_heading", f"{num(r['heading'])}° {compass(lang, r['heading'])}"))
    else:
        out.append(R("f_heading", na))
    if r["vertical_rate"] is not None:
        vr = r["vertical_rate"]
        if abs(vr) < 100:
            out.append(R("f_vrate", tr(lang, "f_level")))
        else:
            out.append(R("f_vrate", f"{'▲ +' if vr > 0 else '▼ -'}{num(abs(vr))} ft/min"))
    if r["squawk"]:
        meaning = {"7500": "sq_7500", "7600": "sq_7600", "7700": "sq_7700", "1200": "sq_vfr",
                   "7000": "sq_vfr"}.get(r["squawk"])
        out.append(R("f_squawk", f"{r['squawk']} · {tr(lang, meaning)}" if meaning else r["squawk"]))
    if r["mach"] is not None:
        out.append(R("f_mach", f"{r['mach']:.3f}"))
    if r["ias_kt"] is not None or r["tas_kt"] is not None:
        out.append(R("f_ias", f"{val(r['ias_kt'])} / {val(r['tas_kt'])} kt"))
    if r["nav_altitude_ft"] is not None:
        out.append(R("f_selalt", f"{num(r['nav_altitude_ft'])} ft"))
    if r["nav_heading"] is not None:
        out.append(R("f_selhdg", f"{num(r['nav_heading'])}°"))
    if r["wind_dir"] is not None and r["wind_kt"] is not None:
        out.append(R("f_wind", f"{num(r['wind_dir'])}° / {num(r['wind_kt'])} kt"))
    if r["oat_c"] is not None:
        out.append(R("f_oat", f"{num(r['oat_c'])} °C"))
    has_pos = r["latitude"] is not None and r["longitude"] is not None
    if has_pos:
        pos = (f"{abs(r['latitude']):.3f}°{'N' if r['latitude'] >= 0 else 'S'} "
               f"{abs(r['longitude']):.3f}°{'E' if r['longitude'] >= 0 else 'W'}")
        out.append(R("f_pos", pos))
        if r["crossing_status"] != "WORLD":
            out.append(R("f_nearcity", nearest_city(lang, r["latitude"], r["longitude"])))
    if r["pos_source"]:
        out.append(R("f_source", POS_SOURCES.get(r["pos_source"], r["pos_source"])))
    out.append(R("f_seen", f"{lt(lang, r['last_seen_utc'])} · {ago(r['last_seen_utc'], lang)}"))

    # ---- Iraq airspace
    if in_iraq:
        out.append(sect(tr(lang, "s_iraq")))
        out.append(R("f_first", lt(lang, r["first_seen_utc"])))
        out.append(R("f_last", lt(lang, r["last_seen_utc"])))
        first, last = parse_dt(r["first_seen_utc"]), parse_dt(r["last_seen_utc"])
        if r["obs_count"] >= 2 and first and last:
            duration = tr(lang, "f_dur_val", n=max(1, int((last - first).total_seconds() // 60)))
        else:
            duration = tr(lang, "f_dur_na")
        out.append(R("f_duration", duration))
        out.append(R("f_obs", r["obs_count"]))
    out += ["", note(lang, tr(lang, "f_times")), note(lang, tr(lang, "tz_note", tz=Ctx.cfg.tz_name)),
            f"<code>REC {flight_id:06d} · SRC {esc(r['data_source'] or '-')} · "
            f"UPD {esc(lt(lang, r['updated_utc'], '%H:%M:%S'))}</code>"]

    user = update.effective_user
    watch_ident = r["callsign"] or r["registration"] or r["mode_s"]
    watched = bool(user and watch_ident and await Ctx.db.scalar(
        "SELECT 1 FROM watch WHERE user_id=? AND ident=?", (user.id, watch_ident)))
    back = context.user_data.get("back")
    kb: list[list[InlineKeyboardButton]] = []
    if has_pos:
        kb.append([url_btn(tr(lang, "b_map"),
                           f"https://www.google.com/maps?q={r['latitude']:.4f},{r['longitude']:.4f}"),
                   btn(tr(lang, "b_pin"), f"P|{flight_id}")])
    kb.append([btn(tr(lang, "b_track"), f"T|{flight_id}|0"), btn(tr(lang, "b_aircraft"), f"A|{flight_id}")])
    kb.append([btn(tr(lang, "b_unfollow" if watched else "b_follow"), f"WA|{flight_id}",
                   "success" if watched else None),
               btn(tr(lang, "b_liveupd"), f"WU|{flight_id}", "primary")])
    kb.append(([btn(tr(lang, "b_back"), back)] if back else []) + menu_row(lang))
    await respond(update, "\n".join(out), InlineKeyboardMarkup(kb))


SPARK = "▁▂▃▄▅▆▇█"


async def view_track(update: Update, context: ContextTypes.DEFAULT_TYPE, flight_id: int, page: int) -> None:
    lang = lg(context)
    r = await Ctx.db.one("SELECT * FROM flights WHERE id=?", (flight_id,))
    if not r:
        await respond(update, head("TRK", tr(lang, "not_found")), InlineKeyboardMarkup([menu_row(lang)]))
        return
    per = 14
    total = await Ctx.db.scalar(
        "SELECT COUNT(*) FROM track_observations WHERE flight_id=?", (flight_id,)) or 0
    pages = max(1, (total + per - 1) // per)
    page = max(0, min(page, pages - 1))
    obs = await Ctx.db.q(
        "SELECT * FROM track_observations WHERE flight_id=? ORDER BY ts_utc LIMIT ? OFFSET ?",
        (flight_id, per, page * per))
    out = [head("TRK", tr(lang, "tr_title", k=ident(r))),
           row(lang, tr(lang, "tr_points"), f"{num(total)} · {tr(lang, 'page')} {page + 1}/{pages}")]
    if not obs:
        out.append(note(lang, tr(lang, "tr_none")))
    else:
        alts = [a[0] for a in await Ctx.db.q(
            "SELECT altitude_ft FROM track_observations WHERE flight_id=? AND altitude_ft IS NOT NULL "
            "ORDER BY ts_utc", (flight_id,))]
        if len(alts) >= 3:
            step = max(1, len(alts) // 24)
            sample = alts[::step][:26]
            low, high = min(sample), max(sample)
            span = (high - low) or 1
            spark = "".join(SPARK[min(7, int((a - low) / span * 7.999))] for a in sample)
            out.append(row(lang, tr(lang, "tr_profile"), f"{spark}  {num(low)}–{num(high)} ft"))
        table = ["TIME   LAT    LON    FL  GS  HDG"]
        for o in obs:
            fl = f"{int(o['altitude_ft'] // 100):03d}" if o["altitude_ft"] is not None else "---"
            gs = f"{int(o['ground_speed_kt']):3d}" if o["ground_speed_kt"] is not None else "---"
            hd = f"{int(o['heading']):03d}" if o["heading"] is not None else "---"
            table.append(f"{local(o['ts_utc'], '%H:%M')}{' ' if o['in_iraq'] else '·'} "
                         f"{o['latitude']:5.2f} {o['longitude']:5.2f} {fl} {gs} {hd}")
        out += [pre(table), note(lang, tr(lang, "tr_outside"))]
    nav = []
    if page > 0:
        nav.append(btn(tr(lang, "b_prev"), f"T|{flight_id}|{page - 1}"))
    if page < pages - 1:
        nav.append(btn(tr(lang, "b_next"), f"T|{flight_id}|{page + 1}"))
    kb = ([nav] if nav else []) + [[btn(tr(lang, "b_flight"), f"F|{flight_id}")], menu_row(lang)]
    await respond(update, "\n".join(out), InlineKeyboardMarkup(kb))


async def view_aircraft_info(update: Update, context: ContextTypes.DEFAULT_TYPE, flight_id: int) -> None:
    lang = lg(context)
    r = await Ctx.db.one("SELECT * FROM flights WHERE id=?", (flight_id,))
    back_kb = [[btn(tr(lang, "b_flight"), f"F|{flight_id}")], menu_row(lang)]
    if not r or not (r["registration"] or r["mode_s"]):
        await respond(update, "\n".join([head("ACF", tr(lang, "s_aircraft")), note(lang, tr(lang, "a_noid"))]),
                      InlineKeyboardMarkup(back_kb))
        return
    key = r["registration"] or r["mode_s"]
    await quick_enrich(flight_id)
    ac = await Ctx.db.one("SELECT * FROM aircraft WHERE key=?", (key,))
    na = tr(lang, "na")
    R = lambda k, v: row(lang, tr(lang, k), v if v not in (None, "") else na)   # noqa: E731
    out = [head("ACF", tr(lang, "a_title", k=key))]
    kb: list[list[InlineKeyboardButton]] = []
    if ac:
        out += [
            R("f_reg", ac["registration"]), R("f_hex", ac["mode_s"]),
            R("f_type", ac["type_icao"] or r["aircraft_type"]),
            R("f_model", (ac["type_desc"] or r["aircraft_type_desc"] or "")[:40]),
            R("f_maker", (ac["manufacturer"] or "")[:40]),
            R("f_owner", (ac["operator_name"] or "")[:40]),
            R("f_country", ac["owner_country"] or r["origin_country"]),
        ]
        if r["category"]:
            cat = CATEGORIES.get(r["category"].upper())
            out.append(R("f_category", f"{r['category']} · {pick(lang, cat)}" if cat else r["category"]))
        if r["aircraft_classes"]:
            out.append(R("f_class", r["aircraft_classes"]))
        count = await Ctx.db.scalar(
            "SELECT COUNT(*) FROM flights WHERE registration=? OR mode_s=?",
            (ac["registration"] or "-", ac["mode_s"] or "-")) or 0
        out += ["", R("a_firstseen", lt(lang, ac["first_seen_utc"], "%d/%m/%Y")),
                R("a_lastseen", lt(lang, ac["last_seen_utc"], "%d/%m/%Y %H:%M")),
                R("a_records", num(count))]
        recent = await Ctx.db.q(
            "SELECT * FROM flights WHERE (registration=? OR mode_s=?) AND id<>? "
            "ORDER BY last_seen_utc DESC LIMIT 6",
            (ac["registration"] or "-", ac["mode_s"] or "-", flight_id))
        if recent:
            out.append(sect(tr(lang, "a_recent")))
            buf: list[InlineKeyboardButton] = []
            table = []
            for f in recent:
                table.append(f"{TAGS.get(f['crossing_status'], '1OB')} {ident(f):<8} "
                             f"{route(f) or '-':<9} {lt(lang, f['last_seen_utc'])}")
                buf.append(btn(f"{ident(f)} · {lt(lang, f['last_seen_utc'], '%d/%m')}", f"F|{f['id']}"))
                if len(buf) == 2:
                    kb.append(buf)
                    buf = []
            if buf:
                kb.append(buf)
            out.append(pre(table))
        if ac["photo_url"] and ac["photo_url"].startswith("https://"):
            kb.insert(0, [url_btn(tr(lang, "b_photo"), ac["photo_url"])])
            out.append(note(lang, tr(lang, "a_photo_by")))
        out.append(note(lang, tr(lang, "a_src")))
    else:
        out.append(note(lang, tr(lang, "empty")))
    await respond(update, "\n".join(out), InlineKeyboardMarkup(kb + back_kb))


async def view_group(update: Update, context: ContextTypes.DEFAULT_TYPE, mode: str, page: int) -> None:
    """Airlines (mode AL) or aircraft types (mode AC) ranked by flights seen inside Iraq."""
    lang = lg(context)
    if mode == "AL":
        col, title, kind, name_sql, tag = "airline_icao", "g_airlines", "al", "MAX(airline_name)", "OPR"
    else:
        col, title, kind, name_sql, tag = "aircraft_type", "g_types", "ac", "MAX(aircraft_type_desc)", "TYP"
    per = 10
    total = await Ctx.db.scalar(
        f"SELECT COUNT(DISTINCT COALESCE({col}, '-')) FROM flights WHERE {IRAQ_ZONE}") or 0
    pages = max(1, (total + per - 1) // per)
    page = max(0, min(page, pages - 1))
    rows = await Ctx.db.q(
        f"SELECT COALESCE({col}, '-') AS code, {name_sql} AS name, COUNT(*) AS n FROM flights "
        f"WHERE {IRAQ_ZONE} GROUP BY code ORDER BY n DESC, code LIMIT ? OFFSET ?", (per, page * per))
    top = rows[0]["n"] if rows else 1
    out = [head(tag, tr(lang, title)),
           row(lang, tr(lang, "g_distinct"), f"{num(total)} · {tr(lang, 'page')} {page + 1}/{pages}")]
    buttons: list[list[InlineKeyboardButton]] = []
    buf: list[InlineKeyboardButton] = []
    if not rows:
        out.append(note(lang, tr(lang, "g_none")))
    table: list[str] = []
    for i, r in enumerate(rows, start=page * per + 1):
        code = "N/A" if r["code"] == "-" else r["code"]
        bar = "█" * max(1, round(r["n"] / top * 6))
        table.append(f"{i:02d} {code:<5} {bar:<6} {r['n']:>4} {(r['name'] or '')[:12]}".rstrip())
        buf.append(btn(f"{code} · {r['n']}", f"L|{kind}|{r['code']}|0"))
        if len(buf) == 2:
            buttons.append(buf)
            buf = []
    if buf:
        buttons.append(buf)
    if table:
        out.append(pre(table))
    nav = []
    if page > 0:
        nav.append(btn(tr(lang, "b_prev"), f"{mode}|{page - 1}"))
    if page < pages - 1:
        nav.append(btn(tr(lang, "b_next"), f"{mode}|{page + 1}"))
    if nav:
        buttons.append(nav)
    buttons.append(menu_row(lang))
    await respond(update, "\n".join(out), InlineKeyboardMarkup(buttons))


async def view_stats(update: Update, context: ContextTypes.DEFAULT_TYPE, days: int) -> None:
    lang = lg(context)
    db = Ctx.db
    label = {0: tr(lang, "st_alltime"), 1: tr(lang, "st_24h")}.get(days, tr(lang, "days", n=days))
    since = iso(now_utc() - timedelta(days=days)) if days else "0000"
    base = "last_seen_utc>=? AND crossing_status='CONFIRMED'"
    args = (since,)
    total = await db.scalar(f"SELECT COUNT(*) FROM flights WHERE {base}", args) or 0
    single = await db.scalar(
        "SELECT COUNT(*) FROM flights WHERE last_seen_utc>=? AND crossing_status='SINGLE_OBS'", args) or 0
    R = lambda key, value: row(lang, tr(lang, key), value)   # noqa: E731
    out = [head("STAT", tr(lang, "st_title", p=label)),
           R("st_confirmed", num(total)), R("st_single", num(single))]
    if total:
        agg = await db.one(
            f"SELECT COUNT(DISTINCT airline_icao) a, COUNT(DISTINCT aircraft_type) t, "
            f"COUNT(airline_icao) ha, COUNT(aircraft_type) ht, COUNT(dep_icao) hd "
            f"FROM flights WHERE {base}", args)
        out += [R("st_airlines", num(agg["a"])), R("st_types", num(agg["t"]))]

        kinds = await db.q(
            f"SELECT traffic_type k, COUNT(*) n FROM flights WHERE {base} GROUP BY k ORDER BY n DESC", args)
        out.append(sect(tr(lang, "st_mix")))
        out += [row(lang, pick(lang, TRAFFIC.get(k["k"], TRAFFIC["UNKNOWN"])),
                    f"{num(k['n'])}  ({round(100 * k['n'] / total)}%)") for k in kinds]

        async def top(col: str, title: str, name_col: Optional[str] = None) -> None:
            name_sql = f"MAX({name_col})" if name_col else "NULL"
            rows = await db.q(
                f"SELECT {col} c, {name_sql} nm, COUNT(*) n FROM flights WHERE {base} AND {col} IS NOT NULL "
                f"GROUP BY c ORDER BY n DESC LIMIT 5", args)
            out.append(sect(tr(lang, title)))
            if not rows:
                out.append(note(lang, tr(lang, "st_nodata")))
            else:
                out.append(pre([f"{i} {x['c']:<5} {x['n']:>4}  {(x['nm'] or '')[:18]}".rstrip()
                                for i, x in enumerate(rows, 1)]))

        await top("airline_icao", "st_top_al", "airline_name")
        await top("aircraft_type", "st_top_ac", "aircraft_type_desc")
        await top("dep_icao", "st_top_dep", "dep_city")
        await top("arr_icao", "st_top_arr", "arr_city")

        hours = [0] * 24
        for f in await db.q(f"SELECT first_seen_utc FROM flights WHERE {base}", args):
            dt = parse_dt(f[0])
            if dt:
                hours[dt.astimezone(Ctx.cfg.tz).hour] += 1
        peak = max(hours) or 1
        out.append(sect(tr(lang, "st_hourly", tz=Ctx.cfg.tz_name)))
        out.append(pre([f"{h:02d} {'█' * round(hours[h] / peak * 14):<14} {hours[h]}" for h in range(24)]))

        avg = await db.one(
            "SELECT AVG(o.altitude_ft) alt, AVG(o.ground_speed_kt) gs, COUNT(o.altitude_ft) n "
            "FROM track_observations o JOIN flights f ON f.id=o.flight_id "
            "WHERE f.last_seen_utc>=? AND f.crossing_status='CONFIRMED' AND o.in_iraq=1", args)
        if avg["alt"] is not None:
            out.append(R("st_avg_alt", f"{num(avg['alt'])} ft"))
        if avg["gs"] is not None:
            out.append(R("st_avg_gs", f"{num(avg['gs'])} kt"))
        out.append(note(lang, tr(lang, "st_from_obs", n=num(avg["n"]))))
        out.append(sect(tr(lang, "st_complete")))
        out.append(f"<code>{esc(tr(lang, 'st_c_airline'))} {round(100 * agg['ha'] / total)}% · "
                   f"{esc(tr(lang, 'st_c_type'))} {round(100 * agg['ht'] / total)}% · "
                   f"{esc(tr(lang, 'st_c_route'))} {round(100 * agg['hd'] / total)}%</code>")
    coverage = await db.scalar(f"SELECT MIN(first_seen_utc) FROM flights WHERE {IRAQ_ZONE}")
    out.append("")
    if coverage:
        out.append(R("st_starts", lt(lang, coverage, "%d/%m/%Y")))
        if days and parse_dt(coverage) > now_utc() - timedelta(days=days) + timedelta(hours=1):  # type: ignore[operator]
            out.append(note(lang, tr(lang, "st_partial")))
    out.append(note(lang, tr(lang, "st_note")))
    kb = InlineKeyboardMarkup([
        [btn("24h", "S|1"), btn("7d", "S|7"), btn("30d", "S|30"), btn(tr(lang, "b_all"), "S|0")],
        menu_row(lang)])
    await respond(update, "\n".join(out), kb)


async def view_archive_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    coverage = await Ctx.db.scalar(f"SELECT MIN(first_seen_utc) FROM flights WHERE {IRAQ_ZONE}")
    out = [head("ARC", tr(lang, "ar_title")),
           row(lang, tr(lang, "st_starts"), lt(lang, coverage, "%d/%m/%Y")),
           note(lang, tr(lang, "ar_note")), "",
           f"{RLM if lang == 'ar' else ''}{esc(tr(lang, 'ar_pick'))}"]
    kb = InlineKeyboardMarkup([
        [btn(tr(lang, "b_p24"), "L|ar|1|0")],
        [btn(tr(lang, "b_p7"), "L|ar|7|0"), btn(tr(lang, "b_p30"), "L|ar|30|0")],
        [btn(tr(lang, "b_custom"), "M|range")],
        menu_row(lang)])
    await respond(update, "\n".join(out), kb)


async def view_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    db = Ctx.db
    last = await db.one("SELECT * FROM sync_history ORDER BY id DESC LIMIT 1")
    flights = await db.scalar(f"SELECT COUNT(*) FROM flights WHERE {IRAQ_ZONE}") or 0
    obs = await db.scalar("SELECT COUNT(*) FROM track_observations") or 0
    live = await db.get_status("live_access") or "-"
    nxt = Ctx.sync.next_run
    up = now_utc() - Ctx.started
    na = tr(lang, "na")
    R = lambda key, value: row(lang, tr(lang, key), value)   # noqa: E731
    out = [head("SYS", tr(lang, "ss_title")),
           R("ss_bot", f"{tr(lang, 'ss_online')} · v{APP_VERSION}"),
           R("ss_uptime", f"{up.days}d {up.seconds // 3600}h {(up.seconds // 60) % 60}m"),
           R("ss_feed", live),
           R("m_sources", await db.get_status("provider") or tr(lang, "none_yet")),
           sect(tr(lang, "ss_lastsync")),
           R("ss_lastsync", ago(last["finished_utc"], lang) if last else na),
           R("ss_result", last["status"] if last else na),
           R("ss_received", num(last["received"]) if last else na),
           R("ss_iniraq", num(last["in_iraq"]) if last else na),
           R("ss_around", num(max(0, last["inserted"] + last["updated"] - last["in_iraq"])) if last else na),
           R("ss_next", lt(lang, iso(nxt), "%H:%M:%S") if nxt else na),
           R("ss_interval", f"{Ctx.cfg.sync_interval}s"),
           "",
           R("ss_flights", num(flights)), R("ss_points", num(obs))]
    if last and last["detail"]:
        out.append(sect(tr(lang, "ss_feeds")))
        out.append(pre([part.strip()[:44] for part in last["detail"].split(";")]))
    if last and last["status"] != "OK":
        out.append(note(lang, tr(lang, "ss_serving")))
    kb = InlineKeyboardMarkup([[btn(tr(lang, "b_refresh"), "M|status")], menu_row(lang)])
    await respond(update, "\n".join(out), kb)


async def view_about(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    cfg = Ctx.cfg
    links = " · ".join(f'<a href="{PROVIDERS[p][1]}">{esc(PROVIDERS[p][0])}</a>' for p in cfg.providers)
    out = [head("INFO", tr(lang, "ab_title")),
           pre([f"SYSTEM   IATM v{APP_VERSION}", "SCOPE    ORBB FIR + 250 NM PERIMETER",
                f"DEV      @{cfg.dev_username}", f"CHANNEL  @{cfg.channel}"]),
           line(lang, tr(lang, "ab_body")),
           sect(tr(lang, "ab_data")),
           f"<code>│</code> LIVE: {links}",
           '<code>│</code> REF: <a href="https://www.adsbdb.com">adsbdb</a> · '
           '<a href="https://hexdb.io">hexdb.io</a> · '
           '<a href="https://www.planespotters.net">planespotters.net</a>',
           note(lang, tr(lang, "ab_data_note"))]
    kb = InlineKeyboardMarkup([credit_row(lang), menu_row(lang)])
    await respond(update, "\n".join(out), kb)


async def view_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    out = [head("MAN", tr(lang, "h_title")), esc(tr(lang, "h_body")), "", note(lang, tr(lang, "legend")),
           esc(tr(lang, "h_marks"))]
    await respond(update, "\n".join(out), InlineKeyboardMarkup([menu_row(lang)]))


async def view_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    user = update.effective_user
    uid = user.id if user else 0
    alerts = bool(await Ctx.db.scalar("SELECT alerts FROM users WHERE user_id=?", (uid,)))
    followed = await Ctx.db.scalar("SELECT COUNT(*) FROM watch WHERE user_id=?", (uid,)) or 0
    out = [head("CFG", tr(lang, "set_title")),
           row(lang, tr(lang, "set_lang"), tr(lang, "set_lang_v")),
           row(lang, tr(lang, "set_alerts"), tr(lang, "set_on" if alerts else "set_off")),
           row(lang, tr(lang, "set_watch"), f"{followed}/{WATCH_LIMIT}"),
           "", note(lang, tr(lang, "set_alerts_note"))]
    kb = InlineKeyboardMarkup([
        [btn(tr(lang, "b_lang"), "M|lang")],
        [btn(tr(lang, "b_alerts_on" if alerts else "b_alerts_off"), "ST|alerts",
             "success" if alerts else None)],
        [btn(tr(lang, "b_watch"), "M|watch")],
        menu_row(lang)])
    await respond(update, "\n".join(out), kb)


async def view_watchlist(update: Update, context: ContextTypes.DEFAULT_TYPE, flash: str = "") -> None:
    lang = lg(context)
    user = update.effective_user
    rows = await Ctx.db.q("SELECT ident FROM watch WHERE user_id=? ORDER BY created_utc",
                          (user.id if user else 0,))
    out = [head("WL", tr(lang, "wl_title"))]
    if flash:
        out.append(f"<b>{esc(flash)}</b>")
    out.append(note(lang, tr(lang, "wl_body")))
    out.append("")
    if rows:
        out.append(pre([f"{i:02d}  {r['ident']}" for i, r in enumerate(rows, 1)]))
    else:
        out.append(note(lang, tr(lang, "wl_empty")))
    out += ["", note(lang, tr(lang, "wl_how"))]
    kb: list[list[InlineKeyboardButton]] = []
    buf: list[InlineKeyboardButton] = []
    for r in rows:
        buf.append(btn(tr(lang, "b_remove", x=r["ident"]), f"WR|{r['ident']}", "danger"))
        if len(buf) == 3:
            kb.append(buf)
            buf = []
    if buf:
        kb.append(buf)
    kb += [[btn(tr(lang, "b_add_watch"), "M|watchadd", "primary")], menu_row(lang)]
    await respond(update, "\n".join(out), InlineKeyboardMarkup(kb))


async def watch_add(update: Update, context: ContextTypes.DEFAULT_TYPE, raw: str) -> str:
    """Add an identifier to the user's watchlist. Returns the message to show."""
    lang = lg(context)
    user = update.effective_user
    ident_text = raw.strip().upper().replace(" ", "")
    if not user or not WORLD_QUERY.match(ident_text):
        return tr(lang, "w_invalid")
    count = await Ctx.db.scalar("SELECT COUNT(*) FROM watch WHERE user_id=?", (user.id,)) or 0
    if count >= WATCH_LIMIT:
        return tr(lang, "wl_full", n=WATCH_LIMIT)
    await Ctx.db.run("INSERT OR IGNORE INTO watch(user_id, ident, created_utc) VALUES(?,?,?)",
                     (user.id, ident_text, iso(now_utc())))
    return tr(lang, "wl_added", x=ident_text)


# --------------------------------------------------------------------------
# COMMAND HANDLERS
# --------------------------------------------------------------------------
async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data.pop("await", None)
    await view_main(update, context)


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_help(update, context)


async def cmd_about(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_about(update, context)


async def cmd_lang(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_lang(update, context)


async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_settings(update, context)


async def cmd_console(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    console = console_btn(lang)
    if not console:
        await respond(update, note(lang, tr(lang, "console_off")), InlineKeyboardMarkup([menu_row(lang)]))
        return
    await respond(update, "\n".join([head("WEB", tr(lang, "b_console")), line(lang, tr(lang, "console_txt"))]),
                  InlineKeyboardMarkup([[console], menu_row(lang)]))


async def cmd_last24(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_list(update, context, "24h", "-", 0)


async def cmd_live(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_list(update, context, "live", "-", 0)


async def cmd_around(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_list(update, context, "near", "-", 0)


async def cmd_alerts(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_list(update, context, "em", "-", 0)


async def cmd_watchlist(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_watchlist(update, context)


async def prompt_watch(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    context.user_data["await"] = "watch"
    await respond(update, "\n".join([head("WL", tr(lang, "wl_title")), esc(tr(lang, "wl_send")),
                                     "<code>QTR8K</code> · <code>A7-ALA</code> · <code>06A1E5</code>"]),
                  InlineKeyboardMarkup([menu_row(lang)]))


async def cmd_watch(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not context.args:
        await prompt_watch(update, context)
        return
    await view_watchlist(update, context, await watch_add(update, context, "".join(context.args)))


async def cmd_unwatch(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    flash = ""
    if context.args and user:
        ident_text = "".join(context.args).strip().upper()
        await Ctx.db.run("DELETE FROM watch WHERE user_id=? AND ident=?", (user.id, ident_text))
        flash = tr(lg(context), "wl_removed", x=ident_text)
    await view_watchlist(update, context, flash)


async def prompt_search(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    context.user_data["await"] = "search"
    out = [head("QRY", tr(lang, "se_title")), f"{RLM if lang == 'ar' else ''}{esc(tr(lang, 'se_send'))}", "",
           note(lang, tr(lang, "se_ex"))]
    await respond(update, "\n".join(out), InlineKeyboardMarkup([menu_row(lang)]))


async def run_search(update: Update, context: ContextTypes.DEFAULT_TYPE, query: str) -> None:
    lang = lg(context)
    query = query.strip()[:40]
    if len(query) < 2:
        await respond(update, esc(tr(lang, "se_short")), InlineKeyboardMarkup([menu_row(lang)]))
        return
    context.user_data["query"] = query
    context.user_data.pop("await", None)
    await view_list(update, context, "s", "-", 0)


async def cmd_search(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if context.args:
        await run_search(update, context, " ".join(context.args))
    else:
        await prompt_search(update, context)


async def cmd_flight(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not context.args:
        await prompt_search(update, context)
        return
    term = "".join(context.args).upper()[:20]
    found = await Ctx.db.one(
        "SELECT id FROM flights WHERE callsign=? OR flight_number_iata=? OR flight_number_icao=? "
        "OR registration=? OR mode_s=? ORDER BY last_seen_utc DESC LIMIT 1", (term,) * 5)
    if found:
        await view_flight(update, context, found["id"])
    else:
        await run_search(update, context, " ".join(context.args))


async def cmd_airlines(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_group(update, context, "AL", 0)


async def cmd_aircraft(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_group(update, context, "AC", 0)


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_stats(update, context, 1)


async def cmd_archive(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_archive_menu(update, context)


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_status(update, context)


# --------------------------------------------------------------------------
# WORLDWIDE ON-DEMAND LOOKUPS
# --------------------------------------------------------------------------
WORLD_QUERY = re.compile(r"^[A-Z0-9-]{2,10}$")
HEX_QUERY = re.compile(r"^[0-9A-F]{6}$")


def world_throttled(context: ContextTypes.DEFAULT_TYPE, seconds: float = 4.0) -> bool:
    """Each worldwide lookup hits the community feeds directly: space them out per user."""
    last = context.user_data.get("world_ts", 0.0)
    if time.monotonic() - last < seconds:
        return True
    context.user_data["world_ts"] = time.monotonic()
    return False


def world_kb(lang: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[btn(tr(lang, "b_newworld"), "M|world")], menu_row(lang)])


async def prompt_world(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    context.user_data["await"] = "world"
    mark = RLM if lang == "ar" else ""
    out = [head("GLB", tr(lang, "w_title")),
           f"{mark}{esc(tr(lang, 'w_one'))}",
           "<code>QTR8K</code> · <code>A7-ALA</code> · <code>06A1E5</code>", "",
           f"{mark}{esc(tr(lang, 'w_area'))}",
           "<code>/near 51.47 -0.45</code>\n<code>/near 25.25 55.36 150</code>", "",
           note(lang, tr(lang, "w_live"))]
    await respond(update, "\n".join(out), InlineKeyboardMarkup([menu_row(lang)]))


async def show_world_results(update: Update, context: ContextTypes.DEFAULT_TYPE, records: list[dict],
                             title: str) -> None:
    lang = lg(context)
    res = await Ctx.db.ingest(records, "WORLD", now_utc())
    ids = res["ids"]
    if not ids:
        await respond(update, "\n".join([head("GLB", title), esc(tr(lang, "w_ground"))]), world_kb(lang))
        return
    context.user_data.pop("await", None)
    if len(ids) == 1:
        context.user_data.pop("back", None)
        await view_flight(update, context, ids[0])
        return
    context.user_data["world_ids"] = ids[:WORLD_LIST_LIMIT]
    context.user_data["world_title"] = title
    await view_list(update, context, "w", "-", 0)


async def run_world(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str) -> None:
    lang = lg(context)
    query = text.strip().upper().replace(" ", "")
    if not WORLD_QUERY.match(query):
        await respond(update, esc(tr(lang, "w_invalid")), world_kb(lang))
        return
    if world_throttled(context):
        await respond(update, esc(tr(lang, "w_wait")), world_kb(lang))
        return
    kinds = ["hex", "callsign"] if HEX_QUERY.match(query) else (
        ["reg"] if "-" in query else ["callsign", "reg"])
    records: list[dict] = []
    answered = 0
    for kind in kinds:
        records, _, n = await Ctx.api.find(kind, query)
        answered += n
        if records:
            break
    title = tr(lang, "t_world", q=query)
    if not records:
        body = tr(lang, "w_notfound") if answered else tr(lang, "w_nofeed")
        await respond(update, "\n".join([head("GLB", title), esc(body)]), world_kb(lang))
        return
    await show_world_results(update, context, records, title)


async def run_near(update: Update, context: ContextTypes.DEFAULT_TYPE, lat: float, lon: float,
                   radius_nm: int = 100) -> None:
    lang = lg(context)
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        await respond(update, esc(tr(lang, "w_badcoord")), world_kb(lang))
        return
    if world_throttled(context):
        await respond(update, esc(tr(lang, "w_wait")), world_kb(lang))
        return
    radius_nm = max(5, min(QUERY_RADIUS_NM, radius_nm))
    records, _, answered = await Ctx.api.around(lat, lon, radius_nm)
    title = tr(lang, "t_nearpt", lat=f"{lat:.1f}", lon=f"{lon:.1f}", r=radius_nm)
    airborne = [r for r in records if r["status"] != "ON_GROUND"]
    if not airborne:
        body = tr(lang, "w_noarea") if answered else tr(lang, "w_nofeed")
        await respond(update, "\n".join([head("GLB", title), esc(body)]), world_kb(lang))
        return
    airborne.sort(key=lambda r: dist_nm(lat, lon, r["latitude"], r["longitude"]))
    await show_world_results(update, context, airborne[:WORLD_LIST_LIMIT], title)


async def cmd_world(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if context.args:
        await run_world(update, context, "".join(context.args))
    else:
        await prompt_world(update, context)


async def cmd_near(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    parts = " ".join(a.replace(",", " ") for a in (context.args or [])).split()
    try:
        lat, lon = float(parts[0]), float(parts[1])
        radius = int(float(parts[2])) if len(parts) > 2 else 100
    except (ValueError, IndexError):
        await prompt_world(update, context)
        return
    await run_near(update, context, lat, lon, radius)


async def on_location(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    loc = update.effective_message.location if update.effective_message else None
    if loc:
        await run_near(update, context, loc.latitude, loc.longitude, 100)


async def world_update(update: Update, context: ContextTypes.DEFAULT_TYPE, flight_id: int) -> None:
    """Re-query one stored flight live (by hex, else callsign) and show it again."""
    r = await Ctx.db.one("SELECT mode_s, callsign FROM flights WHERE id=?", (flight_id,))
    if r and not world_throttled(context, 3.0):
        kind, query = ("hex", r["mode_s"]) if r["mode_s"] and HEX_QUERY.match(r["mode_s"]) else (
            "callsign", r["callsign"])
        if query and WORLD_QUERY.match(query):
            records, _, _ = await Ctx.api.find(kind, query)
            if records:
                await Ctx.db.ingest(records, "WORLD", now_utc())
    await view_flight(update, context, flight_id)


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    lang = lg(context)
    text = (update.effective_message.text or "") if update.effective_message else ""
    text = text.strip(" \t\r\n‎‏​‪‫‬")
    if text.startswith("/"):
        # A command Telegram did not tag as one (leading space, pasted text ...).
        parts = text[1:].split()
        handler = COMMANDS.get(parts[0].split("@")[0].lower()) if parts else None
        if handler:
            context.args = parts[1:]
            await handler(update, context)
        else:
            await respond(update, esc(tr(lang, "unknown_cmd")), InlineKeyboardMarkup([menu_row(lang)]))
        return
    mode = context.user_data.get("await")
    if mode == "range":
        parts = text.replace(",", " ").replace(" to ", " ").split()
        try:
            if len(parts) != 2:
                raise ValueError
            start = datetime.strptime(parts[0], "%Y-%m-%d").replace(tzinfo=Ctx.cfg.tz)
            end = datetime.strptime(parts[1], "%Y-%m-%d").replace(tzinfo=Ctx.cfg.tz) + timedelta(days=1)
            if end <= start:
                raise ValueError
        except ValueError:
            await respond(update, esc(tr(lang, "ar_bad")), InlineKeyboardMarkup([menu_row(lang)]))
            return
        label = f"{start:%d/%m}–{(end - timedelta(days=1)):%d/%m}"
        context.user_data["range"] = (iso(start), iso(end), label)
        context.user_data.pop("await", None)
        await view_list(update, context, "ar", "c", 0)
    elif mode == "world":
        await run_world(update, context, text)
    elif mode == "watch":
        context.user_data.pop("await", None)
        await view_watchlist(update, context, await watch_add(update, context, text))
    elif text:
        await run_search(update, context, text)


# --------------------------------------------------------------------------
# ADMIN
# --------------------------------------------------------------------------
async def deny(update: Update) -> None:
    await respond(update, pre(header("ACCESS DENIED") + ["ADMINISTRATORS ONLY."]),
                  InlineKeyboardMarkup([menu_row()]))


def admin_only(func):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_admin(update):
            ev("admin command denied", user=update.effective_user.id if update.effective_user else None)
            await deny(update)
            return
        await func(update, context)
    wrapper.__name__ = func.__name__
    return wrapper


def admin_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [btn("SYSTEM", "AD|system"), btn("DATABASE", "AD|database")],
        [btn("SYNC NOW", "AD|sync"), btn("SYNC LOG", "AD|synclog")],
        [btn("EXPORT 24H", "X|1"), btn("EXPORT 7D", "X|7"), btn("EXPORT 30D", "X|30")],
        [btn("RESTART INFO", "AD|restart"), btn("USERS", "AD|users")],
        menu_row()])


async def admin_panel(update: Update) -> None:
    lines = header("ADMIN CONSOLE") + [
        "/system       health + feed check",
        "/sync         run a sync now",
        "/sync log     recent sync results",
        "/database     database statistics",
        "/export [days|all]  CSV export",
        "/restart_info process history",
        "/users        user statistics",
        "/broadcast <text>  message all users"]
    await respond(update, pre(lines), admin_kb())


async def admin_system(update: Update) -> None:
    api = Ctx.api
    try:
        with open("/proc/self/status") as fh:
            rss = next((l.split()[1] for l in fh if l.startswith("VmRSS")), None)
        mem = f"{int(rss) // 1024} MB" if rss else NA
    except Exception:
        mem = NA
    state = "REACHABLE" if api.last_ok and not api.last_error else (
        "FAILING" if api.last_error else "NOT CONTACTED YET")
    lines = header("SYSTEM HEALTH") + [
        f"FEED      {state}",
        f"ANSWERED  {api.last_provider or NA}",
        f"ORDER     {','.join(Ctx.cfg.providers)[:30]}",
        f"LAST OK   {ago(iso(api.last_ok)) if api.last_ok else NA}",
        f"LATENCY   {val(api.last_latency_ms, ' ms')}",
        f"LAST ERR  {(api.last_error or 'none')[:60]}",
        f"LOOKUPS   {Ctx.enrich.lookups} route/aircraft",
        f"LOOKUP ERR {(Ctx.enrich.last_error or 'none')[:50]}",
        "(use SYNC NOW to test the feed)",
        SUB,
        f"SYNC TASK {'RUNNING' if not Ctx.sync.stop.is_set() else 'STOPPING'}",
        f"CYCLES    {Ctx.sync.cycles}",
        SUB,
        f"PYTHON    {platform.python_version()}",
        f"MEMORY    {mem}",
        f"STARTED   {local(iso(Ctx.started))}",
        f"ADMINS    {len(Ctx.cfg.admin_ids)}",
        SUB,
        f"FORCE SUB {'ON  @' + Ctx.cfg.channel if Ctx.cfg.force_sub else 'OFF'}",
        f"SUB CHECK {'OK' if not Ctx.sub_error else 'FAILING - make the bot'}",
        *([" an ADMIN of the channel.", f" {Ctx.sub_error[:60]}"] if Ctx.sub_error else []),
    ]
    await respond(update, pre(lines), admin_kb())


async def admin_database(update: Update) -> None:
    db = Ctx.db
    counts = {}
    for table in ("flights", "track_observations", "aircraft", "airlines", "sync_history"):
        counts[table] = await db.scalar(f"SELECT COUNT(*) FROM {table}") or 0
    confirmed = await db.scalar("SELECT COUNT(*) FROM flights WHERE crossing_status='CONFIRMED'") or 0
    nearby = await db.scalar("SELECT COUNT(*) FROM flights WHERE crossing_status='NEARBY'") or 0
    span = await db.one("SELECT MIN(first_seen_utc), MAX(last_seen_utc) FROM flights")
    try:
        size = sum(os.path.getsize(Ctx.cfg.db_path + s) for s in ("", "-wal")
                   if os.path.exists(Ctx.cfg.db_path + s))
        size_text = f"{size / 1048576:.1f} MB"
        st = os.statvfs(os.path.dirname(Ctx.cfg.db_path) or ".")
        free_text = f"{st.f_bavail * st.f_frsize / 1048576:.0f} MB"
    except Exception:
        size_text = free_text = NA
    integrity = await db.scalar("PRAGMA quick_check")
    lines = header("DATABASE") + [
        f"PATH      {Ctx.cfg.db_path}",
        f"SIZE      {size_text}",
        f"DISK FREE {free_text}",
        f"INTEGRITY {integrity}",
        SUB,
        f"FLIGHTS       {counts['flights']}",
        f" CONFIRMED    {confirmed}",
        f" NEARBY ONLY  {nearby}",
        f"TRACK POINTS  {counts['track_observations']}",
        f"AIRCRAFT      {counts['aircraft']}",
        f"AIRLINES      {counts['airlines']}",
        f"SYNC RECORDS  {counts['sync_history']}",
        SUB,
        f"OLDEST  {local(span[0], '%d %b %Y %H:%M')}",
        f"NEWEST  {local(span[1], '%d %b %Y %H:%M')}",
        f"TRACK RETENTION {Ctx.cfg.track_retention_days or '∞'} days",
        f"NEARBY KEPT     {Ctx.cfg.nearby_retention_days} days",
    ]
    await respond(update, pre(lines), admin_kb())


async def admin_synclog(update: Update) -> None:
    rows = await Ctx.db.q("SELECT * FROM sync_history ORDER BY id DESC LIMIT 12")
    lines = header("SYNC HISTORY") + ["TIME  STATUS       RECV  IRQ"]
    for r in rows:
        lines.append(f"{local(r['started_utc'], '%H:%M')} {r['status'][:12]:<12} "
                     f"{r['received']:>4} {r['in_iraq']:>4}")
        if r["status"] != "OK" and r["detail"]:
            lines.append(f"  └ {r['detail'][:60]}")
    if not rows:
        lines.append("NO SYNCHRONISATION YET.")
    lines += [SUB, "RECV = aircraft in query area", "IRQ  = with positions in Iraq"]
    await respond(update, pre(lines), admin_kb())


def sync_report(row: dict) -> list[str]:
    return [
        f"STATUS    {row['status']}",
        f"RECEIVED  {row['received']}", f"IN IRAQ   {row['in_iraq']}",
        f"AROUND    {row['nearby']}",
        f"NEW       {row['inserted']}", f"UPDATED   {row['updated']}",
        f"UNUSABLE  {row['skipped']}",
    ] + ([SUB, "FEEDS (with position/total)"] + [f" {x.strip()[:60]}" for x in row["detail"].split(";")]
         if row["detail"] else [])


async def admin_sync(update: Update) -> None:
    if Ctx.sync.lock.locked():
        await respond(update, pre(["A SYNC IS ALREADY RUNNING."]), admin_kb())
        return
    await respond(update, pre(["SYNCHRONISING …"]))
    row = await Ctx.sync.sync_live("manual")
    await respond(update, pre(header("MANUAL SYNC") + sync_report(row)), admin_kb())


async def admin_restart_info(update: Update) -> None:
    runs = await Ctx.db.q("SELECT * FROM runs ORDER BY id DESC LIMIT 6")
    lines = header("RESTART INFO") + [
        f"CURRENT START {local(iso(Ctx.started), '%d %b %H:%M:%S')}",
        f"DEPLOYMENT    {(os.getenv('RAILWAY_DEPLOYMENT_ID') or 'n/a')[:12]}",
        f"SERVICE       {(os.getenv('RAILWAY_SERVICE_NAME') or 'n/a')[:14]}",
        f"REPLICA       {(os.getenv('RAILWAY_REPLICA_ID') or 'n/a')[:12]}",
        SUB, "RECENT RUNS (start > stop)"]
    for r in runs:
        stop = local(r["stopped_utc"], "%d%b %H:%M") if r["stopped_utc"] else "running/killed"
        lines.append(f"{local(r['started_utc'], '%d%b %H:%M')} > {stop}")
        lines.append(f"  └ {r['stop_reason'] or 'no clean shutdown recorded'}")
    await respond(update, pre(lines), admin_kb())


EXPORT_COLS = ["id", "callsign", "flight_number_iata", "airline_icao", "airline_name",
               "dep_icao", "dep_iata", "dep_city", "dep_country", "arr_icao", "arr_iata", "arr_city",
               "arr_country", "route_source", "traffic_type", "aircraft_type", "aircraft_type_desc",
               "aircraft_classes", "registration", "mode_s",
               "first_seen_utc", "last_seen_utc", "obs_count", "crossing_status",
               "altitude_ft", "ground_speed_kt", "heading", "latitude", "longitude", "data_source"]


async def admin_export(update: Update, days: int) -> None:
    where, args = ("crossing_status IN ('CONFIRMED','SINGLE_OBS')", ()) if days <= 0 else (
        "last_seen_utc>=? AND crossing_status IN ('CONFIRMED','SINGLE_OBS')", (iso(now_utc() - timedelta(days=days)),))
    rows = await Ctx.db.q(
        f"SELECT {','.join(EXPORT_COLS)} FROM flights WHERE {where} ORDER BY first_seen_utc", args)
    if not rows:
        await respond(update, pre(["NOTHING TO EXPORT FOR THIS PERIOD."]), admin_kb())
        return
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(EXPORT_COLS + ["first_seen_local", "last_seen_local"])
    for r in rows:
        writer.writerow([("" if v is None else v) for v in r] + [
            local(r["first_seen_utc"], "%Y-%m-%d %H:%M:%S"), local(r["last_seen_utc"], "%Y-%m-%d %H:%M:%S")])
    payload = io.BytesIO(buf.getvalue().encode("utf-8-sig"))
    label = "all" if days <= 0 else f"{days}d"
    payload.name = f"iraq_air_traffic_{label}_{now_utc():%Y%m%d_%H%M}Z.csv"
    if update.effective_chat:
        await update.get_bot().send_document(
            update.effective_chat.id, payload, filename=payload.name,
            caption=f"{len(rows)} flight records · {label} · times UTC + {Ctx.cfg.tz_name}")
    ev("csv export", rows=len(rows), period=label,
       user=update.effective_user.id if update.effective_user else None)


@admin_only
async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await admin_panel(update)


@admin_only
async def cmd_system(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await admin_system(update)


@admin_only
async def cmd_sync(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    args = context.args or []
    if args and args[0].lower() == "log":
        await admin_synclog(update)
    else:
        await admin_sync(update)


@admin_only
async def cmd_database(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await admin_database(update)


@admin_only
async def cmd_export(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    arg = (context.args[0].lower() if context.args else "1")
    days = 0 if arg == "all" else (int(arg) if arg.isdigit() else 1)
    await admin_export(update, days)


@admin_only
async def cmd_restart_info(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await admin_restart_info(update)


@admin_only
async def cmd_users(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await admin_users(update)


async def admin_users(update: Update) -> None:
    db = Ctx.db
    day = iso(now_utc() - timedelta(hours=24))
    total = await db.scalar("SELECT COUNT(*) FROM users") or 0
    lines = header("USERS") + [
        f"TOTAL        {total}",
        f"ACTIVE 24H   {await db.scalar('SELECT COUNT(*) FROM users WHERE last_seen_utc>=?', (day,)) or 0}",
        f"NEW 24H      {await db.scalar('SELECT COUNT(*) FROM users WHERE first_seen_utc>=?', (day,)) or 0}",
        SUB,
        f"ARABIC       {await db.scalar('SELECT COUNT(*) FROM users WHERE lang=?', ('ar',)) or 0}",
        f"ENGLISH      {await db.scalar('SELECT COUNT(*) FROM users WHERE lang=?', ('en',)) or 0}",
        SUB,
        f"ALERTS ON    {await db.scalar('SELECT COUNT(*) FROM users WHERE alerts=1') or 0}",
        f"WATCH ITEMS  {await db.scalar('SELECT COUNT(*) FROM watch') or 0}",
        SUB,
        "/broadcast <text>  message all users",
    ]
    await respond(update, pre(lines), admin_kb())


@admin_only
async def cmd_broadcast(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    raw = (update.effective_message.text or "") if update.effective_message else ""
    text = raw.strip().partition(" ")[2].strip()
    if not text:
        await respond(update, pre(["USAGE: /broadcast <text>", "Sends the text to every user of the bot."]),
                      admin_kb())
        return
    users = await Ctx.db.q("SELECT user_id FROM users")
    sent = failed = 0
    for u in users:
        try:
            await context.bot.send_message(u["user_id"], f"<code>[BROADCAST]</code> {esc(text)}", parse_mode=ParseMode.HTML,
                                           link_preview_options=NO_PREVIEW)
            sent += 1
        except RetryAfter as exc:
            await asyncio.sleep(float(getattr(exc, "retry_after", 5) or 5) + 1)
            failed += 1
        except TelegramError:
            failed += 1
        await asyncio.sleep(0.05)
    ev("broadcast", sent=sent, failed=failed,
       admin=update.effective_user.id if update.effective_user else None)
    await respond(update, pre(header("BROADCAST") + [f"SENT    {sent}", f"FAILED  {failed}",
                                                     "(failed = user blocked the bot)"]), admin_kb())


COMMANDS: dict[str, Any] = {
    "start": cmd_start, "menu": cmd_start, "console": cmd_console, "help": cmd_help, "about": cmd_about, "lang": cmd_lang,
    "settings": cmd_settings, "last24": cmd_last24, "live": cmd_live, "around": cmd_around,
    "world": cmd_world, "near": cmd_near, "search": cmd_search, "flight": cmd_flight,
    "airlines": cmd_airlines, "aircraft": cmd_aircraft, "stats": cmd_stats, "archive": cmd_archive,
    "alerts": cmd_alerts, "watch": cmd_watch, "unwatch": cmd_unwatch, "watchlist": cmd_watchlist,
    "status": cmd_status,
    "admin": cmd_admin, "system": cmd_system, "sync": cmd_sync, "database": cmd_database,
    "export": cmd_export, "restart_info": cmd_restart_info, "users": cmd_users,
    "broadcast": cmd_broadcast,
}

# (command, English description, Arabic description) shown in Telegram's command menu
MENU_COMMANDS = [
    ("start", "Main menu", "القائمة الرئيسية"),
    ("console", "Open the web console", "فتح الواجهة"),
    ("live", "Aircraft over Iraq now", "الطائرات فوق العراق الآن"),
    ("around", "Aircraft around Iraq", "الطائرات حول العراق"),
    ("last24", "Iraq flights, last 24 hours", "رحلات العراق خلال 24 ساعة"),
    ("world", "Find any aircraft worldwide", "إيجاد أي طائرة في العالم"),
    ("near", "Aircraft near a point: /near lat lon", "الطائرات قرب نقطة: ‎/near lat lon"),
    ("search", "Search the archive", "البحث في الأرشيف"),
    ("flight", "Open a flight by callsign", "فتح رحلة برمز النداء"),
    ("archive", "Flight archive", "أرشيف الرحلات"),
    ("stats", "Statistics", "الإحصائيات"),
    ("alerts", "Emergency squawks", "نداءات الطوارئ"),
    ("watchlist", "My watchlist", "قائمة المتابعة"),
    ("settings", "Language and alerts", "اللغة والتنبيهات"),
    ("lang", "Change language", "تغيير اللغة"),
    ("status", "System status", "حالة النظام"),
    ("about", "About and credits", "حول البوت"),
    ("help", "Help", "المساعدة"),
]


# --------------------------------------------------------------------------
# PUSH NOTIFICATIONS (watchlist hits and emergency squawks)
# --------------------------------------------------------------------------
async def send_notifications(bot: Any) -> None:
    """Called after every sync. Each (user, flight, kind) is notified at most once."""
    db = Ctx.db
    cut = iso(now_utc() - timedelta(minutes=20))
    sent = 0

    async def push(user_id: int, lang: str, text: str, flight_id: int, kind: str) -> None:
        nonlocal sent
        # Record first, so a delivery failure can never turn into repeated messages.
        await db.run("INSERT OR IGNORE INTO notified(user_id, flight_id, kind) VALUES(?,?,?)",
                     (user_id, flight_id, kind))
        try:
            await bot.send_message(
                user_id, text, parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[btn(tr(lang, "b_open"), f"F|{flight_id}")]]))
            sent += 1
        except Forbidden:
            await db.run("UPDATE users SET alerts=0 WHERE user_id=?", (user_id,))   # bot was blocked
        except TelegramError as exc:
            log.warning("notification not delivered: %s", type(exc).__name__)
        await asyncio.sleep(0.05)

    hits = await db.q(
        "SELECT w.user_id, w.ident, f.id, COALESCE(u.lang, 'en') AS lang FROM watch w "
        "JOIN flights f ON (f.callsign=w.ident OR f.registration=w.ident OR f.mode_s=w.ident) "
        "LEFT JOIN users u ON u.user_id=w.user_id "
        f"WHERE f.{IRAQ_ZONE} AND f.last_seen_utc>=? AND NOT EXISTS ("
        "SELECT 1 FROM notified n WHERE n.user_id=w.user_id AND n.flight_id=f.id AND n.kind='watch') "
        "LIMIT 100", (cut,))
    for h in hits:
        await push(h["user_id"], h["lang"], tr(h["lang"], "wl_push", x=esc(h["ident"])), h["id"], "watch")

    emergencies = await db.q(
        f"SELECT * FROM flights WHERE {EM_SQL} AND {REGION_ZONE} AND last_seen_utc>=? LIMIT 10", (cut,))
    if emergencies:
        subscribers = await db.q("SELECT user_id, lang FROM users WHERE alerts=1")
        for f in emergencies:
            for u in subscribers:
                if sent >= 200:
                    break
                if await db.scalar("SELECT 1 FROM notified WHERE user_id=? AND flight_id=? AND kind='em'",
                                   (u["user_id"], f["id"])):
                    continue
                lang = u["lang"]
                where = tr(lang, "al_in" if f["crossing_status"] != "NEARBY" else "al_near")
                if f["latitude"] is not None:
                    where += f" · {nearest_city(lang, f['latitude'], f['longitude'])}"
                text = tr(lang, "al_push", sq=esc(f["squawk"]), mean=tr(lang, "sq_" + f["squawk"]),
                          id=esc(ident(f)), type=esc(f["aircraft_type"] or ""), where=esc(where))
                await push(u["user_id"], lang, text, f["id"], "em")
    if sent:
        ev("notifications", sent=sent)
    await db.run("DELETE FROM notified WHERE flight_id NOT IN (SELECT id FROM flights)")


# --------------------------------------------------------------------------
# CALLBACK ROUTER / ERROR HANDLER
# --------------------------------------------------------------------------
async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query or not query.data:
        return
    lang = lg(context)
    user = update.effective_user
    uid = user.id if user else 0
    parts = query.data.split("|")
    head_ = parts[0]

    async def answer(text: Optional[str] = None, alert: bool = False) -> None:
        try:
            await query.answer(text, show_alert=alert)
        except TelegramError:
            pass

    try:
        if head_ == "LG":
            await answer(tr(parts[1], "lang_set"))
            await set_language(update, context, parts[1])
        elif head_ == "J":
            await answer(tr(lang, "join_ok"))
            await view_main(update, context)
        elif head_ == "P":
            pos = await Ctx.db.one("SELECT latitude, longitude FROM flights WHERE id=?", (int(parts[1]),))
            if pos and pos["latitude"] is not None and update.effective_chat:
                await context.bot.send_location(update.effective_chat.id, pos["latitude"], pos["longitude"])
                await answer(tr(lang, "pin_sent"))
            else:
                await answer(tr(lang, "pin_none"), True)
        elif head_ == "WA":
            flight_id = int(parts[1])
            r = await Ctx.db.one("SELECT callsign, registration, mode_s FROM flights WHERE id=?", (flight_id,))
            target = (r["callsign"] or r["registration"] or r["mode_s"]) if r else None
            if not target:
                await answer(tr(lang, "not_found"), True)
            elif await Ctx.db.scalar("SELECT 1 FROM watch WHERE user_id=? AND ident=?", (uid, target)):
                await Ctx.db.run("DELETE FROM watch WHERE user_id=? AND ident=?", (uid, target))
                await answer(tr(lang, "wl_removed", x=target))
                await view_flight(update, context, flight_id)
            else:
                message = await watch_add(update, context, target)
                await answer(message, message != tr(lang, "wl_added", x=target))
                await view_flight(update, context, flight_id)
        elif head_ == "WR":
            await Ctx.db.run("DELETE FROM watch WHERE user_id=? AND ident=?", (uid, parts[1]))
            await answer()
            await view_watchlist(update, context, tr(lang, "wl_removed", x=parts[1]))
        elif head_ == "ST":
            await Ctx.db.run("UPDATE users SET alerts=1-alerts WHERE user_id=?", (uid,))
            await answer()
            await view_settings(update, context)
        else:
            await answer()
            if head_ == "M":
                target = parts[1]
                context.user_data.pop("await", None)
                if target == "main":
                    await view_main(update, context)
                elif target == "search":
                    await prompt_search(update, context)
                elif target == "world":
                    await prompt_world(update, context)
                elif target == "archive":
                    await view_archive_menu(update, context)
                elif target == "status":
                    await view_status(update, context)
                elif target == "help":
                    await view_help(update, context)
                elif target == "about":
                    await view_about(update, context)
                elif target == "settings":
                    await view_settings(update, context)
                elif target == "lang":
                    await view_lang(update, context)
                elif target == "alerts":
                    await view_list(update, context, "em", "-", 0)
                elif target == "watch":
                    await view_watchlist(update, context)
                elif target == "watchadd":
                    await prompt_watch(update, context)
                elif target == "range":
                    context.user_data["await"] = "range"
                    await respond(update, "\n".join([
                        head("ARC", tr(lang, "b_custom")), esc(tr(lang, "ar_range")),
                        "<code>2026-11-01 2026-11-10</code>",
                        note(lang, tr(lang, "tz_note", tz=Ctx.cfg.tz_name))]),
                        InlineKeyboardMarkup([menu_row(lang)]))
                else:
                    await view_main(update, context)
            elif head_ == "L":
                await view_list(update, context, parts[1], parts[2], int(parts[3]))
            elif head_ == "F":
                await view_flight(update, context, int(parts[1]))
            elif head_ == "WU":
                await world_update(update, context, int(parts[1]))
            elif head_ == "W":
                await run_world(update, context, context.user_data.get("query") or "")
            elif head_ == "T":
                await view_track(update, context, int(parts[1]), int(parts[2]))
            elif head_ == "A":
                await view_aircraft_info(update, context, int(parts[1]))
            elif head_ in ("AL", "AC"):
                await view_group(update, context, head_, int(parts[1]))
            elif head_ == "S":
                await view_stats(update, context, int(parts[1]))
            elif head_ in ("X", "AD"):
                if not is_admin(update):
                    await deny(update)
                elif head_ == "X":
                    await admin_export(update, int(parts[1]))
                elif parts[1] == "system":
                    await admin_system(update)
                elif parts[1] == "database":
                    await admin_database(update)
                elif parts[1] == "sync":
                    await admin_sync(update)
                elif parts[1] == "synclog":
                    await admin_synclog(update)
                elif parts[1] == "restart":
                    await admin_restart_info(update)
                elif parts[1] == "users":
                    await admin_users(update)
            else:
                await view_main(update, context)
    except (ValueError, IndexError):
        await view_main(update, context)


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    err = context.error
    if isinstance(err, RetryAfter):
        log.warning("telegram flood control", extra={"data": {"retry_after": str(err.retry_after)}})
        return
    if isinstance(err, Conflict):
        log.error("telegram conflict: another instance is polling with this bot token")
        return
    log.error("handler error", exc_info=err)
    if isinstance(update, Update) and update.effective_chat and not isinstance(err, TelegramError):
        try:
            lang = (context.user_data or {}).get("lang") or "en"
            key = "err_db" if isinstance(err, (sqlite3.Error, aiosqlite.Error)) else "err_int"
            await context.bot.send_message(update.effective_chat.id, esc(tr(lang, key)),
                                           parse_mode=ParseMode.HTML)
        except Exception:
            pass


# --------------------------------------------------------------------------
# MINI APP: WEB SERVER AND JSON API
# --------------------------------------------------------------------------
# The Mini App is one HTML page (WEBAPP_HTML, end of this file) served by the
# same process as the bot.  Every /api request carries Telegram.WebApp.initData
# in the X-Init-Data header; it is verified with the bot token before anything
# is read, and the same channel-subscription rule as the bot is applied.
# Validation: https://core.telegram.org/bots/webapps#validating-data-received-via-the-mini-app
#   secret_key = HMAC_SHA256(key="WebAppData", msg=bot_token)
#   hash       = hex(HMAC_SHA256(key=secret_key, msg=data_check_string))
#   data_check_string = "key=value" pairs except hash, sorted by key, joined by "\n"
INIT_DATA_MAX_AGE = 24 * 3600
WEB_RATE = (40, 10.0)          # at most 40 API requests per 10 s per user
WEB_SECURITY_HEADERS = {
    "X-Content-Type-Options": "nosniff",
    "Referrer-Policy": "no-referrer",
    "Content-Security-Policy": (
        "default-src 'self'; script-src 'self' 'unsafe-inline' https://telegram.org; "
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
        "font-src https://fonts.gstatic.com; img-src 'self' data:; connect-src 'self'; "
        "frame-ancestors 'self' https://web.telegram.org https://*.telegram.org"),
}


def verify_init_data(raw: str, bot_token: str, now: Optional[float] = None) -> Optional[dict]:
    """Return the parsed init data if its signature is valid and fresh, else None."""
    if not raw or len(raw) > 8192:
        return None
    try:
        pairs = urllib.parse.parse_qsl(raw, keep_blank_values=True, strict_parsing=True)
    except ValueError:
        return None
    data = dict(pairs)
    received = data.get("hash", "")
    if not re.fullmatch(r"[0-9a-f]{64}", received):
        return None
    secret = hmac.new(b"WebAppData", bot_token.encode(), hashlib.sha256).digest()

    def digest(exclude: set[str]) -> str:
        check = "\n".join(f"{k}={v}" for k, v in sorted(data.items()) if k not in exclude)
        return hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()

    # Newer clients also send a "signature" field (for third-party validation). Telegram's
    # page and client libraries disagree on whether it is part of the string, so both
    # forms are accepted; each is still an HMAC keyed with the bot token.
    if not (hmac.compare_digest(digest({"hash"}), received)
            or hmac.compare_digest(digest({"hash", "signature"}), received)):
        return None
    try:
        auth_date = int(data.get("auth_date", "0"))
    except ValueError:
        return None
    if abs((now or time.time()) - auth_date) > INIT_DATA_MAX_AGE:
        return None
    try:
        user = json.loads(data.get("user", "{}"))
    except ValueError:
        return None
    if not isinstance(user, dict) or not isinstance(user.get("id"), int):
        return None
    data["user"] = user
    return data


def jrow(row: Optional[sqlite3.Row], keys: Optional[list[str]] = None) -> Optional[dict]:
    if row is None:
        return None
    return {k: row[k] for k in (keys or row.keys())}


STATUS_CODE = {"CONFIRMED": "CNF", "SINGLE_OBS": "1OB", "NEARBY": "PRM", "WORLD": "GLB"}


def target_brief(r: sqlite3.Row) -> dict:
    return {
        "id": r["id"], "cs": ident(r), "reg": r["registration"], "hex": r["mode_s"],
        "type": r["aircraft_type"], "st": STATUS_CODE.get(r["crossing_status"], "1OB"),
        "lat": r["latitude"], "lon": r["longitude"], "alt": r["altitude_ft"],
        "gs": r["ground_speed_kt"], "hdg": r["heading"], "vr": r["vertical_rate"],
        "sq": r["squawk"], "emg": is_emergency(r),
        "dep": r["dep_iata"] or r["dep_icao"], "arr": r["arr_iata"] or r["arr_icao"],
        "op": r["airline_name"] or r["airline_icao"], "seen": r["last_seen_utc"],
    }


class WebApi:
    def __init__(self, cfg: Config, bot: Any) -> None:
        self.cfg, self.bot = cfg, bot
        self.member_cache: dict[int, dict] = {}
        self.hits: dict[int, list[float]] = {}
        self.runner: Optional[web.AppRunner] = None

    # ---------------------------------------------------------------- plumbing
    def build(self) -> web.Application:
        app = web.Application(middlewares=[self.middleware], client_max_size=64 * 1024)
        app.router.add_get("/", self.index)
        app.router.add_get("/healthz", self.health)
        app.router.add_get("/api/bootstrap", self.bootstrap)
        app.router.add_get("/api/live", self.live)
        app.router.add_get("/api/flight/{id:[0-9]{1,9}}", self.flight)
        app.router.add_get("/api/stats", self.stats)
        app.router.add_get("/api/system", self.system)
        app.router.add_get("/api/search", self.search)
        app.router.add_post("/api/watch", self.watch)
        return app

    async def start(self) -> None:
        self.runner = web.AppRunner(self.build(), access_log=None)
        await self.runner.setup()
        site = web.TCPSite(self.runner, host="0.0.0.0", port=self.cfg.port)
        await site.start()
        ev("mini app online", port=self.cfg.port, url=self.cfg.webapp_url)

    async def stop(self) -> None:
        if self.runner:
            await self.runner.cleanup()

    @web.middleware
    async def middleware(self, request: web.Request, handler: Any) -> web.StreamResponse:
        if request.path.startswith("/api/"):
            auth = verify_init_data(request.headers.get("X-Init-Data", ""), self.cfg.bot_token)
            if auth is None:
                return self.error(401, "auth")
            uid = auth["user"]["id"]
            stamps = [t for t in self.hits.get(uid, []) if time.monotonic() - t < WEB_RATE[1]]
            if len(stamps) >= WEB_RATE[0]:
                return self.error(429, "rate")
            stamps.append(time.monotonic())
            self.hits[uid] = stamps
            if not await member_ok(self.bot, uid, self.member_cache.setdefault(uid, {})):
                resp = self.error(403, "subscribe")
                resp.text = json.dumps({"error": "subscribe", "channel": self.cfg.channel})
                return resp
            request["uid"] = uid
            request["tg_user"] = auth["user"]
            request["lang"] = await self.user_lang(uid, auth["user"])
        try:
            resp = await handler(request)
        except web.HTTPException as exc:
            resp = exc
        except Exception:
            log.exception("mini app request failed", extra={"data": {"path": request.path}})
            resp = self.error(500, "internal")
        for key, value in WEB_SECURITY_HEADERS.items():
            resp.headers.setdefault(key, value)
        return resp

    @staticmethod
    def error(status: int, code: str) -> web.Response:
        return web.json_response({"error": code}, status=status)

    @staticmethod
    def ok(payload: Any) -> web.Response:
        return web.json_response(payload, headers={"Cache-Control": "no-store"},
                                 dumps=lambda o: json.dumps(o, ensure_ascii=False, default=str))

    async def user_lang(self, uid: int, tg_user: dict) -> str:
        saved = await Ctx.db.scalar("SELECT lang FROM users WHERE user_id=?", (uid,))
        if saved in ("ar", "en"):
            return saved
        lang = "ar" if str(tg_user.get("language_code") or "").lower().startswith("ar") else "en"
        stamp = iso(now_utc())
        await Ctx.db.run(
            "INSERT OR IGNORE INTO users(user_id, username, lang, first_seen_utc, last_seen_utc) "
            "VALUES(?,?,?,?,?)", (uid, clean_str(tg_user.get("username")), lang, stamp, stamp))
        return lang

    # ---------------------------------------------------------------- pages
    async def index(self, request: web.Request) -> web.Response:
        return web.Response(text=WEBAPP_HTML, content_type="text/html", charset="utf-8",
                            headers={"Cache-Control": "no-cache"})

    async def health(self, request: web.Request) -> web.Response:
        return web.json_response({"ok": True, "version": APP_VERSION})

    async def bootstrap(self, request: web.Request) -> web.Response:
        cfg = self.cfg
        return self.ok({
            "version": APP_VERSION, "lang": request["lang"], "admin": request["uid"] in cfg.admin_ids,
            "tz": cfg.tz_name, "interval": cfg.sync_interval, "channel": cfg.channel,
            "dev": cfg.dev_username,
            "border": [[lat, lon] for lon, lat in IRAQ_POLYGON],
            "cities": [{"en": c[0], "ar": c[1], "lat": c[2], "lon": c[3]} for c in IRAQ_CITIES],
            "circles": [[lat, lon] for lat, lon in QUERY_CIRCLES], "radius_nm": QUERY_RADIUS_NM,
            "sources": [PROVIDERS[p][0] for p in cfg.providers],
        })

    async def live(self, request: web.Request) -> web.Response:
        db = Ctx.db
        cut = live_cut()
        rows = await db.q(
            f"SELECT * FROM flights WHERE last_seen_utc>=? AND {REGION_ZONE} "
            "AND latitude IS NOT NULL ORDER BY last_seen_utc DESC LIMIT 400", (cut,))
        ids = [r["id"] for r in rows]
        trails: dict[int, list] = {}
        if ids:
            marks = ",".join("?" * len(ids))
            for o in await db.q(
                    f"SELECT flight_id, ts_utc, latitude, longitude FROM track_observations "
                    f"WHERE flight_id IN ({marks}) AND ts_utc>=? ORDER BY ts_utc",
                    (*ids, iso(now_utc() - timedelta(minutes=40)))):
                trails.setdefault(o["flight_id"], []).append([round(o["latitude"], 4), round(o["longitude"], 4)])
        last = await db.one("SELECT finished_utc, status FROM sync_history ORDER BY id DESC LIMIT 1")
        last_ok = await db.scalar("SELECT MAX(finished_utc) FROM sync_history WHERE status='OK'")
        targets = []
        for r in rows:
            item = target_brief(r)
            item["trail"] = trails.get(r["id"], [])[-12:]
            targets.append(item)
        return self.ok({
            "now": iso(now_utc()), "last_ok": last_ok, "last_status": last["status"] if last else None,
            "interval": self.cfg.sync_interval,
            "sources": [x.strip() for x in (await db.get_status("provider") or "").split(",") if x.strip()],
            "targets": targets,
        })

    async def flight(self, request: web.Request) -> web.Response:
        lang = request["lang"]
        flight_id = int(request.match_info["id"])
        await quick_enrich(flight_id)
        db = Ctx.db
        r = await db.one("SELECT * FROM flights WHERE id=?", (flight_id,))
        if not r:
            return self.error(404, "not_found")
        key = r["registration"] or r["mode_s"]
        ac = await db.one("SELECT * FROM aircraft WHERE key=?", (key,)) if key else None
        track = [[o["ts_utc"], o["latitude"], o["longitude"], o["altitude_ft"], o["ground_speed_kt"],
                  o["heading"], o["in_iraq"]]
                 for o in await db.q(
                     "SELECT * FROM track_observations WHERE flight_id=? ORDER BY ts_utc DESC LIMIT 500",
                     (flight_id,))][::-1]
        progress = None
        if None not in (r["dep_lat"], r["dep_lon"], r["arr_lat"], r["arr_lon"], r["latitude"], r["longitude"]):
            flown = dist_nm(r["dep_lat"], r["dep_lon"], r["latitude"], r["longitude"])
            remaining = dist_nm(r["latitude"], r["longitude"], r["arr_lat"], r["arr_lon"])
            if flown + remaining >= 20:
                eta = None
                seen = parse_dt(r["last_seen_utc"])
                if r["ground_speed_kt"] and r["ground_speed_kt"] > 80 and seen and \
                        (now_utc() - seen).total_seconds() < 1800:
                    eta = iso(seen + timedelta(hours=remaining / r["ground_speed_kt"]))
                progress = {"flown": round(flown), "remaining": round(remaining),
                            "pct": round(100 * flown / (flown + remaining)), "eta": eta,
                            "dep": [r["dep_lat"], r["dep_lon"]], "arr": [r["arr_lat"], r["arr_lon"]]}
        recent = [{"id": f["id"], "cs": ident(f), "st": STATUS_CODE.get(f["crossing_status"], "1OB"),
                   "route": route(f), "seen": f["last_seen_utc"]}
                  for f in await db.q(
                      "SELECT * FROM flights WHERE (registration=? OR mode_s=?) AND id<>? "
                      "ORDER BY last_seen_utc DESC LIMIT 8",
                      (r["registration"] or "-", r["mode_s"] or "-", flight_id))]
        watch_id = r["callsign"] or r["registration"] or r["mode_s"]
        watching = bool(watch_id and await db.scalar(
            "SELECT 1 FROM watch WHERE user_id=? AND ident=?", (request["uid"], watch_id)))
        cat = CATEGORIES.get((r["category"] or "").upper())
        out = {k: r[k] for k in (
            "id", "callsign", "flight_number_iata", "airline_icao", "airline_name", "aircraft_type",
            "aircraft_type_desc", "registration", "mode_s", "dep_icao", "dep_iata", "dep_name", "dep_city",
            "dep_country", "arr_icao", "arr_iata", "arr_name", "arr_city", "arr_country", "route_source",
            "route_checked_utc", "first_seen_utc", "last_seen_utc", "obs_count", "altitude_ft", "alt_geom_ft",
            "ground_speed_kt", "heading", "vertical_rate", "squawk", "mach", "ias_kt", "tas_kt",
            "nav_altitude_ft", "nav_heading", "wind_dir", "wind_kt", "oat_c", "latitude", "longitude",
            "category", "aircraft_classes", "origin_country", "data_source", "updated_utc")}
        out.update({
            "cs": ident(r), "st": STATUS_CODE.get(r["crossing_status"], "1OB"), "emg": is_emergency(r),
            "status_text": pick(lang, STATUS_TXT.get(r["crossing_status"], STATUS_TXT["SINGLE_OBS"])),
            "traffic": (pick(lang, TRAFFIC.get(r["traffic_type"], TRAFFIC["UNKNOWN"]))
                        if r["route_source"] and r["crossing_status"] in ("CONFIRMED", "SINGLE_OBS") else None),
            "category_text": pick(lang, cat) if cat else None,
            "pos_source": POS_SOURCES.get(r["pos_source"] or "", r["pos_source"]),
            "near": (nearest_city(lang, r["latitude"], r["longitude"])
                     if r["latitude"] is not None and r["crossing_status"] != "WORLD" else None),
            "compass": compass(lang, r["heading"]) if r["heading"] is not None else None,
            "squawk_text": (tr(lang, {"7500": "sq_7500", "7600": "sq_7600", "7700": "sq_7700",
                                      "1200": "sq_vfr", "7000": "sq_vfr"}[r["squawk"]])
                            if r["squawk"] in ("7500", "7600", "7700", "1200", "7000") else None),
            "aircraft": jrow(ac, ["registration", "mode_s", "type_icao", "type_desc", "manufacturer",
                                  "operator_name", "owner_country", "photo_url", "first_seen_utc",
                                  "last_seen_utc"]) if ac else None,
            "progress": progress, "track": track, "recent": recent, "watching": watching,
        })
        return self.ok(out)

    async def stats(self, request: web.Request) -> web.Response:
        db = Ctx.db
        try:
            days = max(0, min(365, int(request.query.get("days", "1"))))
        except ValueError:
            days = 1
        since = iso(now_utc() - timedelta(days=days)) if days else "0000"
        base = "last_seen_utc>=? AND crossing_status='CONFIRMED'"
        args = (since,)
        total = await db.scalar(f"SELECT COUNT(*) FROM flights WHERE {base}", args) or 0
        single = await db.scalar(
            "SELECT COUNT(*) FROM flights WHERE last_seen_utc>=? AND crossing_status='SINGLE_OBS'", args) or 0
        agg = await db.one(
            f"SELECT COUNT(DISTINCT airline_icao) a, COUNT(DISTINCT aircraft_type) t, COUNT(airline_icao) ha, "
            f"COUNT(aircraft_type) ht, COUNT(dep_icao) hd FROM flights WHERE {base}", args)

        async def top(col: str, name_col: str) -> list:
            return [{"code": x["c"], "name": x["nm"], "n": x["n"]} for x in await db.q(
                f"SELECT {col} c, MAX({name_col}) nm, COUNT(*) n FROM flights WHERE {base} "
                f"AND {col} IS NOT NULL GROUP BY c ORDER BY n DESC LIMIT 8", args)]

        hours = [0] * 24
        for f in await db.q(f"SELECT first_seen_utc FROM flights WHERE {base}", args):
            dt = parse_dt(f[0])
            if dt:
                hours[dt.astimezone(self.cfg.tz).hour] += 1
        mix = [{"code": k["k"], "label": pick(request["lang"], TRAFFIC.get(k["k"], TRAFFIC["UNKNOWN"])),
                "n": k["n"]} for k in await db.q(
            f"SELECT traffic_type k, COUNT(*) n FROM flights WHERE {base} GROUP BY k ORDER BY n DESC", args)]
        avg = await db.one(
            "SELECT AVG(o.altitude_ft) alt, AVG(o.ground_speed_kt) gs, COUNT(o.altitude_ft) n "
            "FROM track_observations o JOIN flights f ON f.id=o.flight_id "
            "WHERE f.last_seen_utc>=? AND f.crossing_status='CONFIRMED' AND o.in_iraq=1", args)
        coverage = await db.scalar(f"SELECT MIN(first_seen_utc) FROM flights WHERE {IRAQ_ZONE}")
        return self.ok({
            "days": days, "confirmed": total, "single": single,
            "airlines": agg["a"], "types": agg["t"],
            "complete": {"airline": agg["ha"], "type": agg["ht"], "route": agg["hd"]},
            "top_airlines": await top("airline_icao", "airline_name"),
            "top_types": await top("aircraft_type", "aircraft_type_desc"),
            "top_dep": await top("dep_icao", "dep_city"), "top_arr": await top("arr_icao", "arr_city"),
            "hours": hours, "mix": mix, "avg_alt": avg["alt"], "avg_gs": avg["gs"], "avg_n": avg["n"],
            "coverage": coverage,
        })

    async def system(self, request: web.Request) -> web.Response:
        db = Ctx.db
        rows = await db.q("SELECT * FROM sync_history ORDER BY id DESC LIMIT 14")
        last = rows[0] if rows else None
        up = now_utc() - Ctx.started
        out = {
            "version": APP_VERSION, "uptime_s": int(up.total_seconds()), "interval": self.cfg.sync_interval,
            "next": iso(Ctx.sync.next_run) if Ctx.sync.next_run else None,
            "feed": await db.get_status("live_access"),
            "sources": [x.strip() for x in (await db.get_status("provider") or "").split(",") if x.strip()],
            "feeds": [p.strip() for p in (last["detail"] or "").split(";") if p.strip()] if last else [],
            "log": [{"t": x["started_utc"], "status": x["status"], "recv": x["received"],
                     "iraq": x["in_iraq"], "around": max(0, x["inserted"] + x["updated"] - x["in_iraq"])}
                    for x in rows],
            "flights": await db.scalar(f"SELECT COUNT(*) FROM flights WHERE {IRAQ_ZONE}") or 0,
            "points": await db.scalar("SELECT COUNT(*) FROM track_observations") or 0,
        }
        if request["uid"] in self.cfg.admin_ids:
            out["admin"] = {
                "users": await db.scalar("SELECT COUNT(*) FROM users") or 0,
                "sub_check": "FAILING" if Ctx.sub_error else "OK",
                "lookups": Ctx.enrich.lookups, "lookup_error": Ctx.enrich.last_error,
            }
        return self.ok(out)

    async def search(self, request: web.Request) -> web.Response:
        query = (request.query.get("q") or "").strip()[:40]
        if len(query) < 2:
            return self.ok({"q": query, "results": []})
        pattern = f"%{like_escape(query.upper())}%"
        where = " OR ".join(f"UPPER({c}) LIKE ? ESCAPE '\\'" for c in SEARCH_COLS)
        rows = await Ctx.db.q(
            f"SELECT * FROM flights WHERE ({where}) ORDER BY last_seen_utc DESC LIMIT 60",
            tuple([pattern] * len(SEARCH_COLS)))
        return self.ok({"q": query, "results": [target_brief(r) for r in rows]})

    async def watch(self, request: web.Request) -> web.Response:
        try:
            body = await request.json()
            flight_id = int(body.get("id"))
        except Exception:
            return self.error(400, "bad_request")
        r = await Ctx.db.one("SELECT callsign, registration, mode_s FROM flights WHERE id=?", (flight_id,))
        target = (r["callsign"] or r["registration"] or r["mode_s"]) if r else None
        if not target:
            return self.error(404, "not_found")
        uid = request["uid"]
        if await Ctx.db.scalar("SELECT 1 FROM watch WHERE user_id=? AND ident=?", (uid, target)):
            await Ctx.db.run("DELETE FROM watch WHERE user_id=? AND ident=?", (uid, target))
            return self.ok({"watching": False, "ident": target})
        count = await Ctx.db.scalar("SELECT COUNT(*) FROM watch WHERE user_id=?", (uid,)) or 0
        if count >= WATCH_LIMIT:
            return self.error(409, "watch_full")
        await Ctx.db.run("INSERT OR IGNORE INTO watch(user_id, ident, created_utc) VALUES(?,?,?)",
                         (uid, target, iso(now_utc())))
        return self.ok({"watching": True, "ident": target})


# --------------------------------------------------------------------------
# PROCESS LIFECYCLE
# --------------------------------------------------------------------------
async def acquire_instance_lock(path: str, wait_seconds: int = 90):
    """Exclusive lock on the volume so two processes never share the database
    or poll Telegram at the same time (waits out a redeploy overlap)."""
    handle = open(path, "w")
    deadline = time.monotonic() + wait_seconds
    while True:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            handle.write(str(os.getpid()))
            handle.flush()
            return handle
        except OSError:
            if time.monotonic() > deadline:
                handle.close()
                raise ConfigError(
                    "Another instance holds the instance lock. Run exactly one replica.")
            await asyncio.sleep(3)


async def heartbeat(stop: asyncio.Event) -> None:
    while not stop.is_set():
        try:
            await asyncio.wait_for(stop.wait(), timeout=600)
        except asyncio.TimeoutError:
            try:
                flights = await Ctx.db.scalar("SELECT COUNT(*) FROM flights")
                ev("health", status="alive", flights=flights,
                   uptime_s=int((now_utc() - Ctx.started).total_seconds()),
                   feed_last_error=Ctx.api.last_error)
            except Exception:
                log.exception("health check failed")


async def amain() -> int:
    setup_logging()
    try:
        cfg = Config()
        cfg.check_storage()
    except ConfigError as exc:
        log.critical("CONFIGURATION ERROR: %s", exc)
        return 2

    stop = asyncio.Event()
    reason = {"text": "unknown"}
    loop = asyncio.get_running_loop()

    def request_stop(name: str) -> None:
        reason["text"] = name
        stop.set()

    for sig in (signal.SIGTERM, signal.SIGINT):
        loop.add_signal_handler(sig, request_stop, sig.name)

    try:
        lock_handle = await acquire_instance_lock(cfg.db_path + ".lock")
    except ConfigError as exc:
        log.critical("CONFIGURATION ERROR: %s", exc)
        return 2

    db = Database(cfg.db_path)
    try:
        await db.open()
    except Exception as exc:
        log.critical("DATABASE ERROR: cannot open %s: %s", cfg.db_path, exc)
        return 2

    api = AdsbClient(cfg.providers)
    enricher = Enricher(db)
    sync = SyncService(cfg, db, api)
    sync.stop = stop
    sync.enricher = enricher
    Ctx.enrich = enricher
    Ctx.cfg, Ctx.db, Ctx.api, Ctx.sync, Ctx.started = cfg, db, api, sync, now_utc()
    run_id = await db.run("INSERT INTO runs(started_utc, deployment) VALUES(?,?)",
                          (iso(Ctx.started), os.getenv("RAILWAY_DEPLOYMENT_ID")))

    # concurrent_updates: one user's slow lookup never blocks the other users.
    app = Application.builder().token(cfg.bot_token).concurrent_updates(16).build()
    # The gate runs first for every update: language question and channel subscription.
    app.add_handler(TypeHandler(Update, gate), group=-1)
    sync.after_sync = lambda: send_notifications(app.bot)
    webapi = WebApi(cfg, app.bot)
    for name, handler in COMMANDS.items():
        app.add_handler(CommandHandler(name, handler))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_handler(MessageHandler(filters.LOCATION, on_location))
    app.add_error_handler(on_error)

    def polling_error(exc: TelegramError) -> None:
        if isinstance(exc, Conflict):
            log.error("telegram conflict: another process is polling this bot token")
        else:
            log.warning("telegram polling error: %s", type(exc).__name__)

    exit_code = 0
    tasks: list[asyncio.Task] = []
    try:
        await app.initialize()
        await app.start()
        try:
            await app.bot.set_my_commands([BotCommand(c, en) for c, en, _ in MENU_COMMANDS])
            await app.bot.set_my_commands([BotCommand(c, ar) for c, _, ar in MENU_COMMANDS],
                                          language_code="ar")
        except TelegramError as exc:
            log.warning("could not register bot commands: %s", type(exc).__name__)
        await app.updater.start_polling(
            allowed_updates=[Update.MESSAGE, Update.CALLBACK_QUERY], error_callback=polling_error)
        if cfg.webapp_enabled:
            try:
                await webapi.start()
            except OSError as exc:
                log.error("mini app could not listen on port %s: %s", cfg.port, exc)
            if cfg.webapp_url:
                try:
                    await app.bot.set_chat_menu_button(menu_button=MenuButtonWebApp(
                        "CONSOLE", WebAppInfo(cfg.webapp_url)))
                except TelegramError as exc:
                    log.warning("could not set the console menu button: %s", type(exc).__name__)
            else:
                log.warning("mini app has no public URL: generate a Railway domain or set WEBAPP_URL; "
                            "the console button is hidden until then")
        ev("bot online", admins=len(cfg.admin_ids), db=cfg.db_path, tz=cfg.tz_name,
           interval=cfg.sync_interval, force_sub=cfg.force_sub, channel=cfg.channel)
        tasks = [asyncio.create_task(sync.run_forever(), name="sync"),
                 asyncio.create_task(heartbeat(stop), name="heartbeat")]
        await stop.wait()
        ev("shutdown requested", reason=reason["text"])
    except Exception as exc:
        log.critical("fatal error: %s", exc, exc_info=True)
        reason["text"] = f"fatal: {type(exc).__name__}"
        exit_code = 1
    finally:
        stop.set()
        for task in tasks:
            try:
                await asyncio.wait_for(task, timeout=20)
            except Exception:
                task.cancel()
        for step in (lambda: app.updater.stop() if app.updater and app.updater.running else None,
                     lambda: app.stop() if app.running else None,
                     webapi.stop, app.shutdown, api.close, enricher.close):
            try:
                result = step()
                if asyncio.iscoroutine(result):
                    await result
            except Exception:
                log.exception("error during shutdown step")
        try:
            await db.run("UPDATE runs SET stopped_utc=?, stop_reason=? WHERE id=?",
                         (iso(now_utc()), reason["text"], run_id))
        except Exception:
            pass
        await db.close()
        try:
            fcntl.flock(lock_handle, fcntl.LOCK_UN)
            lock_handle.close()
        except Exception:
            pass
        ev("shutdown complete", exit_code=exit_code)
    return exit_code



# --------------------------------------------------------------------------
# MINI APP PAGE (served at /).  Plain HTML, CSS and JavaScript, no build step.
# --------------------------------------------------------------------------
WEBAPP_HTML = r"""<!doctype html>
<html lang="en" dir="ltr">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, viewport-fit=cover">
<meta name="color-scheme" content="dark">
<title>GodEyes Console</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500;600&family=IBM+Plex+Sans+Arabic:wght@400;500;600&family=Saira+Semi+Condensed:wght@400;500;600;700&display=swap">
<style>
:root{
  --scope:#0B131A; --panel:#0F1A22; --raised:#14222C; --line:#1F2E39; --line-2:#2C3F4C;
  --ink:#D9E4E9; --ink-2:#97A9B4; --ink-3:#6A7E8B;
  --gold:#C9A24A; --gold-2:#E2C67C; --gold-ink:#16120A;
  --red:#E5484D; --red-bg:#2A1013;
  --target:#D3E6EC; --perimeter:#6E8796;
  --ui:"Saira Semi Condensed", system-ui, sans-serif;
  --data:"IBM Plex Mono", ui-monospace, monospace;
  --top:max(env(safe-area-inset-top),var(--tg-content-safe-area-inset-top,0px));
  --bottom:max(env(safe-area-inset-bottom),var(--tg-content-safe-area-inset-bottom,0px));
}
html[lang="ar"]{--ui:"IBM Plex Sans Arabic", system-ui, sans-serif}
*{box-sizing:border-box}
html,body{margin:0;height:100%;background:var(--scope);color:var(--ink);font-family:var(--ui);font-size:15px;line-height:1.4;-webkit-font-smoothing:antialiased;-webkit-tap-highlight-color:transparent}
body{overflow:hidden;overscroll-behavior:none}
button{font:inherit;color:inherit;background:none;border:0;padding:0;cursor:pointer}
button:focus-visible,a:focus-visible,input:focus-visible{outline:2px solid var(--gold);outline-offset:2px}
.num,.data{font-family:var(--data);font-variant-numeric:tabular-nums;letter-spacing:0}
[hidden]{display:none!important}

/* ---------- frame ---------- */
#app{position:fixed;inset:0;display:grid;grid-template-rows:auto 1fr auto auto}
.bar{display:flex;align-items:center;gap:12px;padding:calc(var(--top) + 8px) 14px 8px;border-bottom:1px solid var(--line);background:var(--scope)}
.mark{display:flex;align-items:baseline;gap:8px;min-width:0}
.mark b{font-family:"Saira Semi Condensed",sans-serif;font-weight:700;font-size:17px;letter-spacing:.14em;color:var(--gold-2)}
.mark span{font-family:"Saira Semi Condensed",sans-serif;font-size:12.5px;letter-spacing:.06em;color:var(--ink-3);white-space:nowrap}
.bar .spacer{flex:1}
.clock{font-family:var(--data);font-size:13px;color:var(--ink-2)}
.feed{display:flex;align-items:center;gap:6px;font-family:var(--data);font-size:12.5px;color:var(--ink-2);white-space:nowrap}
@media (max-width:420px){.mark span{display:none}}
.feed i{width:7px;height:7px;background:var(--gold);display:block}
.feed.stale i{background:var(--red)}
.feed.wait i{background:var(--ink-3)}
main{position:relative;overflow:hidden;min-height:0}
.view{position:absolute;inset:0;overflow-y:auto;-webkit-overflow-scrolling:touch}
.view.pad{padding:14px 14px 20px}
.credit{display:flex;justify-content:center;gap:6px;padding:5px 12px;border-top:1px solid var(--line);font-size:11.5px;color:var(--ink-3);background:var(--scope);direction:ltr;letter-spacing:.02em}
.credit b{color:var(--gold);font-weight:600}
nav{display:grid;grid-template-columns:repeat(4,1fr);border-top:1px solid var(--line);background:var(--panel);padding-bottom:var(--bottom)}
nav button{display:flex;flex-direction:column;align-items:center;justify-content:center;gap:3px;min-height:54px;color:var(--ink-3);font-size:12.5px;font-weight:500;position:relative}
nav button svg{width:21px;height:21px;stroke:currentColor;fill:none;stroke-width:1.6}
nav button[aria-selected="true"]{color:var(--gold-2)}
nav button[aria-selected="true"]::before{content:"";position:absolute;top:-1px;left:28%;right:28%;height:2px;background:var(--gold)}

/* ---------- scope ---------- */
#scope{touch-action:none;overflow:hidden}
#scope canvas{position:absolute;inset:0;width:100%;height:100%;display:block;cursor:crosshair}
.tools{position:absolute;top:10px;inset-inline-end:10px;display:flex;flex-direction:column;border:1px solid var(--line-2);background:rgba(11,19,26,.88)}
.tools button{width:44px;height:44px;display:grid;place-items:center;color:var(--ink-2);border-bottom:1px solid var(--line)}
.tools button:last-child{border-bottom:0}
.tools svg{width:18px;height:18px;stroke:currentColor;fill:none;stroke-width:1.6}
.tools button[aria-pressed="true"]{color:var(--gold-2)}
.layers{position:absolute;top:10px;inset-inline-start:10px;display:flex;border:1px solid var(--line-2);background:rgba(11,19,26,.88)}
.layers button{height:34px;padding:0 11px;font-size:13px;color:var(--ink-3);border-inline-end:1px solid var(--line)}
.layers button:last-child{border-inline-end:0}
.layers button[aria-pressed="true"]{color:var(--ink);background:var(--raised)}
.readout{position:absolute;bottom:28px;inset-inline-start:10px;font-family:var(--data);font-size:11.5px;color:var(--ink-3);line-height:1.5;pointer-events:none;direction:ltr;text-align:left}
.scalebar{height:6px;border:1px solid var(--ink-3);border-top:0;margin-bottom:3px}
.pick{position:absolute;left:10px;right:10px;bottom:10px;border:1px solid var(--line-2);background:rgba(15,26,34,.96);display:grid;grid-template-columns:1fr auto;align-items:stretch}
.pick .info{padding:10px 12px;min-width:0}
.pick .cs{font-weight:600;font-size:18px;letter-spacing:.04em;font-family:"Saira Semi Condensed",sans-serif}
.pick .sub{font-size:13px;color:var(--ink-2);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.pick .vals{display:flex;gap:14px;margin-top:4px;font-family:var(--data);font-size:13px;color:var(--ink)}
.pick .vals em{font-style:normal;color:var(--ink-3)}
.pick .open{border-inline-start:1px solid var(--line-2);padding:0 16px;color:var(--gold-2);font-weight:600;font-size:14px}

/* ---------- strips ---------- */
.search{display:flex;border:1px solid var(--line-2);background:var(--panel);margin-bottom:10px}
.search input{flex:1;min-width:0;height:44px;background:none;border:0;color:var(--ink);font:inherit;padding:0 12px;font-family:var(--data);font-size:14px}
.search input::placeholder{color:var(--ink-3);font-family:var(--ui)}
.search button{width:44px;color:var(--ink-3)}
.seg{display:flex;border:1px solid var(--line-2);margin-bottom:12px}
.seg button{flex:1;height:38px;font-size:13.5px;color:var(--ink-3);border-inline-end:1px solid var(--line)}
.seg button:last-child{border-inline-end:0}
.seg button[aria-pressed="true"]{color:var(--gold-ink);background:var(--gold);font-weight:600}
.count{font-size:13px;color:var(--ink-3);margin:0 0 8px}
.strip{display:grid;grid-template-columns:46px 1fr auto;width:100%;text-align:start;border:1px solid var(--line);background:var(--panel);margin-bottom:6px;min-height:58px}
.strip:active{background:var(--raised)}
.strip .code{display:grid;place-items:center;border-inline-end:1px solid var(--line);font-family:var(--data);font-size:11px;font-weight:600;color:var(--ink-2);letter-spacing:.04em}
.strip.CNF .code{color:var(--gold)}
.strip.PRM .code{color:var(--perimeter)}
.strip.emg{border-color:var(--red)}
.strip.emg .code{color:#fff;background:var(--red)}
.strip .mid{padding:8px 11px;min-width:0;display:grid;gap:2px}
.strip .l1{display:flex;gap:10px;align-items:baseline;min-width:0}
.strip .cs{font-family:"Saira Semi Condensed",sans-serif;font-weight:600;font-size:16.5px;letter-spacing:.04em}
.strip .ty{font-family:var(--data);font-size:12.5px;color:var(--ink-2)}
.strip .l2{font-size:13px;color:var(--ink-2);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.strip .rt{font-family:var(--data);color:var(--ink)}
.strip .end{direction:ltr;padding:8px 11px;border-inline-start:1px solid var(--line);display:grid;align-content:center;justify-items:end;gap:2px;font-family:var(--data);font-size:13px;min-width:84px}
.strip .end span{color:var(--ink-3);font-size:11.5px}
.empty{border:1px dashed var(--line-2);padding:22px 16px;color:var(--ink-2);font-size:14px}

/* ---------- shared blocks ---------- */
h2{font-family:"Saira Semi Condensed",sans-serif;font-size:13.5px;font-weight:600;letter-spacing:.05em;color:var(--ink-2);margin:22px 0 8px;display:flex;align-items:center;gap:10px}
html[lang="ar"] h2{font-family:var(--ui);letter-spacing:0}
h2::after{content:"";flex:1;height:1px;background:var(--line)}
.kv{display:grid;grid-template-columns:1fr 1fr;border-top:1px solid var(--line)}
.kv div{padding:9px 0;border-bottom:1px solid var(--line);min-width:0}
.kv div:nth-child(odd){padding-inline-end:12px}
.kv div:nth-child(even){padding-inline-start:12px;border-inline-start:1px solid var(--line)}
.kv dt{font-size:12.5px;color:var(--ink-3)}
.kv dd{margin:2px 0 0;font-family:"IBM Plex Mono","IBM Plex Sans Arabic",monospace;font-size:14px;overflow-wrap:anywhere;unicode-bidi:plaintext}
html[dir="rtl"] .kv dd{text-align:right}
.kv dd small{color:var(--ink-3);font-size:12px}
.note{font-size:12.5px;color:var(--ink-3);margin:8px 0 0}
.btn{min-height:44px;padding:0 16px;border:1px solid var(--line-2);color:var(--ink);font-size:14px;font-weight:500;display:inline-flex;align-items:center;justify-content:center;gap:8px}
.btn.primary{background:var(--gold);color:var(--gold-ink);border-color:var(--gold);font-weight:600}
.btn.on{border-color:var(--gold);color:var(--gold-2)}
.row-btns{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:14px}

/* ---------- dossier ---------- */
#dossier{position:fixed;inset:0;z-index:20;background:var(--scope);display:grid;grid-template-rows:auto 1fr auto;transform:translateY(100%);transition:transform .22s ease-out}
#dossier.open{transform:none}
.dhead{padding:calc(var(--top) + 10px) 14px 12px;border-bottom:1px solid var(--line);display:grid;grid-template-columns:1fr auto;gap:4px 12px;align-items:start}
.dhead .cs{font-family:"Saira Semi Condensed",sans-serif;font-weight:700;font-size:30px;letter-spacing:.05em;line-height:1.05}
.dhead .op{color:var(--ink-2);font-size:14px}
.dhead .close{width:44px;height:44px;border:1px solid var(--line-2);display:grid;place-items:center;color:var(--ink-2)}
.status{grid-column:1/-1;display:flex;gap:10px;align-items:center;font-size:13.5px;color:var(--ink-2);margin-top:6px}
.chip{font-family:var(--data);font-size:11.5px;font-weight:600;padding:2px 6px;border:1px solid currentColor;letter-spacing:.06em}
.chip.CNF{color:var(--gold)} .chip.PRM,.chip.GLB{color:var(--perimeter)} .chip.OB{color:var(--ink-2)}
.alert{grid-column:1/-1;margin-top:8px;padding:8px 10px;background:var(--red-bg);border:1px solid var(--red);color:#FFD9DB;font-size:14px;font-weight:500}
.dbody{overflow-y:auto;padding:4px 14px 24px;-webkit-overflow-scrolling:touch}
.route{display:grid;grid-template-columns:auto 1fr auto;gap:12px;align-items:center;margin-top:10px}
.route .ap{min-width:0}
.route .ap b{display:block;font-family:"Saira Semi Condensed",sans-serif;font-size:28px;font-weight:600;letter-spacing:.04em;line-height:1}
.route .ap span{display:block;font-size:12.5px;color:var(--ink-2);max-width:110px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.route .ap:last-child{text-align:end}
.track-bar{position:relative;height:18px;direction:ltr}
.track-bar::before{content:"";position:absolute;left:0;right:0;top:8px;height:1px;background:repeating-linear-gradient(90deg,var(--ink-3) 0 3px,transparent 3px 7px)}
.track-bar .done{position:absolute;left:0;top:8px;height:2px;margin-top:-.5px;background:var(--gold)}
.track-bar svg{position:absolute;top:1px;width:16px;height:16px;margin-left:-8px;fill:var(--gold-2)}
html[dir="rtl"] .route{direction:ltr}
html[dir="rtl"] .route .ap span{direction:rtl}
.figure{border:1px solid var(--line);background:var(--panel);margin-top:4px;position:relative}
.figure svg{display:block;width:100%}
.tip{position:absolute;pointer-events:none;background:var(--raised);border:1px solid var(--line-2);padding:4px 7px;font-family:var(--data);font-size:12px;white-space:nowrap;transform:translate(-50%,-100%);margin-top:-8px;color:var(--ink)}
.recent button{display:grid;grid-template-columns:auto 1fr auto;gap:10px;width:100%;text-align:start;padding:10px 0;border-bottom:1px solid var(--line);font-size:14px;align-items:center}
.recent .rt{font-family:var(--data);color:var(--ink-2);font-size:13px}
.recent time{font-family:var(--data);color:var(--ink-3);font-size:12.5px}
.foot-meta{font-family:var(--data);font-size:11.5px;color:var(--ink-3);margin-top:20px;direction:ltr}

/* ---------- traffic ---------- */
.tiles{display:grid;grid-template-columns:1fr 1fr;border:1px solid var(--line)}
.tiles div{padding:12px;border-bottom:1px solid var(--line)}
.tiles div:nth-child(odd){border-inline-end:1px solid var(--line)}
.tiles div:nth-last-child(-n+2){border-bottom:0}
.tiles b{display:block;font-family:var(--data);font-size:24px;font-weight:500;color:var(--ink)}
.tiles span{font-size:12.5px;color:var(--ink-3)}
.tiles .lead b{color:var(--gold-2)}
.rank{width:100%;border-collapse:collapse;font-size:13.5px}
.rank td{padding:7px 0;border-bottom:1px solid var(--line);vertical-align:middle}
.rank td.c{font-family:var(--data);width:58px;color:var(--ink)}
.rank td.n{font-family:var(--data);text-align:end;width:44px}
.rank td.nm{color:var(--ink-2);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:0;padding-inline-end:10px}
.rank td.b{width:34%}
.rank .bar-in{height:6px;background:var(--gold);border-radius:0 3px 3px 0}
html[dir="rtl"] .rank .bar-in{border-radius:3px 0 0 3px}

/* ---------- system ---------- */
.log{width:100%;border-collapse:collapse;font-family:var(--data);font-size:12.5px;direction:ltr}
.log th{font-family:var(--ui);font-weight:500;font-size:12px;color:var(--ink-3);text-align:left;padding:6px 0;border-bottom:1px solid var(--line-2)}
.log td{padding:6px 0;border-bottom:1px solid var(--line)}
.log td.r,.log th.r{text-align:right}
.ok{color:var(--gold-2)} .bad{color:var(--red)}
.links{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:12px}

/* ---------- gate ---------- */
.gate{position:fixed;inset:0;z-index:40;background:var(--scope);display:grid;place-items:center;padding:24px}
.gate .box{max-width:340px;width:100%}
.gate .eye{width:64px;height:64px;margin-bottom:18px}
.gate h1{font-family:"Saira Semi Condensed",sans-serif;font-size:22px;font-weight:600;margin:0 0 8px}
html[lang="ar"] .gate h1{font-family:var(--ui)}
.gate p{color:var(--ink-2);margin:0 0 18px}
.gate .btn{width:100%;margin-bottom:8px}
.gate .credit{position:fixed;left:0;right:0;bottom:0;padding-bottom:calc(var(--bottom) + 6px)}
.boot{font-family:var(--data);font-size:12.5px;color:var(--ink-3);line-height:1.7}
.boot b{color:var(--gold-2);font-weight:500}
@media (prefers-reduced-motion:reduce){#dossier{transition:none}}
@media (min-width:760px){
  .view.pad{max-width:760px;margin:0 auto}
  #dossier .dbody,#dossier .dhead{max-width:760px;width:100%;margin:0 auto}
}
</style>
</head>
<body>
<svg width="0" height="0" style="position:absolute" aria-hidden="true">
  <symbol id="i-scope" viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><circle cx="12" cy="12" r="5"/><path d="M12 12 18.4 5.6M12 3v2M12 19v2M3 12h2M19 12h2"/></symbol>
  <symbol id="i-strips" viewBox="0 0 24 24"><path d="M3 5h18v4H3zM3 11h18v4H3zM3 17h18v4H3zM8 5v4M8 11v4M8 17v4"/></symbol>
  <symbol id="i-traffic" viewBox="0 0 24 24"><path d="M4 20V10M9.3 20V4M14.6 20v-7M20 20V8M3 20h18"/></symbol>
  <symbol id="i-system" viewBox="0 0 24 24"><rect x="3" y="4" width="18" height="12"/><path d="M8 20h8M12 16v4M7 9l2 2-2 2M11 13h5"/></symbol>
  <symbol id="i-plus" viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></symbol>
  <symbol id="i-minus" viewBox="0 0 24 24"><path d="M5 12h14"/></symbol>
  <symbol id="i-center" viewBox="0 0 24 24"><circle cx="12" cy="12" r="3"/><path d="M12 2v5M12 17v5M2 12h5M17 12h5"/></symbol>
  <symbol id="i-label" viewBox="0 0 24 24"><path d="M4 6h10M4 11h16M4 16h7"/><path d="M15 17l3 3 3-6"/></symbol>
  <symbol id="i-close" viewBox="0 0 24 24"><path d="M6 6l12 12M18 6 6 18"/></symbol>
  <symbol id="i-find" viewBox="0 0 24 24"><circle cx="10.5" cy="10.5" r="6.5"/><path d="m15.5 15.5 5 5"/></symbol>
  <symbol id="i-plane" viewBox="-32 -32 64 64"><path d="M0-30C3-30 5-24 5-18L5-6L30 10L30 15L5 8L4 20L12 27L12 30L0 27L-12 30L-12 27L-4 20L-5 8L-30 15L-30 10L-5-6L-5-18C-5-24-3-30 0-30Z"/></symbol>
</svg>

<div id="gate" class="gate">
  <div class="box">
    <svg class="eye" viewBox="0 0 64 64" aria-hidden="true"><path d="M4 32C16 16 48 16 60 32C48 46 16 46 4 32Z" fill="none" stroke="#C9A24A" stroke-width="2.5"/><circle cx="32" cy="32" r="11" fill="#E5484D"/><circle cx="32" cy="32" r="4.5" fill="#0B131A"/></svg>
    <div id="gate-body" class="boot"></div>
  </div>
  <div class="credit">Dev &amp; Powered by <b>KroTheCommander</b></div>
</div>

<div id="app" hidden>
  <header class="bar">
    <div class="mark"><b>GODEYES</b><span id="t-sub">IQ airspace</span></div>
    <div class="spacer"></div>
    <div class="feed wait" id="feed"><i></i><span id="feed-txt">--</span></div>
    <div class="clock" id="clock">--:--:--</div>
  </header>
  <main>
    <section class="view" id="scope" role="tabpanel">
      <canvas id="cv" aria-label="Radar scope of Iraqi airspace"></canvas>
      <div class="layers" role="group">
        <button id="ly-iraq" aria-pressed="true"></button>
        <button id="ly-prm" aria-pressed="true"></button>
      </div>
      <div class="tools">
        <button id="zin" aria-label="Zoom in"><svg><use href="#i-plus"/></svg></button>
        <button id="zout" aria-label="Zoom out"><svg><use href="#i-minus"/></svg></button>
        <button id="zfit" aria-label="Fit Iraq"><svg><use href="#i-center"/></svg></button>
        <button id="zlbl" aria-pressed="true" aria-label="Data blocks"><svg><use href="#i-label"/></svg></button>
      </div>
      <div class="readout"><div class="scalebar" id="scalebar"></div><div id="scaletxt"></div><div id="rings"></div><div id="coords"></div></div>
      <div class="pick" id="pick" hidden></div>
    </section>
    <section class="view pad" id="strips" role="tabpanel" hidden>
      <form class="search" id="search-form" role="search">
        <input id="q" autocomplete="off" autocapitalize="characters" spellcheck="false" maxlength="40">
        <button type="submit" id="q-go"><svg width="18" height="18" stroke="currentColor" fill="none" stroke-width="1.6"><use href="#i-find"/></svg></button>
      </form>
      <div class="seg" role="group" id="strip-seg"></div>
      <p class="count" id="strip-count"></p>
      <div id="strip-list"></div>
    </section>
    <section class="view pad" id="traffic" role="tabpanel" hidden></section>
    <section class="view pad" id="system" role="tabpanel" hidden></section>
  </main>
  <div class="credit">Dev &amp; Powered by <b>KroTheCommander</b></div>
  <nav role="tablist">
    <button role="tab" data-v="scope" aria-selected="true"><svg><use href="#i-scope"/></svg><span></span></button>
    <button role="tab" data-v="strips" aria-selected="false"><svg><use href="#i-strips"/></svg><span></span></button>
    <button role="tab" data-v="traffic" aria-selected="false"><svg><use href="#i-traffic"/></svg><span></span></button>
    <button role="tab" data-v="system" aria-selected="false"><svg><use href="#i-system"/></svg><span></span></button>
  </nav>
</div>

<section id="dossier" aria-modal="true" role="dialog" hidden>
  <div class="dhead" id="d-head"></div>
  <div class="dbody" id="d-body"></div>
  <div class="credit">Dev &amp; Powered by <b>KroTheCommander</b></div>
</section>

<script>
"use strict";
const tg = window.Telegram && window.Telegram.WebApp;
const $ = (s, r = document) => r.querySelector(s);
const esc = v => String(v ?? "").replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;","'":"&#39;"}[c]));
const ver = v => !!(tg && tg.isVersionAtLeast && tg.isVersionAtLeast(v));

/* ---------------------------------------------------------------- language */
const L = {
  en: {
    sub: "IQ airspace", nav: ["Scope", "Strips", "Traffic", "System"],
    iraq: "Iraq", prm: "Perimeter", emg: "Emergency", all: "All",
    open: "Open file", search: "Callsign, registration, airline, airport", searching: "Searching the archive",
    shown: n => `${n} aircraft`, results: n => `${n} archived records`,
    noLive: "No aircraft in this zone at the last update. The scope refreshes on its own.",
    noRes: "Nothing in the archive matches that query.",
    age: s => s < 90 ? `${s}s` : s < 5400 ? `${Math.round(s / 60)}m` : `${Math.round(s / 3600)}h`,
    coast: "coasting", synced: "synced", stale: "stale", pending: "waiting for first sync",
    flight: "Flight", aircraft: "Aircraft", telemetry: "Telemetry", iraqAir: "Iraqi airspace",
    altProfile: "Altitude profile", trackMap: "Track", recent: "Other records of this aircraft",
    callsign: "Callsign", number: "Flight number", operator: "Operator", reg: "Registration", hex: "ICAO24",
    type: "Type", model: "Model", maker: "Manufacturer", owner: "Owner", country: "Country", cat: "Weight class",
    alt: "Altitude", galt: "GPS altitude", gs: "Ground speed", hdg: "Heading", vr: "Vertical rate", sq: "Squawk",
    mach: "Mach", ias: "IAS / TAS", selalt: "Selected altitude", selhdg: "Selected heading", wind: "Wind",
    oat: "Outside air", pos: "Position", near: "Nearest city", src: "Signal", seen: "Last seen",
    first: "First observed", last: "Last observed", dur: "Time over Iraq", obs: "Observations",
    level: "level", flown: "Flown", remaining: "Remaining", eta: "Estimated arrival",
    routeSrc: s => `Route from the ${s} database, matched by callsign. It is the usual route for this callsign, not a filed flight plan.`,
    routeNone: "No route database knows this callsign.",
    routePending: "Route not looked up yet.",
    times: "Scheduled and actual times are not available from open sources.",
    watch: "Watch", watching: "Watching", map: "Open in Maps", photo: "Aircraft photo",
    watchFull: "Your watchlist is full. Remove one in the bot first.",
    durVal: m => `at least ${m} min`, durNa: "needs two observations",
    traffic: "Traffic", period: ["24 h", "7 days", "30 days", "All"],
    confirmed: "Confirmed crossings", single: "Single sightings, not counted", ops: "Operators", types: "Aircraft types",
    hourly: tz => `Entries by hour, ${tz}`, topOps: "Operators", topTypes: "Aircraft types",
    topDep: "Origins", topArr: "Destinations", mix: "Traffic mix", avgAlt: "Average altitude", avgGs: "Average speed",
    complete: "Fields known", fAirline: "operator", fType: "type", fRoute: "route",
    coverage: d => `The archive starts on ${d}. Counts cover only what the bot has observed; short crossings between samples can be missed.`,
    noStats: "No confirmed crossings in this period yet.",
    sys: "System", feed: "Live feed", sources: "Sources answering", uptime: "Uptime", interval: "Sync interval",
    next: "Next sync", stored: "Iraq records", points: "Track points", feeds: "Last sync by source",
    log: "Sync log", time: "Time", status: "Result", recv: "Received", inIraq: "Iraq", around: "Around",
    admin: "Administration", users: "Users", subCheck: "Subscription check", lookups: "Route lookups",
    channel: "Channel", dev: "Developer", version: "Version",
    gateBoot: ["Verifying session", "Linking to the archive", "Loading the scope"],
    noTg: ["Open this console from the bot", "The console only works inside Telegram. Open the bot and press Open console."],
    expired: ["Session expired", "Close the console and open it again from the bot."],
    locked: ["Channel subscription required", c => `Join @${c} to use the console, then check again.`],
    join: "Join channel", recheck: "Check again", retry: "Retry",
    failed: ["Console unavailable", "The server did not answer. Check your connection and retry."],
    tapHint: "Tap a target to read it. Drag to pan, pinch to zoom.", rings: "Rings 50 NM from Baghdad", tracked: "tracked",
  },
  ar: {
    sub: "الأجواء العراقية", nav: ["الرادار", "الشرائط", "الحركة", "النظام"],
    iraq: "العراق", prm: "المحيط", emg: "طوارئ", all: "الكل",
    open: "فتح الملف", search: "رمز النداء، التسجيل، الشركة، المطار", searching: "جارٍ البحث في الأرشيف",
    shown: n => `${n} طائرة`, results: n => `${n} سجل في الأرشيف`,
    noLive: "لا توجد طائرات في هذه المنطقة في آخر تحديث. الرادار يتحدّث تلقائياً.",
    noRes: "لا يوجد في الأرشيف ما يطابق هذا البحث.",
    age: s => s < 90 ? `${s}ث` : s < 5400 ? `${Math.round(s / 60)}د` : `${Math.round(s / 3600)}س`,
    coast: "تقدير", synced: "تحديث", stale: "قديم", pending: "بانتظار أول مزامنة",
    flight: "الرحلة", aircraft: "الطائرة", telemetry: "القياسات", iraqAir: "الأجواء العراقية",
    altProfile: "منحنى الارتفاع", trackMap: "المسار", recent: "سجلات أخرى لهذه الطائرة",
    callsign: "رمز النداء", number: "رقم الرحلة", operator: "المشغّل", reg: "التسجيل", hex: "ICAO24",
    type: "النوع", model: "الموديل", maker: "المصنّع", owner: "المالك", country: "الدولة", cat: "فئة الوزن",
    alt: "الارتفاع", galt: "ارتفاع GPS", gs: "السرعة الأرضية", hdg: "الاتجاه", vr: "معدّل الصعود/الهبوط", sq: "Squawk",
    mach: "ماخ", ias: "IAS / TAS", selalt: "الارتفاع المختار", selhdg: "الاتجاه المختار", wind: "الرياح",
    oat: "الحرارة الخارجية", pos: "الموقع", near: "أقرب مدينة", src: "الإشارة", seen: "آخر رصد",
    first: "أول رصد", last: "آخر رصد", dur: "المدة فوق العراق", obs: "عدد مرات الرصد",
    level: "مستوٍ", flown: "المقطوع", remaining: "المتبقّي", eta: "الوصول التقديري",
    routeSrc: s => `المسار من قاعدة بيانات ${s} حسب رمز النداء. هو المسار المعتاد لهذا الرمز وليس خطة رحلة مقدَّمة.`,
    routeNone: "لا تعرف قواعد بيانات المسارات هذا الرمز.",
    routePending: "لم يُبحث عن المسار بعد.",
    times: "أوقات الجدول والإقلاع والوصول الفعلية غير متوفرة من المصادر المفتوحة.",
    watch: "متابعة", watching: "تتم المتابعة", map: "فتح في الخرائط", photo: "صورة الطائرة",
    watchFull: "قائمة المتابعة ممتلئة. احذف عنصراً من البوت أولاً.",
    durVal: m => `${m} دقيقة على الأقل`, durNa: "تحتاج رصدين",
    traffic: "الحركة", period: ["24 ساعة", "7 أيام", "30 يوماً", "الكل"],
    confirmed: "عبور مؤكَّد", single: "رصد واحد، لا يُحتسب", ops: "المشغّلون", types: "أنواع الطائرات",
    hourly: tz => `الدخول حسب الساعة، ${tz}`, topOps: "المشغّلون", topTypes: "أنواع الطائرات",
    topDep: "مطارات الإقلاع", topArr: "مطارات الوصول", mix: "أنواع الحركة", avgAlt: "متوسط الارتفاع", avgGs: "متوسط السرعة",
    complete: "الحقول المعروفة", fAirline: "المشغّل", fType: "النوع", fRoute: "المسار",
    coverage: d => `يبدأ الأرشيف في ${d}. الأرقام تشمل ما رصده البوت فقط؛ وقد تفوت العبورات القصيرة بين العيّنات.`,
    noStats: "لا يوجد عبور مؤكَّد في هذه الفترة بعد.",
    sys: "النظام", feed: "البث المباشر", sources: "المصادر المستجيبة", uptime: "مدة التشغيل", interval: "فاصل المزامنة",
    next: "المزامنة القادمة", stored: "سجلات العراق", points: "نقاط المسار", feeds: "آخر مزامنة لكل مصدر",
    log: "سجل المزامنة", time: "الوقت", status: "النتيجة", recv: "المستلم", inIraq: "العراق", around: "المحيط",
    admin: "الإدارة", users: "المستخدمون", subCheck: "التحقق من الاشتراك", lookups: "عمليات بحث المسارات",
    channel: "القناة", dev: "المطوّر", version: "الإصدار",
    gateBoot: ["التحقق من الجلسة", "الربط بالأرشيف", "تحميل الرادار"],
    noTg: ["افتح هذه الواجهة من البوت", "تعمل الواجهة داخل تيليغرام فقط. افتح البوت واضغط «فتح المنظومة»."],
    expired: ["انتهت الجلسة", "أغلق الواجهة وافتحها مجدداً من البوت."],
    locked: ["الاشتراك في القناة مطلوب", c => `اشترك في @${c} لاستخدام الواجهة ثم أعد التحقق.`],
    join: "الاشتراك في القناة", recheck: "إعادة التحقق", retry: "إعادة المحاولة",
    failed: ["الواجهة غير متاحة", "لم يستجب الخادم. تحقّق من الاتصال وأعد المحاولة."],
    tapHint: "اضغط على هدف لقراءته. اسحب للتحريك، وقرّب بإصبعين للتكبير.", rings: "حلقات كل 50 ميلاً من بغداد", tracked: "مرصودة",
  },
};
let lang = (tg && tg.initDataUnsafe && tg.initDataUnsafe.user && /^ar/i.test(tg.initDataUnsafe.user.language_code || "")) ? "ar" : "en";
const T = () => L[lang];
function setLang(l) {
  lang = l === "ar" ? "ar" : "en";
  document.documentElement.lang = lang;
  document.documentElement.dir = lang === "ar" ? "rtl" : "ltr";
}

/* ---------------------------------------------------------------- api */
const state = { boot: null, live: null, view: "scope", filter: "iraq", selected: null, labels: true,
  layers: { iraq: true, prm: true }, period: 1, query: "", results: null, dossierId: null };
class ApiError extends Error { constructor(status, body) { super(body && body.error || status); this.status = status; this.body = body; } }
async function api(path, opts = {}) {
  const res = await fetch(path, { ...opts, headers: { "X-Init-Data": tg ? tg.initData : "", "Content-Type": "application/json", ...(opts.headers || {}) } });
  let body = null; try { body = await res.json(); } catch (e) {}
  if (!res.ok) throw new ApiError(res.status, body);
  return body;
}
const haptic = kind => { try { if (!ver("6.1")) return;
  if (kind === "select") tg.HapticFeedback.selectionChanged();
  else if (kind === "ok") tg.HapticFeedback.notificationOccurred("success");
  else if (kind === "err") tg.HapticFeedback.notificationOccurred("error");
  else tg.HapticFeedback.impactOccurred("light"); } catch (e) {} };
const openLink = url => { if (tg && tg.openLink) tg.openLink(url); else window.open(url, "_blank", "noopener"); };
const openTg = url => { if (tg && tg.openTelegramLink) tg.openTelegramLink(url); else window.open(url, "_blank", "noopener"); };

/* ---------------------------------------------------------------- time & format */
const fmtTime = (iso, withDate) => {
  if (!iso) return "--";
  const tz = state.boot ? state.boot.tz : undefined;
  const o = withDate ? { day: "2-digit", month: "2-digit", hour: "2-digit", minute: "2-digit", hour12: false, timeZone: tz }
                     : { hour: "2-digit", minute: "2-digit", hour12: false, timeZone: tz };
  return new Intl.DateTimeFormat("en-GB", o).format(new Date(iso)).replace(",", "");
};
const ageS = iso => iso ? Math.max(0, Math.round((Date.now() - Date.parse(iso)) / 1000)) : null;
const n0 = v => v == null ? "--" : Math.round(v).toLocaleString("en-US");
const fl = a => a == null ? "---" : String(Math.round(a / 100)).padStart(3, "0");

/* ---------------------------------------------------------------- gate */
function gate(kind, extra) {
  const g = $("#gate"), body = $("#gate-body");
  g.hidden = false;
  if (kind === "boot") {
    body.innerHTML = T().gateBoot.map((s, i) => `<div>${i < extra ? "<b>OK</b>" : "&nbsp;.."}&nbsp; ${esc(s)}</div>`).join("");
    return;
  }
  const map = { notg: T().noTg, expired: T().expired, failed: T().failed };
  if (kind === "locked") {
    const [h, p] = T().locked;
    body.className = "";
    body.innerHTML = `<h1>${esc(h)}</h1><p>${esc(p(extra))}</p>
      <button class="btn primary" id="g-join">${esc(T().join)}</button>
      <button class="btn" id="g-re">${esc(T().recheck)}</button>`;
    $("#g-join").onclick = () => openTg(`https://t.me/${extra}`);
    $("#g-re").onclick = () => start();
    return;
  }
  const [h, p] = map[kind];
  body.className = "";
  body.innerHTML = `<h1>${esc(h)}</h1><p>${esc(p)}</p>` + (kind === "failed" ? `<button class="btn" id="g-re">${esc(T().retry)}</button>` : "");
  if (kind === "failed") $("#g-re").onclick = () => start();
}
function handleErr(e) {
  if (e instanceof ApiError) {
    if (e.status === 401) return gate("expired");
    if (e.status === 403) return gate("locked", e.body && e.body.channel);
  }
  gate("failed");
}

/* ---------------------------------------------------------------- shell */
function applyStatic() {
  $("#t-sub").textContent = T().sub;
  document.querySelectorAll("nav button span").forEach((s, i) => s.textContent = T().nav[i]);
  $("#ly-iraq").textContent = T().iraq; $("#ly-prm").textContent = T().prm;
  $("#q").placeholder = T().search;
  $("#strip-seg").innerHTML = [["iraq", T().iraq], ["prm", T().prm], ["emg", T().emg]]
    .map(([k, t]) => `<button data-f="${k}" aria-pressed="${state.filter === k}">${esc(t)}</button>`).join("");
}
function show(v) {
  state.view = v;
  document.querySelectorAll("nav button").forEach(b => b.setAttribute("aria-selected", b.dataset.v === v));
  ["scope", "strips", "traffic", "system"].forEach(id => $("#" + id).hidden = id !== v);
  if (v === "scope") { resize(); }
  if (v === "strips") renderStrips();
  if (v === "traffic") loadTraffic();
  if (v === "system") loadSystem();
}
function tick() {
  const tz = state.boot ? state.boot.tz : undefined;
  $("#clock").textContent = new Intl.DateTimeFormat("en-GB", { hour: "2-digit", minute: "2-digit", second: "2-digit", hour12: false, timeZone: tz }).format(new Date());
  const live = state.live, feed = $("#feed");
  if (!live) return;
  const a = ageS(live.last_ok);
  const stale = a == null || a > 3 * live.interval;
  feed.className = "feed " + (a == null ? "wait" : stale ? "stale" : "");
  const shown = live.targets.filter(t => t.st !== "PRM").length;
  $("#feed-txt").textContent = a == null ? T().pending : `${shown} ${T().tracked}   ${T().age(a)}`;
}

/* ---------------------------------------------------------------- live data */
async function loadLive() {
  try {
    state.live = await api("/api/live");
    if (state.selected && !state.live.targets.some(t => t.id === state.selected)) state.selected = null;
    draw(); renderPick(); if (state.view === "strips" && !state.results) renderStrips(); tick();
  } catch (e) { if (e instanceof ApiError && (e.status === 401 || e.status === 403)) handleErr(e); }
}
/* Dead reckoning between syncs: positions move along heading at ground speed,
   capped at 6 minutes, and are drawn as hollow "coasting" tracks after 90 s. */
function project(t) {
  const a = ageS(t.seen) || 0;
  if (!t.gs || t.hdg == null || a < 5) return { lat: t.lat, lon: t.lon, age: a, coast: false };
  const s = Math.min(a, 360), nm = t.gs * s / 3600, r = t.hdg * Math.PI / 180;
  const lat = t.lat + nm * Math.cos(r) / 60;
  const lon = t.lon + nm * Math.sin(r) / (60 * Math.cos(t.lat * Math.PI / 180));
  return { lat, lon, age: a, coast: a > 90 };
}

/* ---------------------------------------------------------------- scope */
const cv = $("#cv"), ctx = cv.getContext("2d");
const view = { lat: 33.2, lon: 43.8, ppd: 70 }; // pixels per degree of latitude
let W = 0, H = 0, DPR = 1;
const K = () => Math.cos(view.lat * Math.PI / 180);
const toXY = (lat, lon) => [W / 2 + (lon - view.lon) * view.ppd * K(), H / 2 - (lat - view.lat) * view.ppd];
const toLL = (x, y) => [view.lat - (y - H / 2) / view.ppd, view.lon + (x - W / 2) / (view.ppd * K())];
function fit() {
  if (!W) return;
  const latSpan = 8.4, lonSpan = 10.6;
  view.lat = 33.15; view.lon = 43.75;
  view.ppd = Math.min(H / latSpan, W / (lonSpan * Math.cos(view.lat * Math.PI / 180))) * 0.98;
}
function resize() {
  const r = $("#scope").getBoundingClientRect();
  if (!r.width) return;
  DPR = Math.min(2, window.devicePixelRatio || 1);
  const first = !W;
  W = r.width; H = r.height;
  cv.width = Math.round(W * DPR); cv.height = Math.round(H * DPR);
  if (first) fit();
  draw();
}
const C = { scope: "#0B131A", land: "#0F1B24", grid: "#15232D", gridTxt: "#4C6170", ring: "#21313C", border: "#C9A24A",
  city: "#7D919E", target: "#D3E6EC", prm: "#6E8796", red: "#E5484D", gold: "#E2C67C", panel: "rgba(11,19,26,.82)" };
function plane(x, y, hdg, size, fill, hollow) {
  ctx.save(); ctx.translate(x, y); ctx.rotate((hdg || 0) * Math.PI / 180); ctx.scale(size / 60, size / 60);
  ctx.beginPath();
  ctx.moveTo(0, -30); ctx.bezierCurveTo(3, -30, 5, -24, 5, -18); ctx.lineTo(5, -6); ctx.lineTo(30, 10); ctx.lineTo(30, 15);
  ctx.lineTo(5, 8); ctx.lineTo(4, 20); ctx.lineTo(12, 27); ctx.lineTo(12, 30); ctx.lineTo(0, 27); ctx.lineTo(-12, 30);
  ctx.lineTo(-12, 27); ctx.lineTo(-4, 20); ctx.lineTo(-5, 8); ctx.lineTo(-30, 15); ctx.lineTo(-30, 10); ctx.lineTo(-5, -6);
  ctx.lineTo(-5, -18); ctx.bezierCurveTo(-5, -24, -3, -30, 0, -30); ctx.closePath();
  if (hollow) { ctx.lineWidth = 2.4 * 60 / size; ctx.strokeStyle = fill; ctx.stroke(); } else { ctx.fillStyle = fill; ctx.fill(); }
  ctx.restore();
}
let hitList = [];
function draw() {
  if (!W || state.view !== "scope") return;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.fillStyle = C.scope; ctx.fillRect(0, 0, W, H);
  const b = state.boot;
  // graticule
  const [latTop, lonLeft] = toLL(0, 0), [latBot, lonRight] = toLL(W, H);
  const step = view.ppd > 160 ? 0.5 : 1;
  ctx.lineWidth = 1; ctx.strokeStyle = C.grid; ctx.fillStyle = C.gridTxt; ctx.font = `10.5px "IBM Plex Mono", monospace`;
  ctx.beginPath();
  for (let la = Math.ceil(latBot / step) * step; la <= latTop; la += step) { const [, y] = toXY(la, 0); ctx.moveTo(0, Math.round(y) + .5); ctx.lineTo(W, Math.round(y) + .5); }
  for (let lo = Math.ceil(lonLeft / step) * step; lo <= lonRight; lo += step) { const [x] = toXY(0, lo); ctx.moveTo(Math.round(x) + .5, 0); ctx.lineTo(Math.round(x) + .5, H); }
  ctx.stroke();
  ctx.textBaseline = "top";
  for (let la = Math.ceil(latBot / step) * step; la <= latTop; la += step) { const [, y] = toXY(la, 0); if (y > 50 && y < H - 60) ctx.fillText(`${la.toFixed(step < 1 ? 1 : 0)}N`, 4, y + 2); }
  for (let lo = Math.ceil(lonLeft / step) * step; lo <= lonRight; lo += step) { const [x] = toXY(0, lo); if (x > 30 && x < W - 60) ctx.fillText(`${lo.toFixed(step < 1 ? 1 : 0)}E`, x + 3, H - 14); }
  if (!b) return;
  // monitored perimeter (union of the three query circles)
  ctx.save(); ctx.setLineDash([2, 5]); ctx.strokeStyle = C.ring; ctx.lineWidth = 1;
  for (const [la, lo] of b.circles) { const [x, y] = toXY(la, lo); ctx.beginPath(); ctx.ellipse(x, y, b.radius_nm / 60 * view.ppd * K() / Math.cos(la * Math.PI / 180), b.radius_nm / 60 * view.ppd, 0, 0, Math.PI * 2); ctx.stroke(); }
  ctx.restore();
  // Iraq
  ctx.beginPath();
  b.border.forEach(([la, lo], i) => { const [x, y] = toXY(la, lo); i ? ctx.lineTo(x, y) : ctx.moveTo(x, y); });
  ctx.closePath(); ctx.fillStyle = C.land; ctx.fill(); ctx.lineWidth = 1.4; ctx.strokeStyle = C.border; ctx.globalAlpha = .9; ctx.stroke(); ctx.globalAlpha = 1;
  // range rings around Baghdad
  const [bx, by] = toXY(33.31, 44.37);
  ctx.save(); ctx.strokeStyle = C.ring; ctx.fillStyle = C.gridTxt; ctx.setLineDash([1, 4]);
  for (const nm of [50, 100, 150, 200]) {
    const ry = nm / 60 * view.ppd, rx = ry * K() / Math.cos(33.31 * Math.PI / 180); ctx.beginPath(); ctx.ellipse(bx, by, rx, ry, 0, 0, Math.PI * 2); ctx.stroke();
  }
  ctx.restore();
  // cities
  ctx.font = `${lang === "ar" ? "11.5px \"IBM Plex Sans Arabic\"" : "11px \"Saira Semi Condensed\""}, sans-serif`;
  ctx.textBaseline = "middle";
  const cityBoxes = [];
  for (const c of b.cities) {
    if (view.ppd < 55 && !["Baghdad", "Basra", "Mosul", "Erbil"].includes(c.en)) continue;
    const [x, y] = toXY(c.lat, c.lon); if (x < -20 || x > W + 20 || y < -20 || y > H + 20) continue;
    ctx.fillStyle = C.city; ctx.fillRect(x - 1.5, y - 1.5, 3, 3);
    const name = lang === "ar" ? c.ar : c.en;
    ctx.fillText(name, x + 6, y);
    cityBoxes.push([x - 3, y - 8, ctx.measureText(name).width + 12, 16]);
  }
  // targets
  hitList = [];
  const live = state.live; if (!live) return drawScale();
  const targets = live.targets.filter(t => (t.st === "PRM" ? state.layers.prm : state.layers.iraq) || t.emg);
  const boxes = cityBoxes.slice();
  const dense = targets.length > 45 && view.ppd < 110;
  ctx.font = `10.5px "IBM Plex Mono", monospace`; ctx.textBaseline = "alphabetic";
  // Selected target first, then Iraq, then perimeter: earlier ones get the clearest label spot.
  const order = targets.slice().sort((a, b2) => (b2.id === state.selected) - (a.id === state.selected) || (a.st === "PRM") - (b2.st === "PRM"))
    .map(t => { const p = project(t); const [x, y] = toXY(p.lat, p.lon); return { t, p, x, y }; })
    .filter(o => o.x > -40 && o.x < W + 40 && o.y > -40 && o.y < H + 40);
  for (const o of order) boxes.push([o.x - 9, o.y - 9, 18, 18]);   // labels never cover an aircraft
  for (const { t, p, x, y } of order) {
    const col = t.emg ? C.red : t.st === "PRM" ? C.prm : C.target;
    // history dots
    if (t.trail && t.trail.length > 1) {
      ctx.beginPath(); t.trail.forEach(([la, lo], i) => { const [tx, ty] = toXY(la, lo); i ? ctx.lineTo(tx, ty) : ctx.moveTo(tx, ty); }); ctx.lineTo(x, y);
      ctx.strokeStyle = col; ctx.globalAlpha = .22; ctx.lineWidth = 1; ctx.stroke();
      t.trail.forEach(([la, lo], i, arr) => { const [tx, ty] = toXY(la, lo); ctx.globalAlpha = .25 + .45 * (i + 1) / arr.length; ctx.fillStyle = col; ctx.fillRect(tx - 1.5, ty - 1.5, 3, 3); });
      ctx.globalAlpha = 1;
    }
    // velocity leader: where the aircraft will be in 2 minutes
    if (t.gs && t.hdg != null) {
      const nm = t.gs * 120 / 3600, r = t.hdg * Math.PI / 180;
      const [vx, vy] = toXY(p.lat + nm * Math.cos(r) / 60, p.lon + nm * Math.sin(r) / (60 * Math.cos(p.lat * Math.PI / 180)));
      ctx.strokeStyle = col; ctx.globalAlpha = .55; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(x, y); ctx.lineTo(vx, vy); ctx.stroke(); ctx.globalAlpha = 1;
    }
    const sel = t.id === state.selected;
    plane(x, y, t.hdg, sel ? 17 : 13, col, p.coast);
    hitList.push({ id: t.id, x, y });
    if (sel) {
      ctx.strokeStyle = C.gold; ctx.lineWidth = 1.4; const s = 13;
      ctx.beginPath();
      [[-1, -1], [1, -1], [1, 1], [-1, 1]].forEach(([sx, sy]) => { ctx.moveTo(x + sx * s, y + sy * (s - 5)); ctx.lineTo(x + sx * s, y + sy * s); ctx.lineTo(x + sx * (s - 5), y + sy * s); });
      ctx.stroke();
    }
    // data block
    if (!state.labels && !sel) continue;
    const lines = dense && !sel ? [t.cs] : [t.cs, `${fl(t.alt)} ${t.gs == null ? "" : Math.round(t.gs)}`, sel || !dense ? (t.type || "") + (p.coast ? " ~" : "") : ""].filter(Boolean);
    const bw = Math.max(...lines.map(l => ctx.measureText(l).width)) + 6, bh = lines.length * 12 + 3;
    const hits = (lx, ly) => boxes.some(o => lx < o[0] + o[2] && lx + bw > o[0] && ly < o[1] + o[3] && ly + bh > o[1]);
    const spots = [[x + 16, y - 16 - bh], [x - 16 - bw, y - 16 - bh], [x + 16, y + 16], [x - 16 - bw, y + 16]]
      .filter(([sx, sy]) => sx > 2 && sx + bw < W - 2 && sy > 2 && sy + bh < H - 2);
    let spot = spots.find(([sx, sy]) => !hits(sx, sy));
    if (!spot) { if (!sel) continue; spot = spots[0] || [x + 16, y + 16]; }
    const [lx, ly] = spot;
    boxes.push([lx, ly, bw, bh]);
    ctx.strokeStyle = col; ctx.globalAlpha = .6; ctx.beginPath(); ctx.moveTo(x + (lx > x ? 6 : -6), y + (ly > y ? 6 : -6)); ctx.lineTo(lx > x ? lx : lx + bw, ly > y ? ly : ly + bh); ctx.stroke(); ctx.globalAlpha = 1;
    if (sel) { ctx.fillStyle = C.panel; ctx.fillRect(lx - 1, ly - 1, bw + 2, bh + 2); }
    lines.forEach((l, i) => { ctx.fillStyle = i === 0 ? (sel ? C.gold : col) : (t.emg ? C.red : C.city); ctx.fillText(l, lx + 3, ly + 12 + i * 12); });
  }
  drawScale();
}
function drawScale() {
  const nmPer80 = 80 / view.ppd * 60;
  const nice = [5, 10, 20, 25, 50, 100, 200, 250].find(v => v >= nmPer80 * .6) || 250;
  const px = nice / 60 * view.ppd;
  $("#scalebar").style.width = px + "px";
  $("#scaletxt").textContent = `${nice} NM`;
  $("#rings").textContent = T().rings;
}
function centerTxt() { $("#coords").textContent = `${view.lat.toFixed(2)}N ${view.lon.toFixed(2)}E`; }

/* pan, pinch, tap */
const pointers = new Map(); let gesture = null;
cv.addEventListener("pointerdown", e => { cv.setPointerCapture(e.pointerId); pointers.set(e.pointerId, { x: e.offsetX, y: e.offsetY });
  if (pointers.size === 1) gesture = { mode: "pan", x: e.offsetX, y: e.offsetY, lat: view.lat, lon: view.lon, moved: false };
  else if (pointers.size === 2) { const [a, b] = [...pointers.values()]; gesture = { mode: "pinch", d: Math.hypot(a.x - b.x, a.y - b.y), ppd: view.ppd, moved: true }; } });
cv.addEventListener("pointermove", e => { if (!pointers.has(e.pointerId)) return; pointers.set(e.pointerId, { x: e.offsetX, y: e.offsetY });
  if (!gesture) return;
  if (gesture.mode === "pan" && pointers.size === 1) {
    const dx = e.offsetX - gesture.x, dy = e.offsetY - gesture.y;
    if (Math.hypot(dx, dy) > 6) gesture.moved = true;
    if (gesture.moved) { view.lat = gesture.lat + dy / view.ppd; view.lon = gesture.lon - dx / (view.ppd * K()); clampView(); draw(); centerTxt(); }
  } else if (gesture.mode === "pinch" && pointers.size === 2) {
    const [a, b] = [...pointers.values()]; view.ppd = Math.max(25, Math.min(900, gesture.ppd * Math.hypot(a.x - b.x, a.y - b.y) / gesture.d)); draw();
  } });
const endPointer = e => { if (!pointers.has(e.pointerId)) return; pointers.delete(e.pointerId);
  if (gesture && gesture.mode === "pan" && !gesture.moved && pointers.size === 0) tapAt(e.offsetX, e.offsetY);
  if (pointers.size === 0) gesture = null; else if (pointers.size === 1) { const [p] = [...pointers.values()]; gesture = { mode: "pan", x: p.x, y: p.y, lat: view.lat, lon: view.lon, moved: true }; } };
cv.addEventListener("pointerup", endPointer); cv.addEventListener("pointercancel", endPointer);
cv.addEventListener("wheel", e => { e.preventDefault(); zoomAt(e.deltaY < 0 ? 1.18 : 1 / 1.18, e.offsetX, e.offsetY); }, { passive: false });
function zoomAt(f, x = W / 2, y = H / 2) {
  const [la, lo] = toLL(x, y); view.ppd = Math.max(25, Math.min(900, view.ppd * f));
  const [la2, lo2] = toLL(x, y); view.lat += la - la2; view.lon += lo - lo2; clampView(); draw(); centerTxt();
}
function clampView() { view.lat = Math.max(24, Math.min(42, view.lat)); view.lon = Math.max(34, Math.min(54, view.lon)); }
function tapAt(x, y) {
  let best = null, bd = 26;
  for (const h of hitList) { const d = Math.hypot(h.x - x, h.y - y); if (d < bd) { bd = d; best = h; } }
  state.selected = best ? best.id : null; if (best) haptic("select");
  draw(); renderPick();
}
function renderPick() {
  const el = $("#pick"); const t = state.live && state.live.targets.find(x => x.id === state.selected);
  if (!t) { el.hidden = true; return; }
  const a = ageS(t.seen);
  el.hidden = false;
  el.innerHTML = `<div class="info"><div class="cs">${esc(t.cs)}</div>
    <div class="sub">${esc([t.op, t.type, t.dep && t.arr ? `${t.dep} – ${t.arr}` : t.reg].filter(Boolean).join("   "))}</div>
    <div class="vals"><span><em>FL</em> ${fl(t.alt)}</span><span><em>GS</em> ${n0(t.gs)}</span><span><em>HDG</em> ${t.hdg == null ? "--" : String(Math.round(t.hdg)).padStart(3, "0")}</span><span><em>${esc(T().age(a))}</em></span></div></div>
    <button class="open" id="pick-open">${esc(T().open)}</button>`;
  $("#pick-open").onclick = () => openDossier(t.id);
}

/* ---------------------------------------------------------------- strips */
function stripHTML(t) {
  const a = ageS(t.seen);
  const code = t.emg ? "EMG" : t.st;
  return `<button class="strip ${esc(t.st)}${t.emg ? " emg" : ""}" data-id="${t.id}">
    <span class="code">${esc(code)}</span>
    <span class="mid"><span class="l1"><span class="cs">${esc(t.cs)}</span><span class="ty">${esc(t.type || "----")}</span></span>
      <span class="l2">${t.dep && t.arr ? `<span class="rt">${esc(t.dep)} – ${esc(t.arr)}</span>&nbsp;&nbsp;` : ""}${esc(t.op || t.reg || "")}</span></span>
    <span class="end"><b>FL${fl(t.alt)}</b><span>${n0(t.gs)} kt  ${esc(T().age(a))}</span></span></button>`;
}
function renderStrips() {
  document.querySelectorAll("#strip-seg button").forEach(b => b.setAttribute("aria-pressed", !state.results && b.dataset.f === state.filter));
  const list = $("#strip-list");
  if (state.results) {
    $("#strip-count").textContent = T().results(state.results.length);
    list.innerHTML = state.results.length ? state.results.map(stripHTML).join("") : `<div class="empty">${esc(T().noRes)}</div>`;
    return;
  }
  const all = state.live ? state.live.targets : [];
  const rows = all.filter(t => state.filter === "emg" ? t.emg : state.filter === "prm" ? t.st === "PRM" : t.st !== "PRM")
    .sort((a, b) => (b.emg - a.emg) || a.cs.localeCompare(b.cs));
  $("#strip-count").textContent = T().shown(rows.length);
  list.innerHTML = rows.length ? rows.map(stripHTML).join("") : `<div class="empty">${esc(T().noLive)}</div>`;
}

/* ---------------------------------------------------------------- dossier */
const kv = rows => `<dl class="kv">${rows.filter(r => r && r[1] != null && r[1] !== "").map(([k, v]) => `<div><dt>${esc(k)}</dt><dd>${v}</dd></div>`).join("")}</dl>`;
function altChart(track) {
  const pts = track.filter(p => p[3] != null);
  if (pts.length < 3) return "";
  const w = 600, h = 150, pl = 44, pr = 10, pt = 12, pb = 24;
  const t0 = Date.parse(pts[0][0]), t1 = Date.parse(pts[pts.length - 1][0]) || t0 + 1;
  const amax = Math.max(...pts.map(p => p[3])), top = Math.max(1000, Math.ceil(amax / 5000) * 5000);
  const X = t => pl + (w - pl - pr) * ((Date.parse(t) - t0) / Math.max(1, t1 - t0));
  const Y = a => pt + (h - pt - pb) * (1 - a / top);
  const d = pts.map((p, i) => `${i ? "L" : "M"}${X(p[0]).toFixed(1)} ${Y(p[3]).toFixed(1)}`).join("");
  const ticks = [0, top / 2, top].map(a => `<line x1="${pl}" x2="${w - pr}" y1="${Y(a)}" y2="${Y(a)}" stroke="#1F2E39"/><text x="${pl - 6}" y="${Y(a) + 4}" text-anchor="end" fill="#6A7E8B" font-size="11" font-family="IBM Plex Mono, monospace">${a ? "FL" + fl(a) : "0"}</text>`).join("");
  const xl = [pts[0], pts[pts.length - 1]].map((p, i) => `<text x="${X(p[0])}" y="${h - 6}" text-anchor="${i ? "end" : "start"}" fill="#6A7E8B" font-size="11" font-family="IBM Plex Mono, monospace">${fmtTime(p[0])}</text>`).join("");
  return `<div class="figure" id="altfig"><svg viewBox="0 0 ${w} ${h}" role="img" aria-label="${esc(T().altProfile)}">${ticks}${xl}
    <path d="${d}" fill="none" stroke="#C9A24A" stroke-width="2" stroke-linejoin="round"/>
    <line id="alt-x" y1="${pt}" y2="${h - pb}" stroke="#97A9B4" stroke-width="1" visibility="hidden"/>
    <circle id="alt-dot" r="4" fill="#E2C67C" stroke="#0F1A22" stroke-width="2" visibility="hidden"/>
    <rect x="${pl}" y="0" width="${w - pl - pr}" height="${h}" fill="transparent" id="alt-hit"/></svg><div class="tip" id="alt-tip" hidden></div></div>`;
}
function bindAltChart(track) {
  const fig = $("#altfig"); if (!fig) return;
  const pts = track.filter(p => p[3] != null), svg = fig.querySelector("svg");
  const w = 600, h = 150, pl = 44, pr = 10, pt = 12, pb = 24;
  const t0 = Date.parse(pts[0][0]), t1 = Date.parse(pts[pts.length - 1][0]) || t0 + 1;
  const top = Math.max(1000, Math.ceil(Math.max(...pts.map(p => p[3])) / 5000) * 5000);
  const move = e => {
    const r = svg.getBoundingClientRect(), vx = (e.clientX - r.left) / r.width * w;
    const tt = t0 + (vx - pl) / (w - pl - pr) * (t1 - t0);
    let best = pts[0]; for (const p of pts) if (Math.abs(Date.parse(p[0]) - tt) < Math.abs(Date.parse(best[0]) - tt)) best = p;
    const x = pl + (w - pl - pr) * ((Date.parse(best[0]) - t0) / Math.max(1, t1 - t0)), y = pt + (h - pt - pb) * (1 - best[3] / top);
    $("#alt-x").setAttribute("x1", x); $("#alt-x").setAttribute("x2", x); $("#alt-x").setAttribute("visibility", "visible");
    $("#alt-dot").setAttribute("cx", x); $("#alt-dot").setAttribute("cy", y); $("#alt-dot").setAttribute("visibility", "visible");
    const tip = $("#alt-tip"); tip.hidden = false; tip.style.left = (x / w * r.width) + "px"; tip.style.top = (y / h * r.height) + "px";
    tip.textContent = `${fmtTime(best[0])}  FL${fl(best[3])}${best[4] != null ? "  " + Math.round(best[4]) + " kt" : ""}`;
  };
  const leave = () => { $("#alt-tip").hidden = true; $("#alt-x").setAttribute("visibility", "hidden"); $("#alt-dot").setAttribute("visibility", "hidden"); };
  svg.addEventListener("pointermove", move); svg.addEventListener("pointerdown", move); svg.addEventListener("pointerleave", leave);
}
function trackMap(f) {
  const pts = f.track; if (!pts.length || !state.boot) return "";
  const lats = pts.map(p => p[1]), lons = pts.map(p => p[2]);
  let la0 = Math.min(...lats), la1 = Math.max(...lats), lo0 = Math.min(...lons), lo1 = Math.max(...lons);
  const pad = Math.max(.6, (la1 - la0) * .25, (lo1 - lo0) * .2); la0 -= pad; la1 += pad; lo0 -= pad; lo1 += pad;
  const w = 600, h = 260, k = Math.cos((la0 + la1) / 2 * Math.PI / 180);
  const s = Math.min(h / (la1 - la0), w / ((lo1 - lo0) * k));
  const cx = (lo0 + lo1) / 2, cy = (la0 + la1) / 2;
  const P = (la, lo) => [(w / 2 + (lo - cx) * s * k).toFixed(1), (h / 2 - (la - cy) * s).toFixed(1)];
  const border = state.boot.border.map(([la, lo], i) => (i ? "L" : "M") + P(la, lo).join(" ")).join("") + "Z";
  const line = pts.map((p, i) => (i ? "L" : "M") + P(p[1], p[2]).join(" ")).join("");
  const dots = pts.map(p => { const [x, y] = P(p[1], p[2]); return `<rect x="${x - 2}" y="${y - 2}" width="4" height="4" fill="${p[6] ? "#E2C67C" : "#6E8796"}"/>`; }).join("");
  const last = pts[pts.length - 1], [lx, ly] = P(last[1], last[2]);
  const cities = state.boot.cities.filter(c => c.lat > la0 && c.lat < la1 && c.lon > lo0 && c.lon < lo1)
    .map(c => { const [x, y] = P(c.lat, c.lon); return `<rect x="${x - 1.5}" y="${y - 1.5}" width="3" height="3" fill="#7D919E"/><text x="${+x + 6}" y="${+y + 4}" fill="#7D919E" font-size="12" font-family="${lang === "ar" ? "IBM Plex Sans Arabic" : "Saira Semi Condensed"}, sans-serif">${esc(lang === "ar" ? c.ar : c.en)}</text>`; }).join("");
  return `<div class="figure"><svg viewBox="0 0 ${w} ${h}" role="img" aria-label="${esc(T().trackMap)}"><rect width="${w}" height="${h}" fill="#0B131A"/>
    <path d="${border}" fill="#0F1B24" stroke="#C9A24A" stroke-width="1.2" opacity=".9"/>${cities}
    <path d="${line}" fill="none" stroke="#C9A24A" stroke-width="1.5" opacity=".55"/>${dots}
    <path transform="translate(${lx} ${ly}) rotate(${f.heading || 0}) scale(.32)" fill="#D3E6EC" d="M0-30C3-30 5-24 5-18L5-6L30 10L30 15L5 8L4 20L12 27L12 30L0 27L-12 30L-12 27L-4 20L-5 8L-30 15L-30 10L-5-6L-5-18C-5-24-3-30 0-30Z"/></svg></div>`;
}
async function openDossier(id) {
  haptic();
  state.dossierId = id;
  const d = $("#dossier"); d.hidden = false; requestAnimationFrame(() => d.classList.add("open"));
  $("#d-head").innerHTML = `<div><div class="cs">…</div></div>`; $("#d-body").innerHTML = "";
  if (ver("6.1")) { tg.BackButton.show(); }
  try { renderDossier(await api(`/api/flight/${id}`)); } catch (e) { closeDossier(); handleErr(e); }
}
function closeDossier() {
  const d = $("#dossier"); d.classList.remove("open"); state.dossierId = null;
  setTimeout(() => { if (!state.dossierId) d.hidden = true; }, 240);
  if (ver("6.1")) tg.BackButton.hide();
}
function renderDossier(f) {
  const t = T(), na = null;
  const ac = f.aircraft || {};
  const ap = (p) => ({ code: f[p + "_iata"] || f[p + "_icao"], full: [f[p + "_iata"], f[p + "_icao"]].filter(Boolean).join(" / "), city: f[p + "_city"] || f[p + "_name"], cc: f[p + "_country"] });
  const dep = ap("dep"), arr = ap("arr");
  const chipCls = f.st === "1OB" ? "OB" : f.st;
  $("#d-head").innerHTML = `<div><div class="cs">${esc(f.cs)}</div><div class="op">${esc([f.airline_name || f.airline_icao, f.flight_number_iata].filter(Boolean).join("   ") || "")}</div></div>
    <button class="close" id="d-close" aria-label="Close"><svg width="18" height="18" stroke="currentColor" fill="none" stroke-width="1.6"><use href="#i-close"/></svg></button>
    <div class="status"><span class="chip ${chipCls}">${esc(f.st)}</span><span>${esc(f.status_text)}</span></div>
    ${f.emg ? `<div class="alert">Squawk ${esc(f.squawk)}: ${esc(f.squawk_text || "")}</div>` : ""}`;
  $("#d-close").onclick = closeDossier;
  let html = "";
  // route
  if (dep.code && arr.code) {
    const pr = f.progress;
    html += `<div class="route"><div class="ap"><b>${esc(dep.code)}</b><span>${esc([dep.city, dep.cc].filter(Boolean).join(", "))}</span></div>
      <div class="track-bar">${pr ? `<div class="done" style="width:${pr.pct}%"></div><svg style="left:${pr.pct}%" viewBox="-32 -32 64 64"><path transform="rotate(90)" d="M0-30C3-30 5-24 5-18L5-6L30 10L30 15L5 8L4 20L12 27L12 30L0 27L-12 30L-12 27L-4 20L-5 8L-30 15L-30 10L-5-6L-5-18C-5-24-3-30 0-30Z"/></svg>` : ""}</div>
      <div class="ap"><b>${esc(arr.code)}</b><span>${esc([arr.city, arr.cc].filter(Boolean).join(", "))}</span></div></div>`;
    if (pr) html += kv([[t.flown, `${n0(pr.flown)} <small>NM</small>`], [t.remaining, `${n0(pr.remaining)} <small>NM</small>`],
      pr.eta ? [t.eta, `${fmtTime(pr.eta, true)} <small>${pr.pct}%</small>`] : null]);
  }
  html += `<p class="note">${esc(f.route_source ? t.routeSrc(f.route_source) : f.route_checked_utc ? t.routeNone : t.routePending)}</p>`;
  // telemetry
  html += `<h2>${esc(t.telemetry)}</h2>`;
  const vr = f.vertical_rate == null ? null : Math.abs(f.vertical_rate) < 100 ? esc(t.level) : `${f.vertical_rate > 0 ? "+" : "-"}${n0(Math.abs(f.vertical_rate))} <small>ft/min</small>`;
  html += kv([
    [t.alt, f.altitude_ft == null ? "--" : `${n0(f.altitude_ft)} <small>ft  FL${fl(f.altitude_ft)}</small>`],
    [t.gs, f.ground_speed_kt == null ? "--" : `${n0(f.ground_speed_kt)} <small>kt  ${n0(f.ground_speed_kt * 1.852)} km/h</small>`],
    [t.hdg, f.heading == null ? "--" : `${String(Math.round(f.heading)).padStart(3, "0")}° <small>${esc(f.compass || "")}</small>`],
    [t.vr, vr],
    [t.galt, f.alt_geom_ft == null ? na : `${n0(f.alt_geom_ft)} <small>ft</small>`],
    [t.sq, f.squawk ? `${esc(f.squawk)}${f.squawk_text ? ` <small>${esc(f.squawk_text)}</small>` : ""}` : na],
    [t.mach, f.mach == null ? na : f.mach.toFixed(3)],
    [t.ias, f.ias_kt == null && f.tas_kt == null ? na : `${n0(f.ias_kt)} / ${n0(f.tas_kt)} <small>kt</small>`],
    [t.selalt, f.nav_altitude_ft == null ? na : `${n0(f.nav_altitude_ft)} <small>ft</small>`],
    [t.selhdg, f.nav_heading == null ? na : `${String(Math.round(f.nav_heading)).padStart(3, "0")}°`],
    [t.wind, f.wind_dir == null || f.wind_kt == null ? na : `${String(Math.round(f.wind_dir)).padStart(3, "0")}° / ${n0(f.wind_kt)} <small>kt</small>`],
    [t.oat, f.oat_c == null ? na : `${n0(f.oat_c)} <small>°C</small>`],
    [t.pos, f.latitude == null ? na : `${f.latitude.toFixed(3)}, ${f.longitude.toFixed(3)}`],
    [t.near, f.near ? esc(f.near) : na],
    [t.src, f.pos_source ? esc(f.pos_source) : na],
    [t.seen, `${fmtTime(f.last_seen_utc, true)} <small>${esc(t.age(ageS(f.last_seen_utc)))}</small>`],
  ]);
  if (f.track && f.track.length) { html += `<h2>${esc(t.trackMap)}</h2>` + trackMap(f); }
  const prof = altChart(f.track || []); if (prof) html += `<h2>${esc(t.altProfile)}</h2>` + prof;
  // Iraq airspace
  if (f.st === "CNF" || f.st === "1OB") {
    const mins = f.obs_count >= 2 ? Math.max(1, Math.floor((Date.parse(f.last_seen_utc) - Date.parse(f.first_seen_utc)) / 60000)) : null;
    html += `<h2>${esc(t.iraqAir)}</h2>` + kv([[t.first, fmtTime(f.first_seen_utc, true)], [t.last, fmtTime(f.last_seen_utc, true)],
      [t.dur, mins ? esc(t.durVal(mins)) : esc(t.durNa)], [t.obs, n0(f.obs_count)],
      f.traffic ? [t.traffic, esc(f.traffic)] : null]);
  }
  // aircraft
  html += `<h2>${esc(t.aircraft)}</h2>` + kv([
    [t.reg, esc(f.registration || ac.registration || "--")], [t.hex, esc(f.mode_s || "--")],
    [t.type, esc(f.aircraft_type || ac.type_icao || "--")], [t.model, esc(ac.type_desc || f.aircraft_type_desc || "") || na],
    [t.maker, ac.manufacturer ? esc(ac.manufacturer) : na], [t.owner, ac.operator_name ? esc(ac.operator_name) : na],
    [t.country, ac.owner_country || f.origin_country ? esc(ac.owner_country || f.origin_country) : na],
    [t.cat, f.category ? `${esc(f.category)} <small>${esc(f.category_text || "")}</small>` : na],
  ]);
  if (f.recent && f.recent.length) {
    html += `<h2>${esc(t.recent)}</h2><div class="recent">` + f.recent.map(r => `<button data-id="${r.id}"><span class="chip ${r.st === "1OB" ? "OB" : esc(r.st)}">${esc(r.st)}</span><span><b>${esc(r.cs)}</b> <span class="rt">${esc(r.route || "")}</span></span><time>${fmtTime(r.seen, true)}</time></button>`).join("") + `</div>`;
  }
  html += `<div class="row-btns"><button class="btn ${f.watching ? "on" : "primary"}" id="d-watch">${esc(f.watching ? t.watching : t.watch)}</button>` +
    (f.latitude != null ? `<button class="btn" id="d-map">${esc(t.map)}</button>` : "") + `</div>`;
  if (ac.photo_url && /^https:\/\//.test(ac.photo_url)) html += `<div class="row-btns" style="grid-template-columns:1fr"><button class="btn" id="d-photo">${esc(t.photo)}</button></div>`;
  html += `<p class="note">${esc(t.times)}</p><div class="foot-meta">REC ${String(f.id).padStart(6, "0")}   SRC ${esc(f.data_source || "-")}   UPD ${fmtTime(f.updated_utc, true)}</div>`;
  $("#d-body").innerHTML = html; $("#d-body").scrollTop = 0;
  bindAltChart(f.track || []);
  $("#d-body").querySelectorAll(".recent button").forEach(b => b.onclick = () => openDossier(+b.dataset.id));
  $("#d-watch").onclick = async () => {
    try { const r = await api("/api/watch", { method: "POST", body: JSON.stringify({ id: f.id }) });
      f.watching = r.watching; haptic("ok"); renderDossier(f);
    } catch (e) { haptic("err"); if (e.status === 409) { if (tg && tg.showAlert && ver("6.2")) tg.showAlert(t.watchFull); } else handleErr(e); }
  };
  if ($("#d-map")) $("#d-map").onclick = () => openLink(`https://www.google.com/maps?q=${f.latitude.toFixed(4)},${f.longitude.toFixed(4)}`);
  if ($("#d-photo")) $("#d-photo").onclick = () => openLink(ac.photo_url);
}

/* ---------------------------------------------------------------- traffic */
function rankTable(rows, noCode) {
  if (!rows.length) return `<div class="empty">${esc(T().noStats)}</div>`;
  const top = rows[0].n || 1;
  return `<table class="rank"><tbody>${rows.map(r => `<tr>${noCode ? "" : `<td class="c">${esc(r.code || "--")}</td>`}<td class="nm">${esc(r.name || r.label || "")}</td><td class="b"><div class="bar-in" style="width:${Math.max(2, r.n / top * 100)}%"></div></td><td class="n">${n0(r.n)}</td></tr>`).join("")}</tbody></table>`;
}
function hourChart(hours) {
  const w = 600, h = 170, pl = 30, pr = 6, pt = 14, pb = 22, max = Math.max(1, ...hours);
  const bw = (w - pl - pr) / 24, gap = 2;
  const top = max <= 4 ? 4 : Math.ceil(max / 4) * 4;
  const Y = v => pt + (h - pt - pb) * (1 - v / top);
  const grid = [0, top / 2, top].map(v => `<line x1="${pl}" x2="${w - pr}" y1="${Y(v)}" y2="${Y(v)}" stroke="#1F2E39"/><text x="${pl - 6}" y="${Y(v) + 4}" text-anchor="end" font-size="11" fill="#6A7E8B" font-family="IBM Plex Mono, monospace">${v}</text>`).join("");
  const bars = hours.map((v, i) => { const x = pl + i * bw + gap / 2, y = Y(v), bh = (h - pb) - y;
    return `<g data-h="${i}" data-v="${v}">${v ? `<path d="M${x} ${h - pb}V${y + Math.min(4, bh)}Q${x} ${y} ${x + Math.min(4, (bw - gap) / 2)} ${y}H${x + bw - gap - Math.min(4, (bw - gap) / 2)}Q${x + bw - gap} ${y} ${x + bw - gap} ${y + Math.min(4, bh)}V${h - pb}Z" fill="#C9A24A"/>` : ""}<rect x="${x - gap / 2}" y="${pt}" width="${bw}" height="${h - pt - pb}" fill="transparent"/></g>`; }).join("");
  const xl = [0, 6, 12, 18, 23].map(i => `<text x="${pl + i * bw + bw / 2}" y="${h - 6}" text-anchor="middle" font-size="11" fill="#6A7E8B" font-family="IBM Plex Mono, monospace">${String(i).padStart(2, "0")}</text>`).join("");
  return `<div class="figure" id="hourfig" style="direction:ltr"><svg viewBox="0 0 ${w} ${h}" role="img" aria-label="hourly">${grid}${bars}${xl}</svg><div class="tip" hidden></div></div>`;
}
async function loadTraffic() {
  const el = $("#traffic"), t = T();
  const periods = [1, 7, 30, 0];
  el.innerHTML = `<div class="seg" id="per">${periods.map((p, i) => `<button data-p="${p}" aria-pressed="${state.period === p}">${esc(t.period[i])}</button>`).join("")}</div><div id="tr-body"><p class="count">…</p></div><div class="credit-space"></div>`;
  el.querySelectorAll("#per button").forEach(b => b.onclick = () => { state.period = +b.dataset.p; haptic("select"); loadTraffic(); });
  let s; try { s = await api(`/api/stats?days=${state.period}`); } catch (e) { return handleErr(e); }
  const pct = (a) => s.confirmed ? Math.round(100 * a / s.confirmed) + "%" : "--";
  let html = `<div class="tiles"><div class="lead"><b>${n0(s.confirmed)}</b><span>${esc(t.confirmed)}</span></div><div><b>${n0(s.single)}</b><span>${esc(t.single)}</span></div>
    <div><b>${n0(s.airlines)}</b><span>${esc(t.ops)}</span></div><div><b>${n0(s.types)}</b><span>${esc(t.types)}</span></div></div>`;
  if (s.confirmed) {
    html += `<h2>${esc(t.hourly(state.boot.tz))}</h2>` + hourChart(s.hours);
    html += `<h2>${esc(t.mix)}</h2>` + rankTable(s.mix.map(m => ({ label: m.label, n: m.n })), true);
    html += `<h2>${esc(t.topOps)}</h2>` + rankTable(s.top_airlines) + `<h2>${esc(t.topTypes)}</h2>` + rankTable(s.top_types);
    html += `<h2>${esc(t.topDep)}</h2>` + rankTable(s.top_dep) + `<h2>${esc(t.topArr)}</h2>` + rankTable(s.top_arr);
    html += `<h2>${esc(t.avgAlt)}</h2>` + kv([[t.avgAlt, s.avg_alt == null ? "--" : `${n0(s.avg_alt)} <small>ft</small>`], [t.avgGs, s.avg_gs == null ? "--" : `${n0(s.avg_gs)} <small>kt</small>`],
      [t.complete, `${esc(t.fAirline)} ${pct(s.complete.airline)}`], ["", `${esc(t.fType)} ${pct(s.complete.type)}  ${esc(t.fRoute)} ${pct(s.complete.route)}`]]);
  } else html += `<div class="empty" style="margin-top:14px">${esc(t.noStats)}</div>`;
  if (s.coverage) html += `<p class="note">${esc(t.coverage(fmtTime(s.coverage, true).split(",")[0]))}</p>`;
  $("#tr-body").innerHTML = html;
  const fig = $("#hourfig");
  if (fig) { const tip = fig.querySelector(".tip"), svg = fig.querySelector("svg");
    fig.querySelectorAll("g[data-h]").forEach(g => { const on = () => { const r = svg.getBoundingClientRect(), bb = g.getBBox();
      tip.hidden = false; tip.style.left = ((bb.x + bb.width / 2) / 600 * r.width) + "px"; tip.style.top = "26px";
      tip.textContent = `${String(g.dataset.h).padStart(2, "0")}:00  ${g.dataset.v}`; };
      g.addEventListener("pointerenter", on); g.addEventListener("pointerdown", on); });
    svg.addEventListener("pointerleave", () => tip.hidden = true); }
}

/* ---------------------------------------------------------------- system */
async function loadSystem() {
  const el = $("#system"), t = T();
  let s; try { s = await api("/api/system"); } catch (e) { return handleErr(e); }
  const up = s.uptime_s, upTxt = `${Math.floor(up / 86400)}d ${Math.floor(up % 86400 / 3600)}h ${Math.floor(up % 3600 / 60)}m`;
  let html = kv([[t.feed, `<span class="${s.feed === "OK" ? "ok" : "bad"}">${esc(s.feed || "--")}</span>`], [t.version, esc(s.version)],
    [t.uptime, upTxt], [t.interval, `${s.interval} <small>s</small>`], [t.next, s.next ? fmtTime(s.next) : "--"],
    [t.sources, esc(String(s.sources.length))], [t.stored, n0(s.flights)], [t.points, n0(s.points)]]);
  if (s.feeds.length) html += `<h2>${esc(t.feeds)}</h2><table class="log"><tbody>${s.feeds.map(x => `<tr><td>${esc(x)}</td></tr>`).join("")}</tbody></table>`;
  html += `<h2>${esc(t.log)}</h2><table class="log"><thead><tr><th>${esc(t.time)}</th><th>${esc(t.status)}</th><th class="r">${esc(t.recv)}</th><th class="r">${esc(t.inIraq)}</th><th class="r">${esc(t.around)}</th></tr></thead><tbody>` +
    s.log.map(r => `<tr><td>${fmtTime(r.t)}</td><td class="${r.status === "OK" ? "ok" : "bad"}">${esc(r.status)}</td><td class="r">${r.recv}</td><td class="r">${r.iraq}</td><td class="r">${r.around}</td></tr>`).join("") + `</tbody></table>`;
  if (s.admin) html += `<h2>${esc(t.admin)}</h2>` + kv([[t.users, n0(s.admin.users)], [t.subCheck, `<span class="${s.admin.sub_check === "OK" ? "ok" : "bad"}">${esc(s.admin.sub_check)}</span>`],
    [t.lookups, n0(s.admin.lookups)], ["", esc(s.admin.lookup_error || "")]]);
  html += `<div class="links"><button class="btn" id="s-ch">${esc(t.channel)}  @${esc(state.boot.channel)}</button><button class="btn" id="s-dev">${esc(t.dev)}  @${esc(state.boot.dev)}</button></div>`;
  el.innerHTML = html;
  $("#s-ch").onclick = () => openTg(`https://t.me/${state.boot.channel}`);
  $("#s-dev").onclick = () => openTg(`https://t.me/${state.boot.dev}`);
}

/* ---------------------------------------------------------------- start */
let pollTimer = null, tickTimer = null;
async function start() {
  setLang(lang);
  if (!tg || !tg.initData) { gate("notg"); return; }
  try {
    tg.ready(); tg.expand();
    if (ver("6.1")) { tg.setHeaderColor("#0B131A"); tg.setBackgroundColor("#0B131A"); tg.BackButton.onClick(closeDossier); }
    if (ver("7.10")) tg.setBottomBarColor("#0F1A22");
    if (ver("7.7")) tg.disableVerticalSwipes();
  } catch (e) {}
  gate("boot", 0);
  try {
    state.boot = await api("/api/bootstrap");
    setLang(state.boot.lang); gate("boot", 1);
    state.live = await api("/api/live"); gate("boot", 2);
  } catch (e) { return handleErr(e); }
  applyStatic();
  $("#gate").hidden = true; $("#app").hidden = false;
  show(state.view); tick(); centerTxt();
  clearInterval(pollTimer); clearInterval(tickTimer);
  pollTimer = setInterval(() => { if (!document.hidden && (state.view === "scope" || state.view === "strips")) loadLive(); }, 20000);
  tickTimer = setInterval(() => { tick(); if (!document.hidden && state.view === "scope") draw(); }, 1000);
}
document.querySelectorAll("nav button").forEach(b => b.onclick = () => { haptic("select"); show(b.dataset.v); });
$("#ly-iraq").onclick = e => { state.layers.iraq = !state.layers.iraq; e.currentTarget.setAttribute("aria-pressed", state.layers.iraq); draw(); };
$("#ly-prm").onclick = e => { state.layers.prm = !state.layers.prm; e.currentTarget.setAttribute("aria-pressed", state.layers.prm); draw(); };
$("#zin").onclick = () => zoomAt(1.4); $("#zout").onclick = () => zoomAt(1 / 1.4);
$("#zfit").onclick = () => { fit(); draw(); centerTxt(); };
$("#zlbl").onclick = e => { state.labels = !state.labels; e.currentTarget.setAttribute("aria-pressed", state.labels); draw(); };
$("#strip-seg").addEventListener("click", e => { const b = e.target.closest("button"); if (!b) return; state.filter = b.dataset.f; state.results = null; $("#q").value = ""; haptic("select"); renderStrips(); });
$("#strip-list").addEventListener("click", e => { const b = e.target.closest(".strip"); if (b) openDossier(+b.dataset.id); });
$("#search-form").addEventListener("submit", async e => {
  e.preventDefault(); const q = $("#q").value.trim(); $("#q").blur();
  if (q.length < 2) { state.results = null; renderStrips(); return; }
  $("#strip-count").textContent = T().searching;
  try { state.results = (await api(`/api/search?q=${encodeURIComponent(q)}`)).results; renderStrips(); } catch (err) { handleErr(err); }
});
window.addEventListener("resize", () => { if (state.view === "scope") resize(); });
document.addEventListener("visibilitychange", () => { if (!document.hidden && state.boot) loadLive(); });
document.addEventListener("keydown", e => { if (e.key === "Escape" && state.dossierId) closeDossier(); });
start();
</script>
</body>
</html>
"""

if __name__ == "__main__":
    sys.exit(asyncio.run(amain()))
