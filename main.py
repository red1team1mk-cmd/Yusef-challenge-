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
"""
from __future__ import annotations

import asyncio
import csv
import fcntl
import html
import io
import json
import logging
import os
import platform
import random
import re
import signal
import sqlite3
import sys
import time
from datetime import datetime, timedelta, timezone
from typing import Any, Optional
from zoneinfo import ZoneInfo

import aiosqlite
import httpx
from telegram import (
    BotCommand,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest, Conflict, RetryAfter, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
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
}
# Three 250 NM circles (the maximum radius the feeds allow) that together cover Iraq.
QUERY_RADIUS_NM = 250
QUERY_CIRCLES = [(33.0, 41.6), (35.2, 44.6), (31.2, 46.0)]
MAX_POSITION_AGE = 300  # seconds; older positions are ignored. Each position is
                        # stored with its own true timestamp (feed time - age).
APP_NAME = "IRAQ AIR TRAFFIC MONITOR"
APP_VERSION = "2.3.0"

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
        raw = os.getenv("ADSB_PROVIDERS", "").strip() or "adsbfi,adsblol,airplaneslive"
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

    async def snapshot(self) -> tuple[list[dict], str, str]:
        """Current aircraft around Iraq, merged from every configured provider so
        that one feed's coverage gaps are filled by the others.
        Returns (records, providers that answered, per-provider note)."""
        merged: dict[str, dict] = {}
        notes: list[str] = []
        errors: list[str] = []
        answered: list[str] = []
        for provider in self.providers:
            name = PROVIDERS[provider][0]
            try:
                records, raw_count = await self._snapshot_from(provider)
            except ApiError as exc:
                errors.append(f"{name}: {exc}")
                notes.append(f"{name} ERR {str(exc)[:60]}")
                log.warning("feed failed", extra={"data": {"provider": provider, "error": str(exc)}})
                continue
            answered.append(name)
            notes.append(f"{name} {len(records)}/{raw_count}")
            for record in records:
                key = record["aircraftModeS"] or record["aircraftRegistration"] or record["callsign"]
                if key not in merged or record["updated"] > merged[key]["updated"]:
                    merged[key] = record
        if not answered:
            self.last_error = "; ".join(errors)[:300]
            if errors and all("429" in e for e in errors):
                raise ApiRateLimited(self.last_error)
            raise ApiError(self.last_error)
        self.last_ok = now_utc()
        self.last_error = "; ".join(errors)[:300] or None
        self.last_provider = ", ".join(answered)
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
              "dep_city", "dep_country", "arr_icao", "arr_iata", "arr_name", "arr_city", "arr_country"]


class Enricher:
    """Looks up the usual route of a callsign and the registry details of an
    aircraft.  Every answer (including "unknown") is cached in SQLite, so each
    callsign/aircraft costs at most one lookup per cache period."""
    ADSBDB = "https://api.adsbdb.com/v0"
    HEXDB = "https://hexdb.io/api/v1"
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
        self.paused_until: Optional[datetime] = None
        self.lookups = 0
        self.last_error: Optional[str] = None

    async def close(self) -> None:
        await self._client.aclose()

    async def _get(self, url: str) -> tuple[int, Any]:
        """One polite request. Returns (status, json-or-None); 0 = network failure."""
        if self.paused_until and now_utc() < self.paused_until:
            return 0, None
        async with self._gate:
            wait = 1.0 - (time.monotonic() - self._last_request)
            if wait > 0:
                await asyncio.sleep(wait)
            try:
                resp = await self._client.get(url)
            except (httpx.TimeoutException, httpx.TransportError) as exc:
                self.last_error = f"network error: {type(exc).__name__}"
                return 0, None
            finally:
                self._last_request = time.monotonic()
        self.lookups += 1
        if resp.status_code == 429 or resp.status_code >= 500:
            # Back off for a while instead of pressing a busy or limiting service.
            self.paused_until = now_utc() + timedelta(minutes=15)
            self.last_error = f"lookup service HTTP {resp.status_code}; paused 15 min"
            return resp.status_code, None
        try:
            return resp.status_code, resp.json()
        except ValueError:
            return resp.status_code, None

    @staticmethod
    def _airport(a: Any, prefix: str) -> dict:
        a = a if isinstance(a, dict) else {}
        country = clean_str(a.get("country_iso_name"))
        return {f"{prefix}_icao": clean_str(a.get("icao_code")), f"{prefix}_iata": clean_str(a.get("iata_code")),
                f"{prefix}_name": clean_str(a.get("name")), f"{prefix}_city": clean_str(a.get("municipality")),
                f"{prefix}_country": country.upper() if country else None}

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
        if not route_done:
            status, data = await self._get(f"{self.ADSBDB}/callsign/{callsign}")
            resp = data.get("response") if isinstance(data, dict) else None
            if status == 200 and isinstance(resp, dict):
                route = self._parse_route(resp.get("flightroute"))
            asked = status in (200, 404)
            if route is None:
                status, data = await self._get(f"{self.HEXDB}/route/icao/{callsign}")
                text = clean_str(data.get("route")) if isinstance(data, dict) else None
                if status == 200 and text and text.count("-") >= 1:
                    parts = [x.strip().upper() for x in text.split("-") if x.strip()]
                    if len(parts) >= 2:
                        route = {c: None for c in ROUTE_COLS}
                        route.update({"dep_icao": parts[0], "arr_icao": parts[-1], "source": "hexdb"})
                asked = asked or status in (200, 404)
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
            "WHERE f.crossing_status<>'NEARBY' AND f.last_seen_utc>=? AND "
            "(f.route_checked_utc IS NULL OR "
            " (a.key IS NOT NULL AND a.detail_fetched_utc IS NULL)) "
            "ORDER BY f.last_seen_utc DESC LIMIT ?",
            (iso(now_utc() - timedelta(hours=6)), limit))
        done = 0
        for r in rows:
            if stop.is_set() or (self.paused_until and now_utc() < self.paused_until):
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
                              ("aircraft", "photo_url TEXT")):
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
               "skipped": 0, "no_evidence": 0}
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
        if source == "LIVE":
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
            # Never observed inside Iraq: keep as NEARBY, spanning all its positions.
            zone, crossing, pos_filter = "NEARBY", "NEARBY", ""
            async with self.conn.execute(
                "SELECT MIN(ts_utc), MAX(ts_utc) FROM track_observations WHERE flight_id=?",
                (flight_id,)) as cur:
                first, last = await cur.fetchone()
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
            "DELETE FROM flights WHERE crossing_status='NEARBY' AND last_seen_utc<?", (near_cut,))
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
                    done = await self.enricher.background(40, self.stop)
                    if done:
                        ev("enrichment", flights=done, lookups_total=self.enricher.lookups)
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
# TELEGRAM PRESENTATION HELPERS
# --------------------------------------------------------------------------
class Ctx:
    """Shared runtime objects (set in main())."""
    cfg: Config
    db: Database
    api: AdsbClient
    enrich: Enricher
    sync: SyncService
    started: datetime


def esc(value: Any) -> str:
    return html.escape(str(value), quote=False)


def pre(lines: list[str]) -> str:
    text = "\n".join(lines)
    if len(text) > 3900:
        text = text[:3900] + "\n… (truncated)"
    return f"<pre>{esc(text)}</pre>"


def local(iso_value: Optional[str], fmt: str = "%d %b %H:%M") -> str:
    dt = parse_dt(iso_value)
    return dt.astimezone(Ctx.cfg.tz).strftime(fmt) if dt else NA


def val(value: Any, suffix: str = "") -> str:
    if value is None or value == "":
        return NA
    if isinstance(value, float):
        value = int(round(value))
    return f"{value}{suffix}"


def ago(iso_value: Optional[str]) -> str:
    dt = parse_dt(iso_value)
    if not dt:
        return NA
    secs = int((now_utc() - dt).total_seconds())
    if secs < 90:
        return f"{secs}s ago"
    if secs < 5400:
        return f"{secs // 60}m ago"
    if secs < 172800:
        return f"{secs // 3600}h ago"
    return f"{secs // 86400}d ago"


def header(title: str) -> list[str]:
    return [SEP, f" ✈ {title}", SEP]


def is_admin(update: Update) -> bool:
    user = update.effective_user
    return bool(user and user.id in Ctx.cfg.admin_ids)


def btn(text: str, data: str) -> InlineKeyboardButton:
    return InlineKeyboardButton(text, callback_data=data)


def menu_row() -> list[InlineKeyboardButton]:
    return [btn("⌂ MAIN MENU", "M|main")]


def main_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [btn("[ LAST 24 HOURS ]", "L|24h|-|0")],
        [btn("[ LIVE AIRCRAFT ]", "L|live|-|0")],
        [btn("[ AROUND IRAQ ]", "L|near|-|0")],
        [btn("[ SEARCH FLIGHT ]", "M|search")],
        [btn("[ AIRLINES ]", "AL|0"), btn("[ AIRCRAFT ]", "AC|0")],
        [btn("[ STATISTICS ]", "S|1")],
        [btn("[ FLIGHT ARCHIVE ]", "M|archive")],
        [btn("[ SYSTEM STATUS ]", "M|status")],
    ])


async def respond(update: Update, text: str, kb: Optional[InlineKeyboardMarkup] = None) -> None:
    query = update.callback_query
    try:
        if query and query.message:
            await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        elif update.effective_message:
            await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    except BadRequest as exc:
        if "not modified" in str(exc).lower():
            return
        if update.effective_chat:
            await update.get_bot().send_message(
                update.effective_chat.id, text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def data_age_line() -> str:
    last = await Ctx.db.scalar("SELECT MAX(finished_utc) FROM sync_history WHERE status='OK'")
    if not last:
        return "DATA: no successful sync yet"
    stale = (now_utc() - parse_dt(last)).total_seconds() > 3 * Ctx.cfg.sync_interval  # type: ignore[operator]
    return f"DATA: synced {ago(last)}" + ("  ⚠ STALE" if stale else "")


async def source_line() -> str:
    provider = await Ctx.db.get_status("provider")
    return f"SOURCE: {provider or 'none yet'}"


def route(row: sqlite3.Row) -> str:
    dep = row["dep_iata"] or row["dep_icao"]
    arr = row["arr_iata"] or row["arr_icao"]
    return f"{dep}→{arr}" if dep and arr else (row["registration"] or "")


def ident(row: sqlite3.Row) -> str:
    return row["callsign"] or row["flight_number_icao"] or row["registration"] or row["mode_s"] or "UNKNOWN"


# --------------------------------------------------------------------------
# VIEWS
# --------------------------------------------------------------------------
async def view_main(update: Update) -> None:
    total = await Ctx.db.scalar("SELECT COUNT(*) FROM flights WHERE crossing_status='CONFIRMED'") or 0
    live_cut = iso(now_utc() - timedelta(seconds=max(600, 2 * Ctx.cfg.sync_interval)))
    live = await Ctx.db.scalar(
        "SELECT COUNT(*) FROM flights WHERE last_seen_utc>=? AND crossing_status<>'NEARBY'", (live_cut,)) or 0
    near = await Ctx.db.scalar(
        "SELECT COUNT(*) FROM flights WHERE last_seen_utc>=? AND crossing_status='NEARBY'",
        (live_cut,)) or 0
    lines = header(APP_NAME) + [
        "AIRSPACE  IRAQ / ORBB FIR",
        f"TIME      {now_utc().astimezone(Ctx.cfg.tz).strftime('%d %b %Y %H:%M')}",
        f"ZONE      {Ctx.cfg.tz_name}",
        SUB,
        f"IN AIRSPACE NOW   {live}",
        f"AROUND IRAQ NOW   {near}",
        f"CROSSINGS LOGGED  {total}",
        await data_age_line(),
        await source_line(),
        SUB,
        "SELECT A MODULE ▼",
    ]
    await respond(update, pre(lines), main_menu_kb())


def like_escape(text: str) -> str:
    return text.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


SEARCH_COLS = ["callsign", "flight_number_iata", "flight_number_icao", "registration", "mode_s",
               "airline_name", "airline_icao", "airline_iata", "aircraft_type", "aircraft_type_desc",
               "dep_icao", "dep_iata", "dep_city", "dep_name", "arr_icao", "arr_iata", "arr_city",
               "arr_name"]


def list_filter(kind: str, arg: str, user_data: dict) -> tuple[str, str, tuple]:
    """Return (title, where-clause, args) for a flight list context."""
    now = now_utc()
    if kind == "24h":
        return "LAST 24 HOURS", "last_seen_utc>=? AND crossing_status<>'NEARBY'", (iso(now - timedelta(hours=24)),)
    if kind == "live":
        window = max(600, 2 * Ctx.cfg.sync_interval)
        return "LIVE AIRCRAFT", "last_seen_utc>=? AND crossing_status<>'NEARBY'", (iso(now - timedelta(seconds=window)),)
    if kind == "near":
        window = max(600, 2 * Ctx.cfg.sync_interval)
        return ("AROUND IRAQ · LIVE", "last_seen_utc>=? AND crossing_status='NEARBY'",
                (iso(now - timedelta(seconds=window)),))
    if kind == "ar":
        if arg == "c":
            rng = user_data.get("range")
            if not rng:
                return "ARCHIVE", "0", ()
            return (f"ARCHIVE {rng[2]}", "last_seen_utc>=? AND first_seen_utc<? AND crossing_status<>'NEARBY'",
                    (rng[0], rng[1]))
        days = int(arg)
        label = "24 HOURS" if days == 1 else f"{days} DAYS"
        return f"ARCHIVE · {label}", "last_seen_utc>=? AND crossing_status<>'NEARBY'", (iso(now - timedelta(days=days)),)
    if kind == "al":
        if arg == "-":
            return "AIRLINE · UNKNOWN", "airline_icao IS NULL AND crossing_status<>'NEARBY'", ()
        return f"AIRLINE · {arg}", "airline_icao=? AND crossing_status<>'NEARBY'", (arg,)
    if kind == "ac":
        if arg == "-":
            return "TYPE · UNKNOWN", "aircraft_type IS NULL AND crossing_status<>'NEARBY'", ()
        return f"TYPE · {arg}", "aircraft_type=? AND crossing_status<>'NEARBY'", (arg,)
    if kind == "s":
        query = (user_data.get("query") or "").strip()
        if not query:
            return "SEARCH", "0", ()
        pattern = f"%{like_escape(query.upper())}%"
        where = " OR ".join(f"UPPER({c}) LIKE ? ESCAPE '\\'" for c in SEARCH_COLS)
        return f"SEARCH · {query[:14].upper()}", f"({where})", tuple([pattern] * len(SEARCH_COLS))
    return "FLIGHTS", "0", ()


async def view_list(update: Update, context: ContextTypes.DEFAULT_TYPE, kind: str, arg: str,
                    page: int) -> None:
    title, where, args = list_filter(kind, arg, context.user_data)
    total = await Ctx.db.scalar(f"SELECT COUNT(*) FROM flights WHERE {where}", args) or 0
    pages = max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, pages - 1))
    rows = await Ctx.db.q(
        f"SELECT * FROM flights WHERE {where} ORDER BY last_seen_utc DESC LIMIT ? OFFSET ?",
        (*args, PAGE_SIZE, page * PAGE_SIZE))
    context.user_data["back"] = f"L|{kind}|{arg}|{page}"

    lines = header(title) + [f"RECORDS {total}   PAGE {page + 1}/{pages}", await data_age_line(), SUB]
    if not rows:
        lines.append("NO RECORDS FOR THIS VIEW.")
        if kind in ("live", "near"):
            lines.append("No aircraft observed in this")
            lines.append("zone in the last sync.")
    buttons: list[list[InlineKeyboardButton]] = []
    row_buf: list[InlineKeyboardButton] = []
    for i, r in enumerate(rows, start=page * PAGE_SIZE + 1):
        mark = {"CONFIRMED": "✓", "NEARBY": "○"}.get(r["crossing_status"], "?")
        lines.append(f"{i:02d} {ident(r):<8} {r['aircraft_type'] or '----':<4} {route(r)}")
        alt = f"{int(r['altitude_ft']):>5}ft" if r["altitude_ft"] is not None else "   N/A "
        lines.append(f"   {alt} {local(r['last_seen_utc'], '%d%b %H:%M')} {mark}")
        row_buf.append(btn(f"{i:02d} {ident(r)}", f"F|{r['id']}"))
        if len(row_buf) == 2:
            buttons.append(row_buf)
            row_buf = []
    if row_buf:
        buttons.append(row_buf)
    if rows:
        lines += [SUB, "✓ crossed Iraq  ? one position", "○ around Iraq only (not inside)"]
    nav: list[InlineKeyboardButton] = []
    if page > 0:
        nav.append(btn("◀ PREV", f"L|{kind}|{arg}|{page - 1}"))
    nav.append(btn("⟳ REFRESH", f"L|{kind}|{arg}|{page}"))
    if page < pages - 1:
        nav.append(btn("NEXT ▶", f"L|{kind}|{arg}|{page + 1}"))
    buttons.append(nav)
    if kind == "ar" and is_admin(update) and arg != "c":
        buttons.append([btn("⬇ EXPORT CSV", f"X|{arg}")])
    buttons.append(menu_row())
    await respond(update, pre(lines), InlineKeyboardMarkup(buttons))


async def view_flight(update: Update, context: ContextTypes.DEFAULT_TYPE, flight_id: int) -> None:
    await Ctx.enrich.enrich(flight_id)  # cached after the first time
    r = await Ctx.db.one("SELECT * FROM flights WHERE id=?", (flight_id,))
    if not r:
        await respond(update, pre(header("FLIGHT") + ["RECORD NOT FOUND."]),
                      InlineKeyboardMarkup([menu_row()]))
        return

    def airport(prefix: str) -> str:
        parts = [r[f"{prefix}_icao"], r[f"{prefix}_iata"], r[f"{prefix}_city"] or r[f"{prefix}_name"]]
        parts = [p for p in parts if p]
        text = " ".join(parts)[:22] if parts else NA
        return f"{text} {r[f'{prefix}_country']}" if parts and r[f"{prefix}_country"] else text

    def when(prefix: str) -> str:
        if not r[f"{prefix}_time_utc"]:
            return NA
        return f"{local(r[f'{prefix}_time_utc'])} {r[f'{prefix}_time_kind'][:3]}"

    numbers = " / ".join(x for x in (r["flight_number_iata"], r["flight_number_icao"]) if x) or NA
    if r["airline_name"]:
        airline = f"{r['airline_name']} ({r['airline_icao'] or r['airline_iata'] or '?'})"
    else:
        airline = f"{r['airline_icao']} (from callsign)" if r["airline_icao"] else NA
    if r["route_source"]:
        route_note = [f"ROUTE SRC {r['route_source']} (by callsign)", " usual route, not a live plan"]
    elif r["route_checked_utc"]:
        route_note = ["ROUTE     not in route database"]
    else:
        route_note = ["ROUTE     not looked up (no", " airline callsign / service busy)"]
    model = " ".join(x for x in (r["aircraft_type"], r["aircraft_type_desc"]) if x) or NA
    first, last = parse_dt(r["first_seen_utc"]), parse_dt(r["last_seen_utc"])
    if r["obs_count"] >= 2 and first and last:
        duration = f"≥ {max(1, int((last - first).total_seconds() // 60))} min (observed)"
    else:
        duration = "N/A (needs 2+ obs)"
    nearby = r["crossing_status"] == "NEARBY"
    crossing = {"CONFIRMED": "CONFIRMED CROSSING", "NEARBY": "NOT IN IRAQ (NEARBY)"}.get(
        r["crossing_status"], "UNCONFIRMED (1 OBS)")
    pos = (f"{abs(r['latitude']):.2f}{'N' if r['latitude'] >= 0 else 'S'} "
           f"{abs(r['longitude']):.2f}{'E' if r['longitude'] >= 0 else 'W'}"
           if r["latitude"] is not None else NA)
    lines = header(f"FLIGHT {ident(r)}") + [
        f"CALLSIGN  {val(r['callsign'])}",
        f"FLIGHT NO {numbers}",
        f"AIRLINE   {airline[:26]}",
        f"AIRCRAFT  {model[:26]}",
        f"REG       {val(r['registration'])}",
        f"ICAO24    {val(r['mode_s'])}",
        SUB,
        f"FROM  {airport('dep')}",
        f"TO    {airport('arr')}",
        *route_note,
        f"TRAFFIC   {r['traffic_type']}",
        "DEP/ARR TIMES  N/A (no source)",
        SUB + ("\n AROUND IRAQ (OUTSIDE BORDER)" if nearby else "\n IRAQ AIRSPACE"),
        f"FIRST OBS {local(r['first_seen_utc'])}",
        f"LAST OBS  {local(r['last_seen_utc'])}",
        f"DURATION  {duration}",
        f"OBS COUNT {r['obs_count']}",
        f"STATUS    {crossing}",
        f"CLASS     {val(r['aircraft_classes'])}",
        SUB + ("\n LAST POSITION" if nearby else "\n LAST POSITION OVER IRAQ"),
        f"ALT   {val(r['altitude_ft'], ' ft')}",
        f"GS    {val(r['ground_speed_kt'], ' kt')}",
        f"HDG   {val(r['heading'], '°')}",
        f"POS   {pos}",
        SUB,
        f"Times in {Ctx.cfg.tz_name}. N/A = not",
        "provided by the data source.",
    ]
    back = context.user_data.get("back")
    kb = [
        [btn("⌖ TRACK", f"T|{flight_id}|0"), btn("✈ AIRCRAFT INFO", f"A|{flight_id}")],
        *([[InlineKeyboardButton(
            "🗺 OPEN LAST POSITION ON MAP",
            url=f"https://www.google.com/maps?q={r['latitude']:.4f},{r['longitude']:.4f}")]]
          if r["latitude"] is not None else []),
        [btn("⟳ REFRESH", f"F|{flight_id}")] + ([btn("◀ BACK", back)] if back else []),
        menu_row(),
    ]
    await respond(update, pre(lines), InlineKeyboardMarkup(kb))


async def view_track(update: Update, flight_id: int, page: int) -> None:
    r = await Ctx.db.one("SELECT * FROM flights WHERE id=?", (flight_id,))
    if not r:
        await respond(update, pre(["RECORD NOT FOUND."]), InlineKeyboardMarkup([menu_row()]))
        return
    per = 14
    total = await Ctx.db.scalar(
        "SELECT COUNT(*) FROM track_observations WHERE flight_id=?", (flight_id,)) or 0
    pages = max(1, (total + per - 1) // per)
    page = max(0, min(page, pages - 1))
    obs = await Ctx.db.q(
        "SELECT * FROM track_observations WHERE flight_id=? ORDER BY ts_utc LIMIT ? OFFSET ?",
        (flight_id, per, page * per))
    lines = header(f"TRACK {ident(r)}") + [f"POINTS {total}   PAGE {page + 1}/{pages}", SUB]
    if not obs:
        lines += ["TRACK NOT AVAILABLE.", "No stored observations (not",
                  "provided, or past retention)."]
    else:
        lines.append("TIME   LAT    LON    FL  GS")
        for o in obs:
            fl = f"{int(o['altitude_ft'] // 100):03d}" if o["altitude_ft"] is not None else "---"
            gs = f"{int(o['ground_speed_kt']):3d}" if o["ground_speed_kt"] is not None else "---"
            flag = " " if o["in_iraq"] else "·"
            lines.append(f"{local(o['ts_utc'], '%H:%M')}{flag} {o['latitude']:5.2f} "
                         f"{o['longitude']:5.2f} {fl} {gs}")
        lines += [SUB, "· = outside Iraq boundary"]
    nav = []
    if page > 0:
        nav.append(btn("◀ PREV", f"T|{flight_id}|{page - 1}"))
    if page < pages - 1:
        nav.append(btn("NEXT ▶", f"T|{flight_id}|{page + 1}"))
    kb = ([nav] if nav else []) + [[btn("◀ FLIGHT", f"F|{flight_id}")], menu_row()]
    await respond(update, pre(lines), InlineKeyboardMarkup(kb))


async def view_aircraft_info(update: Update, flight_id: int) -> None:
    r = await Ctx.db.one("SELECT * FROM flights WHERE id=?", (flight_id,))
    kb = InlineKeyboardMarkup([[btn("◀ FLIGHT", f"F|{flight_id}")], menu_row()])
    if not r or not (r["registration"] or r["mode_s"]):
        await respond(update, pre(header("AIRCRAFT") + [
            "NO REGISTRATION OR ICAO24 ON", "RECORD. DETAILS UNAVAILABLE."]), kb)
        return
    key = r["registration"] or r["mode_s"]
    await Ctx.enrich.enrich(flight_id)
    ac = await Ctx.db.one("SELECT * FROM aircraft WHERE key=?", (key,))
    lines = header(f"AIRCRAFT {key}")
    if ac:
        if ac["photo_url"] and ac["photo_url"].startswith("https://"):
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("📷 AIRCRAFT PHOTO", url=ac["photo_url"])],
                                       [btn("◀ FLIGHT", f"F|{flight_id}")], menu_row()])
        lines += [
            f"REG       {val(ac['registration'])}",
            f"ICAO24    {val(ac['mode_s'])}",
            f"TYPE      {val(ac['type_icao'])}",
            f"MODEL     {val(ac['type_desc'])[:24]}",
            f"MAKER     {val(ac['manufacturer'])[:24]}",
            f"OWNER/OPR {val(ac['operator_name'])[:24]}",
            f"REG. IN   {val(ac['owner_country'])[:24]}",
            f"CLASS     {val(r['aircraft_classes'])}",
            SUB,
            f"FIRST SEEN {local(ac['first_seen_utc'], '%d %b %Y')}",
            f"LAST SEEN  {local(ac['last_seen_utc'], '%d %b %Y %H:%M')}",
        ]
        seen = await Ctx.db.scalar(
            "SELECT COUNT(*) FROM flights WHERE registration=? OR mode_s=?",
            (ac["registration"] or "-", ac["mode_s"] or "-"))
        lines += [f"RECORDS    {seen} in archive", SUB,
                  "From ADS-B feed + adsbdb registry.", "N/A = not provided."]
    else:
        lines.append("NO STORED AIRCRAFT DATA.")
    await respond(update, pre(lines), kb)


async def view_group(update: Update, context: ContextTypes.DEFAULT_TYPE, mode: str, page: int) -> None:
    """Airlines (mode AL) or aircraft types (mode AC) ranked by recorded flights."""
    if mode == "AL":
        col, title, kind = "airline_icao", "AIRLINES", "al"
        name_sql = "MAX(airline_name)"
    else:
        col, title, kind = "aircraft_type", "AIRCRAFT TYPES", "ac"
        name_sql = "MAX(aircraft_type_desc)"
    per = 10
    total = await Ctx.db.scalar(
        f"SELECT COUNT(DISTINCT COALESCE({col}, '-')) FROM flights WHERE crossing_status<>'NEARBY'") or 0
    pages = max(1, (total + per - 1) // per)
    page = max(0, min(page, pages - 1))
    rows = await Ctx.db.q(
        f"SELECT COALESCE({col}, '-') AS code, {name_sql} AS name, COUNT(*) AS n FROM flights "
        f"WHERE crossing_status<>'NEARBY' GROUP BY code ORDER BY n DESC, code LIMIT ? OFFSET ?", (per, page * per))
    lines = header(title) + [f"DISTINCT {total}   PAGE {page + 1}/{pages}", "FLIGHTS SEEN INSIDE IRAQ", SUB]
    buttons: list[list[InlineKeyboardButton]] = []
    buf: list[InlineKeyboardButton] = []
    if not rows:
        lines.append("NO RECORDS YET.")
    for r in rows:
        code = "UNKNOWN" if r["code"] == "-" else r["code"]
        lines.append(f"{code:<7} {r['n']:>5}  {(r['name'] or '')[:13]}")
        buf.append(btn(f"{code} ({r['n']})", f"L|{kind}|{r['code']}|0"))
        if len(buf) == 2:
            buttons.append(buf)
            buf = []
    if buf:
        buttons.append(buf)
    nav = []
    if page > 0:
        nav.append(btn("◀ PREV", f"{mode}|{page - 1}"))
    if page < pages - 1:
        nav.append(btn("NEXT ▶", f"{mode}|{page + 1}"))
    if nav:
        buttons.append(nav)
    buttons.append(menu_row())
    await respond(update, pre(lines), InlineKeyboardMarkup(buttons))


async def view_stats(update: Update, days: int) -> None:
    db = Ctx.db
    label = {0: "ALL TIME", 1: "24 HOURS"}.get(days, f"{days} DAYS")
    since = iso(now_utc() - timedelta(days=days)) if days else "0000"
    base = "last_seen_utc>=? AND crossing_status='CONFIRMED'"
    args = (since,)
    total = await db.scalar(f"SELECT COUNT(*) FROM flights WHERE {base}", args) or 0
    single = await db.scalar(
        "SELECT COUNT(*) FROM flights WHERE last_seen_utc>=? AND crossing_status='SINGLE_OBS'", args) or 0
    lines = header(f"STATISTICS · {label}") + [
        f"CONFIRMED CROSSINGS {total}",
        f"UNCONFIRMED (1 OBS) {single}",
    ]
    if total:
        row = await db.one(
            f"SELECT COUNT(DISTINCT airline_icao) a, COUNT(DISTINCT aircraft_type) t, "
            f"COUNT(airline_icao) ha, COUNT(aircraft_type) ht, COUNT(dep_icao) hd, COUNT(arr_icao) hr "
            f"FROM flights WHERE {base}", args)
        lines += [f"AIRLINES            {row['a']}", f"AIRCRAFT TYPES      {row['t']}"]

        async def top(col: str, title: str) -> None:
            rows = await db.q(
                f"SELECT {col} c, COUNT(*) n FROM flights WHERE {base} AND {col} IS NOT NULL "
                f"GROUP BY c ORDER BY n DESC LIMIT 5", args)
            lines.extend([SUB, title] + ([f" {r['c']:<11}{r['n']:>6}" for r in rows] or [" no data"]))

        await top("airline_icao", "TOP AIRLINES")
        await top("aircraft_type", "TOP AIRCRAFT")
        await top("dep_icao", "TOP ORIGINS")
        await top("arr_icao", "TOP DESTINATIONS")
        kinds = await db.q(
            f"SELECT traffic_type k, COUNT(*) n FROM flights WHERE {base} GROUP BY k ORDER BY n DESC", args)
        lines += [SUB, "TRAFFIC MIX"] + [f" {k['k']:<11}{k['n']:>6}" for k in kinds]

        firsts = await db.q(f"SELECT first_seen_utc FROM flights WHERE {base}", args)
        hours = [0] * 24
        for f in firsts:
            dt = parse_dt(f[0])
            if dt:
                hours[dt.astimezone(Ctx.cfg.tz).hour] += 1
        peak = max(hours) or 1
        lines += [SUB, f"HOURLY ENTRIES ({Ctx.cfg.tz_name})"]
        for h in range(24):
            bar = "█" * round(hours[h] / peak * 14)
            lines.append(f" {h:02d} {bar:<14} {hours[h]}")

        avg = await db.one(
            f"SELECT AVG(o.altitude_ft) alt, AVG(o.ground_speed_kt) gs, COUNT(o.altitude_ft) n "
            f"FROM track_observations o JOIN flights f ON f.id=o.flight_id "
            f"WHERE f.last_seen_utc>=? AND f.crossing_status='CONFIRMED' AND o.in_iraq=1", args)
        lines += [SUB,
                  f"AVG ALTITUDE  {val(avg['alt'], ' ft')}",
                  f"AVG SPEED     {val(avg['gs'], ' kt')}",
                  f" (from {avg['n']} observations)"]

        def pct(n: int) -> str:
            return f"{round(100 * n / total):>3}%"
        lines += [SUB, "DATA COMPLETENESS",
                  f" airline {pct(row['ha'])}  type  {pct(row['ht'])}",
                  f" route   {pct(row['hd'])}  (by callsign DB)"]
    coverage = await db.scalar("SELECT MIN(first_seen_utc) FROM flights WHERE crossing_status<>'NEARBY'")
    lines.append(SUB)
    if coverage:
        lines.append(f"ARCHIVE STARTS {local(coverage, '%d %b %Y')}")
        if days and parse_dt(coverage) > now_utc() - timedelta(days=days) + timedelta(hours=1):  # type: ignore[operator]
            lines.append("⚠ PERIOD ONLY PARTLY COVERED")
    lines += ["⚠ Based on sampled observations;", "  short crossings can be missed.",
              "  Missing fields are excluded."]
    kb = InlineKeyboardMarkup([
        [btn("24H", "S|1"), btn("7D", "S|7"), btn("30D", "S|30"), btn("ALL", "S|0")],
        menu_row()])
    await respond(update, pre(lines), kb)


async def view_archive_menu(update: Update) -> None:
    coverage = await Ctx.db.scalar("SELECT MIN(first_seen_utc) FROM flights WHERE crossing_status<>'NEARBY'")
    lines = header("FLIGHT ARCHIVE") + [
        f"ARCHIVE STARTS {local(coverage, '%d %b %Y') if coverage else NA}",
        "Only flights actually collected",
        "by this bot are available.",
        SUB, "SELECT A PERIOD ▼"]
    kb = InlineKeyboardMarkup([
        [btn("LAST 24 HOURS", "L|ar|1|0")],
        [btn("LAST 7 DAYS", "L|ar|7|0"), btn("LAST 30 DAYS", "L|ar|30|0")],
        [btn("CUSTOM DATE RANGE", "M|range")],
        menu_row()])
    await respond(update, pre(lines), kb)


async def view_status(update: Update) -> None:
    db = Ctx.db
    last = await db.one("SELECT * FROM sync_history ORDER BY id DESC LIMIT 1")
    last_ok = await db.scalar("SELECT MAX(finished_utc) FROM sync_history WHERE status='OK'")
    flights = await db.scalar("SELECT COUNT(*) FROM flights WHERE crossing_status<>'NEARBY'") or 0
    obs = await db.scalar("SELECT COUNT(*) FROM track_observations") or 0
    live = await db.get_status("live_access") or "UNTESTED"
    nxt = Ctx.sync.next_run
    uptime = now_utc() - Ctx.started
    lines = header("SYSTEM STATUS") + [
        f"BOT        ONLINE  v{APP_VERSION}",
        f"UPTIME     {uptime.days}d {uptime.seconds // 3600}h {(uptime.seconds // 60) % 60}m",
        SUB,
        f"LIVE FEED  {live[:17]}",
        (await source_line()).replace("SOURCE:", "SOURCE    "),
        "HISTORY    own archive only",
        f"LAST SYNC  {ago(last['finished_utc']) if last else NA}",
        f"RESULT     {last['status'] if last else NA}",
        f"RECEIVED   {last['received'] if last else NA} aircraft in area",
        f"IN IRAQ    {last['in_iraq'] if last else NA}",
        f"AROUND     {max(0, last['inserted'] + last['updated'] - last['in_iraq']) if last else NA}",
        f"LAST OK    {ago(last_ok)}",
        f"NEXT SYNC  {local(iso(nxt), '%H:%M:%S') if nxt else NA}",
        f"INTERVAL   {Ctx.cfg.sync_interval}s",
        SUB,
        f"IRAQ FLTS  {flights}",
        f"TRACK PTS  {obs}",
        f"TIMEZONE   {Ctx.cfg.tz_name}",
    ]
    if last and last["detail"]:
        lines += [SUB, "FEEDS (with position/total)"] + [
            f" {part.strip()[:27]}" for part in last["detail"].split(";")]
    if last and last["status"] != "OK":
        lines += [SUB, "⚠ Serving stored records."]
    await respond(update, pre(lines), InlineKeyboardMarkup([[btn("⟳ REFRESH", "M|status")], menu_row()]))


HELP_LINES = header("HELP") + [
    "/start    main menu",
    "/last24   flights, last 24 hours",
    "/live     aircraft in airspace now",
    "/around   aircraft around Iraq now",
    "/search   search the archive",
    "/flight   open one flight",
    "/airlines airlines seen",
    "/aircraft aircraft types seen",
    "/stats    traffic statistics",
    "/archive  browse history",
    "/status   system status",
    SUB,
    "SEARCH: /search QTR  or  /search",
    "A7-ALA, B77W, 06A1E5 …",
    SUB,
    "✓ CONFIRMED = 2+ positions inside",
    "Iraq at least 60 s apart.",
    "? = one position only; not counted",
    "as a crossing.",
    "○ = seen only outside Iraq, within",
    "~250 NM. Kept a few days only.",
]


# --------------------------------------------------------------------------
# COMMAND HANDLERS
# --------------------------------------------------------------------------
async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data.pop("await", None)
    await view_main(update)


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await respond(update, pre(HELP_LINES), InlineKeyboardMarkup([menu_row()]))


async def cmd_last24(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_list(update, context, "24h", "-", 0)


async def cmd_live(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_list(update, context, "live", "-", 0)


async def cmd_around(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_list(update, context, "near", "-", 0)


async def prompt_search(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data["await"] = "search"
    lines = header("SEARCH FLIGHT") + [
        "SEND A SEARCH TERM:", SUB,
        "callsign      QTR8K", "registration  A7-ALA", "airline       Emirates / UAE",
        "aircraft      B77W", "airport       ORBI / BGW / Dubai", "ICAO24 hex    06A1E5"]
    await respond(update, pre(lines), InlineKeyboardMarkup([menu_row()]))


async def run_search(update: Update, context: ContextTypes.DEFAULT_TYPE, query: str) -> None:
    query = query.strip()[:40]
    if len(query) < 2:
        await respond(update, pre(["SEARCH TERM TOO SHORT (MIN 2)."]), InlineKeyboardMarkup([menu_row()]))
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
    row = await Ctx.db.one(
        "SELECT id FROM flights WHERE callsign=? OR flight_number_iata=? OR flight_number_icao=? "
        "OR registration=? OR mode_s=? ORDER BY last_seen_utc DESC LIMIT 1", (term,) * 5)
    if row:
        await view_flight(update, context, row["id"])
    else:
        await run_search(update, context, " ".join(context.args))


async def cmd_airlines(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_group(update, context, "AL", 0)


async def cmd_aircraft(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_group(update, context, "AC", 0)


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_stats(update, 1)


async def cmd_archive(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_archive_menu(update)


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await view_status(update)


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    text = (update.effective_message.text or "") if update.effective_message else ""
    text = text.strip(" \t\r\n\u200e\u200f\u200b\u202a\u202b\u202c")
    if text.startswith("/"):
        parts = text[1:].split()
        handler = COMMANDS.get(parts[0].split("@")[0].lower()) if parts else None
        if handler:
            context.args = parts[1:]
            await handler(update, context)
        else:
            await respond(update, pre(["UNKNOWN COMMAND.", "Send /help for the list."]),
                          InlineKeyboardMarkup([menu_row()]))
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
            await respond(update, pre(["INVALID RANGE.", "FORMAT: 2026-11-01 2026-11-10"]),
                          InlineKeyboardMarkup([menu_row()]))
            return
        label = f"{start:%d%b}-{(end - timedelta(days=1)):%d%b}".upper()
        context.user_data["range"] = (iso(start), iso(end), label)
        context.user_data.pop("await", None)
        await view_list(update, context, "ar", "c", 0)
    elif mode == "search" or text:
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
        [btn("RESTART INFO", "AD|restart")],
        menu_row()])


async def admin_panel(update: Update) -> None:
    lines = header("ADMIN CONSOLE") + [
        "/system       health + feed check",
        "/sync         run a sync now",
        "/sync log     recent sync results",
        "/database     database statistics",
        "/export [days|all]  CSV export",
        "/restart_info process history"]
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
        SUB, "RECENT RUNS (start → stop)"]
    for r in runs:
        stop = local(r["stopped_utc"], "%d%b %H:%M") if r["stopped_utc"] else "running/killed"
        lines.append(f"{local(r['started_utc'], '%d%b %H:%M')} → {stop}")
        lines.append(f"  └ {r['stop_reason'] or 'no clean shutdown recorded'}")
    await respond(update, pre(lines), admin_kb())


EXPORT_COLS = ["id", "callsign", "flight_number_iata", "airline_icao", "airline_name",
               "dep_icao", "dep_iata", "dep_city", "dep_country", "arr_icao", "arr_iata", "arr_city",
               "arr_country", "route_source", "traffic_type", "aircraft_type", "aircraft_type_desc",
               "aircraft_classes", "registration", "mode_s",
               "first_seen_utc", "last_seen_utc", "obs_count", "crossing_status",
               "altitude_ft", "ground_speed_kt", "heading", "latitude", "longitude", "data_source"]


async def admin_export(update: Update, days: int) -> None:
    where, args = ("crossing_status<>'NEARBY'", ()) if days <= 0 else (
        "last_seen_utc>=? AND crossing_status<>'NEARBY'", (iso(now_utc() - timedelta(days=days)),))
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


COMMANDS: dict[str, Any] = {
    "start": cmd_start, "help": cmd_help, "last24": cmd_last24, "live": cmd_live,
    "around": cmd_around,
    "search": cmd_search, "flight": cmd_flight, "airlines": cmd_airlines,
    "aircraft": cmd_aircraft, "stats": cmd_stats, "archive": cmd_archive,
    "status": cmd_status, "admin": cmd_admin, "system": cmd_system, "sync": cmd_sync,
    "database": cmd_database, "export": cmd_export, "restart_info": cmd_restart_info,
}


# --------------------------------------------------------------------------
# CALLBACK ROUTER / ERROR HANDLER
# --------------------------------------------------------------------------
async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query or not query.data:
        return
    try:
        await query.answer()
    except TelegramError:
        pass
    parts = query.data.split("|")
    head = parts[0]
    try:
        if head == "M":
            target = parts[1]
            context.user_data.pop("await", None)
            if target == "main":
                await view_main(update)
            elif target == "search":
                await prompt_search(update, context)
            elif target == "archive":
                await view_archive_menu(update)
            elif target == "status":
                await view_status(update)
            elif target == "range":
                context.user_data["await"] = "range"
                await respond(update, pre(header("CUSTOM DATE RANGE") + [
                    "SEND TWO DATES (start end):", "", "  2026-11-01 2026-11-10", "",
                    f"Dates in {Ctx.cfg.tz_name}."]), InlineKeyboardMarkup([menu_row()]))
        elif head == "L":
            await view_list(update, context, parts[1], parts[2], int(parts[3]))
        elif head == "F":
            await view_flight(update, context, int(parts[1]))
        elif head == "T":
            await view_track(update, int(parts[1]), int(parts[2]))
        elif head == "A":
            await view_aircraft_info(update, int(parts[1]))
        elif head in ("AL", "AC"):
            await view_group(update, context, head, int(parts[1]))
        elif head == "S":
            await view_stats(update, int(parts[1]))
        elif head in ("X", "AD"):
            if not is_admin(update):
                await deny(update)
            elif head == "X":
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
    except (ValueError, IndexError):
        await view_main(update)


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
            kind = "DATABASE ERROR" if isinstance(err, (sqlite3.Error, aiosqlite.Error)) else "INTERNAL ERROR"
            await context.bot.send_message(
                update.effective_chat.id, pre([f"⚠ {kind}", "The request could not be completed.",
                                               "Try again or use /start."]),
                parse_mode=ParseMode.HTML)
        except Exception:
            pass


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

    app = Application.builder().token(cfg.bot_token).build()
    for name, handler in COMMANDS.items():
        app.add_handler(CommandHandler(name, handler))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
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
            await app.bot.set_my_commands([BotCommand(c, d) for c, d in [
                ("start", "Main menu"), ("last24", "Flights in the last 24 hours"),
                ("live", "Aircraft in Iraqi airspace now"),
                ("around", "Aircraft around Iraq now"), ("search", "Search the archive"),
                ("flight", "Open a flight by callsign / number"), ("airlines", "Airlines"),
                ("aircraft", "Aircraft types"), ("stats", "Statistics"),
                ("archive", "Flight archive"), ("status", "System status"), ("help", "Help")]])
        except TelegramError as exc:
            log.warning("could not register bot commands: %s", type(exc).__name__)
        await app.updater.start_polling(
            allowed_updates=[Update.MESSAGE, Update.CALLBACK_QUERY], error_callback=polling_error)
        ev("bot online", admins=len(cfg.admin_ids), db=cfg.db_path, tz=cfg.tz_name,
           interval=cfg.sync_interval)
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
                     app.shutdown, api.close, enricher.close):
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


if __name__ == "__main__":
    sys.exit(asyncio.run(amain()))
