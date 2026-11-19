# Iraq Air Traffic Monitor v4

Bilingual (Arabic / English) Telegram bot that records aircraft over Iraq and around it, enriches each flight with route and aircraft details, and can find any airborne aircraft in the world on demand. Free data sources, no API key. Runs as one Railway worker. All application code is in `main.py`.

- Developer: @krofullpower
- Channel: @dlxfullpower

## Files

| File | Purpose |
|---|---|
| `main.py` | The whole application |
| `requirements.txt` | Python dependencies (python-telegram-bot 22.7 or newer for coloured buttons; aiohttp for the web console) |
| `railway.json` | Start command, single replica, restart policy (unchanged) |

## Before you deploy: mandatory subscription

Users must join `@dlxfullpower` before they can use the bot.

**Add the bot as an administrator of the channel.** Telegram only tells a bot who is a member of a channel if the bot is an admin there. No special admin rights are needed.

If the bot is not an admin, it cannot check anyone, so it lets everybody in and reports the problem: `/system` shows `SUB CHECK FAILING`, and the Railway log shows `subscription check impossible`.

Admins listed in `ADMIN_IDS` are never asked to subscribe.

## Environment variables

| Variable | Required | Default | Notes |
|---|---|---|---|
| `TELEGRAM_BOT_TOKEN` | yes | – | From @BotFather |
| `ADMIN_IDS` | recommended | empty | Telegram user IDs, comma separated |
| `REQUIRED_CHANNEL` | no | `dlxfullpower` | Channel users must join |
| `FORCE_SUBSCRIBE` | no | `true` | `false` turns the subscription requirement off |
| `DEV_USERNAME` | no | `krofullpower` | Shown on the Developer button and About page |
| `DATABASE_PATH` | no | `/data/iraq_air_traffic.db` | Must be inside the Railway Volume |
| `SYNC_INTERVAL` | no | `300` | Seconds, minimum 60 |
| `TIMEZONE` | no | `Asia/Baghdad` | Display only; storage is UTC |
| `ADSB_PROVIDERS` | no | `adsbfi,adsblol,airplaneslive,opensky` | Live sources to merge |
| `NEARBY_RETENTION_DAYS` | no | `3` | How long non-Iraq aircraft are kept |
| `WEBAPP_ENABLED` | no | `true` | `false` turns the web console off |
| `WEBAPP_URL` | no | from `RAILWAY_PUBLIC_DOMAIN` | Public HTTPS address of the console. Set it only for a custom domain |
| `PORT` | no | set by Railway, else `8080` | Port the console listens on |
| `TRACK_RETENTION_DAYS` | no | `90` | Track points older than this are deleted. `0` = keep all |

## What users see

**First contact.** The bot asks for the language (العربية / English), then checks the channel subscription, then opens the main menu. The language button stays on the main menu, in Settings, on the subscription screen, and as `/lang`.

**Interface style.** Terminal layout with no emoji: module tags such as `[IATM:FLT]`, monospace data blocks, tree-style record lines, `//` remarks, and three-letter record codes. Buttons use Telegram's coloured styles (blue for primary actions, green for confirmations, red for alerts and removals). Telegram apps released before February 2026 show the same buttons without colour.

| Code | Meaning |
|---|---|
| `CNF` | Confirmed crossing of Iraqi airspace |
| `1OB` | Single observation inside Iraq, not counted |
| `PRM` | Perimeter: around Iraq, not inside |
| `GLB` | Result of a global trace |
| `EMG` | Emergency squawk |

**Main menu** (English label / Arabic label)

| Button | What it does |
|---|---|
| AIRSPACE · LIVE / الأجواء العراقية · مباشر | Aircraft inside Iraqi airspace now |
| PERIMETER / محيط العراق | Aircraft outside the border, within about 250 NM |
| LAST 24H, ARCHIVE | Iraq flights collected by the bot: 24 h, 7 d, 30 d, custom dates |
| QUERY / استعلام | Archive search by callsign, registration, airline, type, airport, city, ICAO24 |
| GLOBAL TRACE / تتبّع عالمي | Any airborne aircraft worldwide; aircraft around a shared location |
| OPERATORS, AIRFRAMES | Rankings with bars; tap one to list its flights |
| ANALYTICS / التحليلات | Crossings, traffic mix, top airlines, types, origins, destinations, hourly chart |
| SQUAWK ALERTS / إنذارات الطوارئ | Aircraft that broadcast 7500 / 7600 / 7700 in the last 24 h |
| WATCHLIST / قائمة المتابعة | Follow a callsign, registration or ICAO24; get a message when it enters Iraq |
| CONFIG / الإعدادات | Language, emergency alerts on/off |
| SYSTEM, MANUAL, ABOUT | Feed health, commands, credits and data sources |
| DEVELOPER, CHANNEL | Links to @krofullpower and @dlxfullpower |

**Flight page**

- Flight: callsign, flight number, airline, origin and destination with city and country code.
- Route progress bar, distance flown and remaining, estimated arrival (from current speed).
- Aircraft: type, model, manufacturer, registration, ICAO24, owner, country, weight category.
- Live data: altitude (ft, FL, m), GPS altitude, speed (kt, km/h), heading with compass, climb/descent rate, squawk, Mach, IAS/TAS, selected altitude and heading, wind, outside temperature, position, nearest Iraqi city, signal source.
- Iraq airspace: first and last observation, duration, crossing status.
- Buttons: open on map, send position as a Telegram location, track with altitude profile, aircraft page with photo link and recent flights, follow, live update.

Only fields the aircraft actually broadcasts are shown.

**Push messages**

- Watchlist: one message when a followed identifier is seen inside Iraq.
- Emergency alerts (opt-in in Settings): one message per aircraft squawking an emergency code in or around Iraq.

## Web console (Telegram Mini App)

The bot also serves a web console that opens inside Telegram, from the **OPEN CONSOLE** button at the top of the main menu, the menu button next to the message box, or `/console`.

Every page carries the credit line "Dev & Powered by KroTheCommander" at the bottom.

| Tab | What it shows |
|---|---|
| Scope | Radar of Iraq and its perimeter drawn by the bot itself (no map provider): border, cities, range rings from Baghdad, aircraft rotated to their heading, history trail, 2-minute speed vector, ATC-style data blocks (callsign, flight level, speed, type). Drag to pan, pinch or buttons to zoom, tap an aircraft for its summary |
| Strips | The live aircraft as flight strips, filtered by Iraq, perimeter or emergency, plus a search of the whole archive |
| Traffic | Crossings, operators and types for 24 h, 7 d, 30 d or all time; hourly chart; top operators, types, origins, destinations; traffic mix |
| System | Feed health, sources, sync log, record counts, links to the channel and developer. Admins also see users, subscription check and lookup status |

Tapping an aircraft opens its file: route with progress bar, distance flown and remaining, estimated arrival, full telemetry, a track map, an altitude chart, Iraqi airspace times, airframe details, other records of the same aircraft, and buttons to watch it, open it in Maps or open its photo page.

Between syncs, aircraft are moved forward along their heading at their ground speed (up to 6 minutes). After 90 seconds without an update they are drawn hollow and their data block is marked `~`, so an estimate is never shown as a fresh position. With the default 300-second sync this happens often; `SYNC_INTERVAL=60` gives a smoother scope (9 feed requests per sync, about 11 seconds of work).

**Security.** Every request is signed by Telegram (`initData`) and checked against the bot token, with a 24-hour expiry, before any data is read. The channel subscription rule applies to the console too. Each user is limited to 40 requests per 10 seconds.

**Design.** Air-traffic-control vocabulary rather than generic dashboard parts: a slate scope, gold for structure and selection, red only for emergencies, flight strips, data blocks and history dots. Fonts are Saira Semi Condensed, IBM Plex Mono and IBM Plex Sans Arabic (Google Fonts). Arabic switches the whole layout to right-to-left; the scope stays geographic.

## Commands

User: `/start /live /around /last24 /archive /search /flight /world /near /airlines /aircraft /stats /alerts /watch /unwatch /watchlist /settings /lang /status /about /help`

Admin: `/admin /system /sync /sync log /database /export [days|all] /restart_info /users /broadcast <text>`

Admin panels are in English only.

## Data sources

**Live positions** (merged every sync; a gap in one is filled by the others)

| Source | Notes |
|---|---|
| adsb.fi | Verified from its official README. 1 request/second. Personal, non-commercial use; credit and link required (shown on the About page) |
| adsb.lol | No key today; the project says a key will be required in future |
| airplanes.live | 1 request/second |
| OpenSky Network | Separate receiver network. Anonymous access, polled every 10 minutes for the Iraq area to stay inside the daily allowance. May refuse requests from cloud hosts; the bot then skips it for an hour |

**Route and aircraft lookups** (cached in SQLite; each callsign or aircraft is looked up once per cache period)

| Source | Used for |
|---|---|
| adsbdb.com | Route by callsign, airline name, flight number, aircraft registry, photo link |
| adsb.lol route service | Second route source; it also checks the route is plausible for the aircraft's position |
| hexdb.io | Third route source, airport names and coordinates, aircraft registry fallback |
| planespotters.net | Link to an aircraft photo page |

What is and is not verified:

- Only adsb.fi's endpoints were confirmed from official documentation. The other URL formats and response field names were written from search-result excerpts and from memory, because their documentation could not be opened from the build environment.
- Nothing has been run against the live services. Testing used simulated responses.
- A source whose URL or format is wrong is skipped; the others keep working. `/status` shows what each feed returned.

**What a route means.** It is the route usually flown under that callsign, from community databases. It is not a live flight plan, and it can be missing or wrong. The flight page says which database it came from.

**Still not available from free sources:** actual departure and arrival times, and any flight history from before the bot was deployed.

## How a crossing is decided

- Each position is tested against a simplified Iraq border polygon (accuracy about 10–20 km).
- **Confirmed** (`CNF`): two or more airborne positions inside Iraq at least 60 s apart.
- **Single observation** (`1OB`): one position only. Listed, never counted as a crossing.
- **Perimeter** (`PRM`) and **global** (`GLB`) aircraft never count in Iraq statistics and are deleted after `NEARBY_RETENTION_DAYS`.
- Aircraft on the ground and positions older than 5 minutes are ignored.

## Railway deployment

1. **Create a project.** Railway dashboard → New Project.
2. **Connect GitHub.** Push the three files to a repository, then "Deploy from GitHub repo".
3. **Service type.** The service is now a web service: it listens on `PORT` for the console. Do not set a port yourself; Railway provides it.
4. **Generate a domain.** Settings → Networking → Public Networking → Generate Domain. The console needs it; the bot works without it. Railway fills `RAILWAY_PUBLIC_DOMAIN` and the bot uses it automatically.
5. **Add a volume.** Create a Volume, attach it to the service, mount path `/data`.
6. **Add variables.** `TELEGRAM_BOT_TOKEN` and `ADMIN_IDS`.
7. **Make the bot an admin of the channel** (see above).
8. **Deploy and check logs** for `mini app online`, `bot online` and `sync finished` with `"status": "OK"`.

Upgrading from an earlier version: replace `main.py`, `requirements.txt` and `railway.json`, then generate a domain. The existing database is upgraded in place on first start; nothing is deleted.

## Testing checklist

1. `/start` from a new account: language question, then the subscription screen, then the menu after joining.
2. Leave the channel: within 10 minutes the bot asks you to join again.
3. `/status`: the FEEDS section lists each source with aircraft counts or an error.
4. Open a flight with an airline callsign: origin, destination and progress bar appear if the route is in a database.
5. `/world` with a callsign that is flying now; send a location.
6. Follow a flight, turn alerts on in Settings.
7. Press OPEN CONSOLE: the scope loads, tap an aircraft, open its file, switch to Arabic in the bot and reopen.
8. As admin: `/system` (check `SUB CHECK OK`), `/users`, `/broadcast test`, `/export 1`.
