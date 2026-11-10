# Iraq Air Traffic Monitor

Telegram bot that records aircraft observed inside Iraqi airspace, using the AirNav Radar On Demand API, SQLite and long polling. Runs as one Railway worker. All application code is in `main.py`.

## Files

| File | Purpose |
|---|---|
| `main.py` | The whole application |
| `requirements.txt` | Python dependencies |
| `railway.json` | Start command, single replica, restart policy |

## Environment variables

| Variable | Required | Default | Notes |
|---|---|---|---|
| `TELEGRAM_BOT_TOKEN` | yes | – | From @BotFather |
| `AIRNAV_API_KEY` | yes | – | AirNav Radar On Demand API token |
| `ADMIN_IDS` | recommended | empty | Telegram user IDs, comma separated (`111,222`). Empty = no admins |
| `DATABASE_PATH` | no | `/data/iraq_air_traffic.db` | Must be inside the Railway Volume |
| `SYNC_INTERVAL` | no | `300` | Seconds, minimum 60 |
| `TIMEZONE` | no | `Asia/Baghdad` | Display only; storage is UTC |
| `DAILY_CREDIT_BUDGET` | no | `0` (off) | Syncs stop for the UTC day once this many API credits are spent |
| `BACKFILL_ON_START` | no | `true` | Fetch the gap since the last sync (max 24 h) at startup |
| `TRACK_RETENTION_DAYS` | no | `90` | Track points older than this are deleted; flight records are kept. `0` = keep all |

## Railway deployment

1. **Create a project.** Railway dashboard → New Project.
2. **Connect GitHub.** Push these three files to a GitHub repository, then choose "Deploy from GitHub repo" and select it.
3. **Make it a worker.** Railway has no separate worker type: a worker is a service with no public networking. In the service Settings, do not generate a domain and do not set a port. `railway.json` already sets the start command `python main.py`, one replica, and restart on failure.
4. **Add a volume.** Create a Volume, attach it to this service, and set the mount path to `/data`.
5. **Add variables.** In the service Variables tab, add the variables from the table above.
6. **Deploy and check logs.** Redeploy, open the deployment logs, and look for `"msg": "bot online"` followed by `"msg": "sync finished"` lines.

Notes:

- Railway menu labels change from time to time; the settings to find are "Volume → mount path" and "Variables".
- If no volume is attached, or `DATABASE_PATH` is outside it, the bot logs `CONFIGURATION ERROR` and exits instead of writing history to temporary storage.
- Keep replicas at 1. A lock file on the volume stops a second process from starting, and Telegram itself rejects two pollers on one token.
- To pin the Python version, set the variable `RAILPACK_PYTHON_VERSION=3.12`.

## API subscription requirements

Source: <https://www.airnavradar.com/api/openapi> (On Demand API v2) and <https://www.airnavradar.com/api/pricing>.

Endpoints used:

| Endpoint | Used for |
|---|---|
| `POST /flights/live` | Current flights in the Iraq bounding box, every sync |
| `POST /flights/geosearch` | Previous 24 h with flight paths (startup backfill, `/sync history`) |
| `GET /aircraft` | Aircraft details, only when a user opens "Aircraft info"; cached 30 days |
| `GET /billing/status` | Credit balance and connectivity check in `/system` |

What is not verified:

- **Historical access.** The published docs do not say which plans include `geosearch` history, how far back it goes, or whether `positions[]` is always returned. The bot tests this at runtime: `/status` shows HISTORY as `OK`, `UNAVAILABLE`, `NO_TRACKS` or `ERROR`. If history is unavailable the bot runs on live collection only, and the archive starts from first deployment.
- **Credit cost.** Pricing is per result, but the cost per flight returned is not published. At the default interval the bot makes 288 live calls per day. Watch the CR column in `/sync log` on the first day and set `DAILY_CREDIT_BUDGET` or raise `SYNC_INTERVAL` to fit your plan (Starter is 10,000 credits per month).
- **Rate limits.** None are documented. The client spaces requests 1 s apart, retries with exponential backoff, and honours `Retry-After` on HTTP 429.

## How a crossing is decided

- Each position is tested against a simplified Iraq border polygon (accuracy about 10–20 km).
- **CONFIRMED**: two or more airborne positions inside Iraq at least 60 s apart.
- **SINGLE_OBS** (shown as `?`): one position only. Listed, but never counted as a crossing in statistics.
- Flights with no position inside the polygon are not stored. Origin or destination airport is never used as evidence.
- Live sampling is every `SYNC_INTERVAL` seconds, so very short border clips can be missed and "duration over Iraq" is a lower bound.

## Commands

User: `/start /last24 /live /search /flight /airlines /aircraft /stats /archive /status /help`

Admin: `/admin /system /sync /sync history [hours] /sync log /database /export [days|all] /restart_info`

## Testing

Local run:

```bash
pip install -r requirements.txt
mkdir -p ./data
export TELEGRAM_BOT_TOKEN=... AIRNAV_API_KEY=... ADMIN_IDS=<your id>
export DATABASE_PATH=./data/iraq_air_traffic.db
python main.py
```

Checklist:

1. Start without `TELEGRAM_BOT_TOKEN`: the process exits with `CONFIGURATION ERROR`.
2. Send `/start`: the main menu appears with eight buttons.
3. As admin, `/system`: API shows `REACHABLE · AUTH OK` and a credit balance.
4. `/sync`: status `OK`, with RECEIVED and IN IRAQ counts.
5. Wait for two sync cycles, then `/live`: flights seen twice show `✓`.
6. Open a flight → Track and Aircraft info.
7. `/sync history 2`, then `/status`: check the HISTORY line.
8. `/export 1`: a CSV file arrives. From a non-admin account the same command returns ACCESS DENIED.
9. Set a wrong `AIRNAV_API_KEY` and restart: `/last24` still serves stored records and `/status` shows the failure.
10. On Railway, redeploy and confirm the archive is still there (`/database`).
