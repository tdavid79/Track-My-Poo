# Flush Persistence Server

> [!WARNING]
> No authentication is implemented. This server is for local/dev use only and must not be internet-exposed without auth.

## Run

```bash
cd server
npm install
npm run dev
```

Defaults:
- Port: `8787`
- DB file: `server/data/flushes.db`
- Retention: terminal rows purged after `30` days, swept every `15` minutes
- CORS: localhost allowlist (`http://localhost:5173`, `http://127.0.0.1:5173`)

Env vars:
- `PORT`
- `FLUSH_DB_PATH`
- `RETENTION_DAYS`
- `RETENTION_SWEEP_MINUTES`
- `CORS_ORIGINS` (comma-separated allowlist override)
- `ALLOW_ALL_CORS=true` (dev/debug only)

## API Notes

- `POST /api/flushes` is create-only.
- Duplicate ids return `409`.
- `GET /api/flushes` supports `status`, `updated_after`, `limit`, `offset`.
