# AGENTS.md

## Project Overview
`APP_Track_my_poo` is a two-part app:
1. `web/` (React + Vite + Leaflet) for map simulation UI.
2. `server/` (Express + SQLite) for persistence, replay state, and SSE push updates.

The app simulates flush travel in two phases:
1. Street route to sewer contact point (OSRM).
2. Directed pipe-network traversal to true endpoints.

## Active Architecture
- Frontend persists/rehydrates flush runs through backend APIs.
- Backend stores runs in SQLite (`server/data/flushes.db`).
- Cross-browser live sync uses SSE (`GET /api/events`).
- Routing includes fallback logic designed to stay on the purple sewer network where possible.

## Primary Files
- Frontend core: `web/src/App.jsx`
- Frontend styles: `web/src/App.css`
- Frontend entry: `web/src/main.jsx`
- Main network file: `web/public/Sewerage_Network_Main_Pipelines.geojson`
- Backend API: `server/src/index.js`
- Root startup script: `start-dev.sh`
- Product docs: `README.md`

## Run Commands
From repo root (preferred):
- `./start-dev.sh`

Manual split run:
- Backend:
  - `cd server && npm install && npm run dev`
- Frontend:
  - `cd web && npm install && VITE_API_BASE_URL=http://localhost:8787 npm run dev`

Validation:
- Frontend:
  - `cd web && npm run lint`
  - `cd web && npm run build`
- Backend:
  - `node --check server/src/index.js`

## API Surface (Current)
- `GET /api/time`
- `GET /api/flushes?status=active`
- `POST /api/flushes`
- `PATCH /api/flushes/:id/status`
- `GET /api/events` (SSE: `flush_created`, `flush_status_updated`, `heartbeat`)

## Data + Routing Notes
- Keep compatibility with existing persisted shape in `flush_runs` table.
- Treat replay model as source of truth after restart (elapsed wall-clock time).
- Do not silently mark runs as arrived unless terminal endpoint was reached.
- Prefer network-following connector fallback paths over straight-line bridges.

## Working Rules For Agents
1. Start by checking repo state:
   - `git status --short`
2. Scope changes narrowly to requested behavior.
3. Avoid editing backup snapshots unless explicitly requested:
   - `web/src/App.jsx.bak`
   - `web/src/Backup/*`
4. If behavior changes, run relevant validation before handoff.
5. Update docs (`README.md`/`AGENTS.md`) when behavior or run steps change.

## Commit Prompt Requirement
After you successfully land requested code changes and validations:
1. Summarize what changed and what checks ran.
2. Prompt the user to commit in a direct question.
3. If they confirm, use existing repo identity (or latest commit identity if unset), then commit.

Suggested wording:
- "Changes are landed and checks passed. Do you want me to commit these changes now?"

If checks could not run, state that clearly before asking to commit.

## Known Footguns
- `web/src/App.jsx` is large and stateful; small edits can affect routing/animation.
- OSRM demo API may fail/rate-limit and can create street-route errors.
- SSE and startup rehydrate can race; keep event handlers idempotent by flush `id`.
- Large GeoJSON rendering can regress performance if frequent full re-renders are reintroduced.
