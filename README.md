# Track My Poo

Live sewer-route flush simulator with persistent state and cross-browser realtime updates.

## Current State

This repo now has two apps:

1. `web/` (React + Vite + Leaflet)
- Renders sewer network overlays from:
  - `/web/public/Sewerage_Network_Main_Pipelines.geojson`
- Simulates flush movement (street phase -> pipe phase -> arrived/error).
- Uses 💩 markers and on-map labels with:
  - started time
  - base velocity (m/s)
  - ETA to destination
- Supports settings modal + click-to-flush + speed toggle.

2. `server/` (Express + SQLite via `better-sqlite3`)
- Persists flush runs in `server/data/flushes.db`.
- Rehydrates active flushes on frontend startup.
- Pushes live delta events via SSE (`/api/events`) so multiple browser windows stay in sync.

## Key Features

- Persistent flush data survives frontend/server restarts.
- Replay-based recovery: flush position is recomputed from elapsed real time.
- Cross-browser live updates:
  - `flush_created`
  - `flush_status_updated`
- Purple-network-first fallback routing for broken directed segments.
- True endpoint targeting logic (3 selected terminal destinations).

## Project Structure

- `web/src/App.jsx`: core simulation, routing, map UI.
- `web/src/App.css`: UI/layout styling.
- `server/src/index.js`: REST + SSE + SQLite persistence API.
- `start-dev.sh`: starts backend + frontend together.

## Requirements

- Node.js 18+
- npm

## Quick Start

From repo root:

```bash
./start-dev.sh
```

This script:
- installs missing deps in `server/` and `web/`
- starts API server on `http://localhost:8787`
- starts web app on `http://localhost:5173`
- sets `VITE_API_BASE_URL=http://localhost:8787` for frontend

Press `Ctrl+C` to stop both services.

## Manual Start (Alternative)

Terminal 1:

```bash
cd server
npm install
npm run dev
```

Terminal 2:

```bash
cd web
npm install
VITE_API_BASE_URL=http://localhost:8787 npm run dev
```

## How To Use

1. Open the app (`http://localhost:5173`).
2. Use a user button in sidebar (Tom/Steph/etc.) to trigger a flush.
3. Optionally toggle `Click-to-flush` and click on map.
4. Watch movement + labels update in real time.
5. Open a second browser window to verify live sync via SSE.
6. Use `Settings` floating button for routing/overlay/performance controls.
7. Use `My location` floating button to recenter.

## Persistence + Realtime API

Base URL: `http://localhost:8787`

- `GET /api/time`
- `GET /api/flushes?status=active`
- `POST /api/flushes`
- `PATCH /api/flushes/:id/status`
- `GET /api/events` (SSE stream)

## Data Notes

- SQLite file: `server/data/flushes.db`
- Route payloads and metadata are stored in `flush_runs` JSON fields.
- Frontend rehydrates persisted active runs once on startup, then consumes SSE deltas.

## Dev Checks

Frontend:

```bash
cd web
npm run lint
npm run build
```

Backend:

```bash
node --check server/src/index.js
```
