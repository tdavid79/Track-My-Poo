# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

**Start everything (preferred):**
```bash
./start-dev.sh
```
Starts backend on `http://localhost:8787` and frontend on `http://localhost:5173`.

**Manual start:**
```bash
# Terminal 1
cd server && npm install && npm run dev

# Terminal 2
cd web && npm install && VITE_API_BASE_URL=http://localhost:8787 npm run dev
```

**Validation:**
```bash
cd web && npm run lint
cd web && npm run build
node --check server/src/index.js
```

## Architecture

Two-process app: a React frontend and a Node backend that communicate over HTTP REST + SSE.

### Flush lifecycle
A flush has two sequential phases:
1. **Street phase** — OSRM public API routes the poo from the user's location to the nearest sewer pipe contact point (~1.1 m/s)
2. **Pipe phase** — directed graph traversal of the loaded GeoJSON network carries it downhill to a terminal endpoint (~0.6–3.0 m/s)

State machine: `street` → `pipe` → `arrived` (or `error` if routing fails).

Position is never persisted — on restart the frontend recomputes it from elapsed wall-clock time against the stored route.

### Frontend (`web/src/App.jsx`)
Single large file (~2600 lines) containing all routing logic, animation loop, Leaflet map setup, SSE client, settings UI, and person buttons. Edits here can easily affect unrelated features — scope changes narrowly and run lint + build after.

Key constants to know:
- `NODE_SNAP_TOL_M = 8` — snap radius when connecting to pipe network
- Fallback connector bridges broken segments up to 250m (straight-line only if network gap is unavoidable)
- Animation loop targets 30 FPS, throttled to 6 FPS for UI label sync

### Backend (`server/src/index.js`)
Express server with SQLite (WAL mode). Single `flush_runs` table stores route payloads as JSON. SSE broadcasts `flush_created` and `flush_status_updated` events to all connected clients.

Do not change the `flush_runs` schema without accounting for existing persisted rows.

### GeoJSON networks (`web/public/`)
- `Sewerage_Network_Main_Pipelines.geojson` — Melbourne (2.7 MB, committed)
- `bundaberg-sewerage-mains.normalized.geojson` — Bundaberg (15 MB, committed)
- `goldcoast-sewer-pipes-non-pressurised.normalized.geojson` — Gold Coast (46 MB, **excluded from git** — must be hosted separately or via Git LFS)

## Key Footguns

- **OSRM demo API** can rate-limit or fail, producing street-route errors — not a code bug
- **SSE + startup rehydration can race** — flush event handlers must be idempotent on flush `id`
- **Large GeoJSON rendering** — avoid triggering full re-renders of the pipe overlay; it's expensive
- **`web/src/Backup/`** — timestamped snapshots from development, do not edit

## No Authentication

The app has no auth. Never expose it publicly without adding auth to write endpoints and the SSE stream first.
