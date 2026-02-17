# AGENTS.md

## Project Overview
`APP_Track_my_poo` is a single-page React + Leaflet simulation app.
It visualizes sewer pipes from GeoJSON and animates "flush points" from user/device location:
1. Street travel to nearest pipe via OSRM.
2. Pipe-network traversal using directed connectivity and Manning-based speeds.

Primary working directory: `web/`.

## Stack And Runtime
- Vite + React 19 (`web/package.json`)
- React-Leaflet + Leaflet map rendering
- GeoJSON loaded from `web/public/`
- ESLint flat config (`web/eslint.config.js`)
- External dependency at runtime: OSRM demo API (`https://router.project-osrm.org`)

Scripts (run in `web/`):
- `npm run dev`
- `npm run build`
- `npm run lint`
- `npm run preview`

Note: in some shells, `npm` may be missing. If commands fail with `command not found: npm`, install Node/npm first and re-run validations.

## Key Files
- App entry: `web/src/main.jsx`
- Main logic/UI: `web/src/App.jsx` (large, ~1400+ lines)
- Styles: `web/src/App.css`, `web/src/index.css`
- Primary network data: `web/public/Sewerage_Network_Main_Pipelines.geojson` (~2.6 MB)
- Optional cleaned variants: `web/public/Sewerage_Network_Main_Pipelines_cleaned_20m.geojson`, `web/public/Sewerage_Network_Main_Pipelines_cleaned_40m.geojson`
- Data tooling: `web/public/geojson_to_flow_svg.py`
- Historical snapshots: `web/src/Backup/*.jsx`, plus `App.jsx.bak` and `App.jsx.broken-backup`

## App Behavior Summary
`web/src/App.jsx` does all core work:
- Loads GeoJSON at startup from `/Sewerage_Network_Main_Pipelines.geojson`.
- Computes per-pipe hydraulic velocity (`_v_half_mps`) from Manning assumptions.
- Reads/normalizes direction from `DIR` (fallback `u_to_d`).
- Builds graph connectivity using snapped endpoint node keys (`_upNodeKey`, `_downNodeKey`, `_nextObjectIds`).
- Uses browser geolocation for spawn center (fallback near Elsternwick).
- For each flush point:
  - Finds nearest pipe contact point.
  - Requests OSRM road route to that contact.
  - Enters pipe mode and traverses directed network path.
- Animates points on a fixed interval tick.

## Data Contract Notes
Observed GeoJSON properties used in logic include:
- `OBJECTID`
- `SEWER_NAME` / `SEWERNAME`
- `DIR`
- `MATERIAL`
- `GRADE`
- `UPSTREAM_IL`
- `DOWNSTREAM_IL`
- `PIPE_LENGTH`
- `PIPE_WIDTH`
- `PIPE_HEIGHT`

Derived/internal properties written onto each feature:
- `_manning_n`
- `_slope_S`
- `_v_half_mps`
- `_dir`
- `_dir_source`
- `_sewer_name_norm`
- `_upNodeKey`
- `_downNodeKey`
- `_nextObjectIds`

When editing traversal logic, preserve these names to avoid breaking popups and animation state.

## Agent Workflow (Recommended)
1. Start with `git -C <repo> status --short`.
2. Work inside `web/` unless task explicitly targets repo root docs.
3. Read `web/src/App.jsx` before changing behavior; many helpers are interdependent.
4. Keep changes narrow and avoid touching backup snapshots unless explicitly asked.
5. Validate with:
   - `npm run lint`
   - `npm run build`
6. If runtime behavior changed, run `npm run dev` and manually verify:
   - map loads
   - GeoJSON renders
   - click-to-flush works
   - street route appears
   - marker transitions to pipe mode and progresses

## Known Footguns
- `App.jsx` is monolithic; small edits can have broad effects.
- There is duplicated speed-toggle button markup in sidebar; avoid introducing further UI duplication.
- Popup content includes a few debug-looking template strings for virtual-next fields; review carefully before relying on those values.
- `_sharedDownstream` is referenced in styling but may not always be populated.
- Network traversal quality depends on source data `DIR` and endpoint snapping tolerance.
- OSRM demo service can rate-limit/fail; app currently treats failures as point errors.

## Geospatial/Performance Guidance
- Avoid recomputing full-feature scans inside render paths.
- Keep expensive graph preprocessing in startup effects/memoized paths.
- If changing coordinate math, document units (meters vs lat/lng degrees) explicitly.
- For large dataset changes, sanity-check feature count and bounds after load.
