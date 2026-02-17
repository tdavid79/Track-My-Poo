# Australian Sewer Dataset Normalization Plan

Date: 2026-02-17

## Pulled Sources (staged locally)

- `data/australia-sewer/raw/barwon-water-gravity-sewer-pipes.geojson` (GeoJSON, ~40 MB)
- `data/australia-sewer/raw/chw-sewermains.geojson` (GeoJSON, ~18 MB)
- `data/australia-sewer/raw/bundaberg-sewerage-network.zip` (FileGDB ZIP, ~2.4 MB)
- `data/australia-sewer/raw/goldcoast-sewer-pipes-non-pressurised.csv` (CSV, ~23 MB)
- WA Water Corporation endpoints (`WCORP-068`, `WCORP-069`) currently return SSO login HTML unless authenticated.

## Target Schema For This App

The app logic in `web/src/App.jsx` relies mainly on:

- `OBJECTID`
- `SEWER_NAME` (or fallback `SEWERNAME`)
- `MATERIAL`
- `PIPE_LENGTH`
- `PIPE_WIDTH`
- `PIPE_HEIGHT`
- `GRADE`
- `UPSTREAM_IL`
- `DOWNSTREAM_IL`
- `geometry` (`LineString` or `MultiLineString`)

Everything else is optional for display/debug.

## Canonical Normalized Output

Single GeoJSON output per source:

- `data/australia-sewer/normalized/<source>.geojson`

Each feature should include these normalized properties:

- `OBJECTID` (string/integer stable id)
- `SEWER_NAME` (string, uppercase preferred)
- `MATERIAL` (string)
- `PIPE_LENGTH` (meters, float)
- `PIPE_WIDTH` (mm, float)
- `PIPE_HEIGHT` (mm, float; fallback `0` when unknown)
- `GRADE` (m/m slope, float)
- `UPSTREAM_IL` (meters, float)
- `DOWNSTREAM_IL` (meters, float)
- `_source` (dataset id)
- `_quality_flags` (pipe-delimited flags string)

## Source-to-Target Mapping Plan

### 1) Barwon Water (`barwon-water-gravity-sewer-pipes.geojson`)

Likely direct mapping:

- `OBJECTID` <- `OBJECTID`
- `SEWER_NAME` <- `GENERAL_TEXT` or fallback `"BARWON_GRAVITY"`
- `MATERIAL` <- `PIPE_MATERIAL`
- `PIPE_LENGTH` <- `PIPE_LENGTH`
- `PIPE_WIDTH` <- `PIPE_DIA`
- `PIPE_HEIGHT` <- `0`
- `GRADE` <- `PIPE_GRADIENT`
- `UPSTREAM_IL` <- `UPSTREAM_INVELEV`
- `DOWNSTREAM_IL` <- `DOWNSTREAM_INVELEV`

Quality flags:

- `MISSING_SEWER_NAME` when `GENERAL_TEXT` empty
- `ZERO_HEIGHT_ASSUMED`

### 2) Central Highlands Water (`chw-sewermains.geojson`)

Field mapping:

- `OBJECTID` <- `OBJECTID` (or `id`)
- `SEWER_NAME` <- `type` (fallback `"CHW_SEWER_MAIN"`)
- `MATERIAL` <- `material`
- `PIPE_LENGTH` <- `SHAPE__Length`
- `PIPE_WIDTH` <- `diameter`
- `PIPE_HEIGHT` <- `0`
- `GRADE` <- null (no clean source field)
- `UPSTREAM_IL` <- null
- `DOWNSTREAM_IL` <- null

Quality flags:

- `NO_INVERT_LEVELS`
- `NO_GRADE`
- `ZERO_HEIGHT_ASSUMED`

### 3) Bundaberg (`bundaberg-sewerage-network.zip`)

This is an ESRI FileGDB package. Need conversion first:

1. Unzip under `data/australia-sewer/raw/bundaberg/`
2. Use GDAL to inspect layers: `ogrinfo BRC_Sewerage_Network.gdb`
3. Select sewer main polyline layer
4. Convert to GeoJSON and map fields:
   - candidate names from metadata: `Asset_ID`, `materialType`, `length`, `diameter`, `upstreamManholeIL`, `downstreamManholeIL`

Quality flags:

- `GDB_LAYER_PICK_REQUIRED` until layer is fixed in script

### 4) Gold Coast (`goldcoast-sewer-pipes-non-pressurised.csv`)

Current pulled file is CSV. Build line geometry via paired node coordinates if present:

1. Parse columns (likely includes diameter, material, upstream/downstream levels, length).
2. If geometry text exists (WKT/encoded), parse directly.
3. If only endpoints exist, create 2-point `LineString`.
4. If no geometry can be built, hold record in reject log.

Preferred follow-up: retry WFS GeoJSON with paging/filter to avoid 504 timeout.

Quality flags:

- `GEOMETRY_SYNTHESIZED` or `NO_GEOMETRY`

## Implementation Steps

1. Create a normalizer script (`data/australia-sewer/normalize.rb`) with source-specific adapters.
2. Emit two outputs per source:
   - normalized GeoJSON
   - reject report CSV (`id,reason,source`)
3. Add validation checks:
   - non-empty features
   - geometry type is line-based
   - at least one of `PIPE_WIDTH`, `PIPE_LENGTH` present
4. Add merge step:
   - `normalized/all-au-sewer-mains.geojson`
5. Add app compatibility smoke test:
   - swap `PIPE_GEOJSON_PATH` in `web/src/App.jsx` to a normalized file and verify map load + routing.

## Licensing/Use Constraints To Enforce

- Respect each source license before redistribution.
- Some sources are `cc-nc-nd`; normalized outputs may need to stay internal (non-commercial, no derivatives restrictions may apply).
- Keep `_source` attribution on every feature.

## Current Blockers

- WA Water Corporation direct files require authenticated access (SSO gate).
- Bundaberg is FileGDB; needs GDAL tooling in environment.
- Gold Coast WFS GeoJSON endpoint timed out (504); CSV fallback is staged.
