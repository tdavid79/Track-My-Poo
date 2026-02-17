## Replit Build Brief: Multi-User Live Flush Tracker (From Scratch)

### Summary
Build a new web app on Replit that recreates current core behavior (flush simulation, live map visualization, route progression, per-user tracking metadata) and adds onboarding/account ownership so every person has their own flush button/account while seeing everyone else’s flushes live.

Locked decisions for this build:
- Auth: **Magic-link email**
- Realtime backend: **Supabase (Postgres + Realtime + Auth)**
- Map data: **OSM-derived generic sewer estimate** (lower fidelity than current proprietary GeoJSON)

---

## Product Goals
1. Each user can onboard, create an account, and trigger flushes tied to their identity.
2. All users in the same shared map context can see flushes update live.
3. Map points show per-flush metadata (who, start time, current velocity, ETA).
4. Routes animate from origin through network-like paths to destination endpoints.
5. System is deployable and maintainable inside Replit with minimal ops burden.

---

## User Experience Scope

### Core flows
1. **Onboarding**
- Enter email, receive magic link, complete sign-in.
- First login prompts display name and optional avatar/emoji preference.
2. **Flush creation**
- Logged-in user clicks own flush button or map click-to-flush.
- New flush appears instantly for all connected users.
3. **Live tracking**
- Point animates on map.
- Label displays:
  - user/display name
  - started time
  - base velocity
  - ETA to destination
4. **Shared visibility**
- Everyone sees everyone’s active and recent flushes in near real time.

### Roles
- `User` (default): can create/view flushes.
- `Admin` (optional v1.1): can adjust environment settings and map layers.

---

## Architecture (Replit-Friendly)

### Frontend
- React + Vite + TypeScript.
- Leaflet (react-leaflet) for map rendering.
- Client-side animation loop (`requestAnimationFrame`), throttled UI sync.

### Backend (Supabase)
- Supabase Auth for magic links.
- Postgres for persistent users/flush/session state.
- Realtime subscriptions for flush inserts/updates/events.
- Edge functions (optional) for server-authoritative route calculations in v1.1.

### Routing/Data engine
- OSM-derived network graph prepared offline or at startup.
- Directed flow + connector fallback strategy (network-first pathing).
- Client computes movement state from persisted route plan.

---

## Data Model (Public Interfaces / Types)

### `profiles`
- `id: uuid` (auth user id)
- `email: text`
- `display_name: text`
- `emoji: text` (default `💩`)
- `created_at: timestamptz`

### `flushes`
- `id: uuid`
- `user_id: uuid`
- `user_display_name: text` (denormalized for fast render)
- `status: enum('street','pipe','arrived','error')`
- `origin_lat: double`
- `origin_lng: double`
- `current_lat: double`
- `current_lng: double`
- `route_plan: jsonb` (array of lat/lng path points)
- `route_meta: jsonb` (fallback info, endpoint info)
- `current_velocity_base_mps: double`
- `eta_to_destination_sec: double`
- `initiated_at: timestamptz`
- `updated_at: timestamptz`

### `flush_events` (optional audit/debug)
- `id: uuid`
- `flush_id: uuid`
- `event_type: text`
- `payload: jsonb`
- `created_at: timestamptz`

### Realtime channels
- `flushes:*` for insert/update/delete stream.
- Clients subscribe by environment/workspace key (single global room in v1).

---

## Functional Requirements

### Authentication & onboarding
- Magic-link sign-in only.
- On first login:
  - force profile completion (`display_name`).
- Session persisted in browser.

### Account-specific flush buttons
- Sidebar/top panel includes:
  - “My Flush” primary action.
  - Optional quick buttons for recent teammates (if collaborative space enabled).

### Live map
- Show active flush markers and labels.
- Show route overlays:
  - street segment
  - network segment
  - fallback connector path (dashed)
- Endpoint markers rendered from chosen OSM-derived terminal model.

### Routing behavior
- Strict path first.
- Network connector fallback if strict breaks.
- No long off-network straight bridge in normal mode.
- Mark `error/incomplete` when no connector path exists.

### Telemetry in labels
- Started time
- Base velocity (m/s)
- ETA to destination (seconds formatted)

---

## Non-Functional Requirements
- Mobile-first performance target.
- Realtime update latency target: <1s perceived.
- Map remains responsive with at least 20 concurrent active flushes.
- Graceful reconnect after network drop.

---

## Replit Deliverables
1. Fullstack Replit project with environment-variable setup docs.
2. Supabase schema migration SQL + seed script.
3. Frontend app with onboarding, map, flush controls, live tracking.
4. README with local/dev/prod runbook.
5. Basic test suite (unit + smoke e2e).

---

## Testing & Validation

### Functional scenarios
1. New user completes magic-link onboarding and sees own flush button.
2. User A triggers flush; User B sees it within realtime latency budget.
3. Flush progresses street → network → arrived/error with metadata updates.
4. Labels show started time, velocity, ETA and update over time.
5. Reconnect after offline resumes live state correctly.

### Performance scenarios
1. 20 simultaneous active flushes on mobile viewport.
2. Map pan/zoom during active animations remains smooth.
3. Realtime burst updates do not freeze UI.

### Security scenarios
1. User cannot impersonate another user id in writes.
2. Row-level security prevents unauthorized profile edits.
3. Anonymous non-auth users cannot create flushes.

---

## Rollout Plan
1. Milestone 1: Auth + profile + basic map render.
2. Milestone 2: Flush creation + realtime sync.
3. Milestone 3: Routing + animation + label telemetry.
4. Milestone 4: Connector fallback + endpoint handling + polish.
5. Milestone 5: QA, load checks, deploy.

---

## Assumptions and Defaults
- OSM-derived sewer approximation is acceptable for v1 realism tradeoff.
- Single shared environment/room for v1 (multi-tenant later).
- Client-side animation is authoritative for display; backend stores snapshots.
- Endpoint quality may be less accurate than your current proprietary dataset.
