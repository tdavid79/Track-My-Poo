# Backend Cost Minimization Strategy

## Objective
Minimize backend cost to the lowest practical level, even if that shifts more computation and responsibility to the frontend.

## Guiding Principle
Treat backend as a **thin shared event store**, not a simulation engine.

- Backend should accept new flush events and return deltas.
- Frontend should calculate routes, movement, status, ETA, and rendering.

---

## Current High-Cost / High-Complexity Areas

1. Long-lived server connections (SSE fanout).
2. Server write churn for status updates (`PATCH /status`).
3. Large persisted payloads (full route snapshots per flush).
4. Reliance on external routing services (risk + potential billed API usage).
5. Always-on server runtime even during low traffic.

---

## Target Architecture (Backend-lean)

## 1) Backend as Append-Only Event Log

### Keep only two endpoints
1. `POST /api/flushes`
- Append immutable `flush_created` event.

2. `GET /api/flushes?updated_after=<iso>&limit=<n>`
- Return new events since the caller’s checkpoint.

### Remove
- `PATCH /api/flushes/:id/status`
- Server-side lifecycle/status mutation logic
- SSE endpoint (`/api/events`) if polling mode is chosen

### Why this helps
- Fewer writes and less DB contention
- Simpler server code and lower compute needs
- Easy to host on cheap serverless/edge infrastructure

---

## 2) Frontend-Owned Simulation (Shift right)

Frontend computes all dynamic state from immutable event data:

- route generation
- street-to-pipe transition
- fallback/connector logic
- velocity and ETA
- arrived/error status

The backend no longer needs to track moving position or mode transitions.

### Result
- Backend stores only source-of-truth event data.
- Browser handles all expensive per-frame logic (already happening largely today).

---

## 3) Replace SSE with Delta Polling (Lowest ops overhead)

Use periodic polling from client:

- Every 10-20 seconds: `GET /api/flushes?updated_after=...`
- Merge by `id` and `updated_at` on client.

### Tradeoff
- Slightly less realtime than SSE (seconds vs instant)
- Lower runtime complexity and lower persistent connection load

### Why this helps
- No long-lived connection management
- No heartbeat loops
- Better fit for serverless platforms and cheap tiers

---

## 4) Reduce Persisted Payload Size

Persist minimal event shape rather than full route snapshots.

### Minimal suggested schema
- `id`
- `user_name`
- `origin_lat`, `origin_lng`
- `started_at`
- `route_version`
- `contact_pipe_id`
- `contact_point` (lat/lng)
- optional: `seed` for deterministic jitter
- `created_at`, `updated_at`

### Optional compatibility fields
- `street_route_json` only during transition period
- remove once all clients can deterministically recompute

### Why this helps
- Smaller DB size
- Lower I/O and less transfer per response
- Better long-term retention economics

---

## 5) Routing Cost Strategy (Biggest lever)

## Option A: Cheapest possible (no road API)
- Skip external road route API.
- Use direct connector from origin to nearest pipe contact point.
- Pipe routing remains as-is (client-side).

Pros:
- Zero routing API cost.
- Very simple.

Cons:
- Less realistic street phase geometry.

## Option B: Better realism without backend cost
- Ship a lightweight road graph with app assets.
- Run A*/Dijkstra in browser Web Worker.
- Cache route results in IndexedDB/localStorage.

Pros:
- No backend routing cost.
- Better route quality.

Cons:
- Larger frontend payload and complexity.

## Option C: Hybrid
- Use direct connector by default.
- Enable local graph route only for users who opt into “high fidelity mode”.

---

## 6) Deployment Model for Near-Zero Backend Spend

1. Static frontend on CDN (cheap/free tier).
2. Tiny API on serverless/edge runtime.
3. Lightweight edge DB or minimal managed SQLite/libSQL.
4. Polling (not SSE) to avoid stateful workers.

This is typically the minimum-cost production-like shared architecture.

---

## Recommended Roadmap

## Phase 1 (Immediate, low risk)
1. Remove server status PATCH dependency.
2. Keep only create + list APIs.
3. Move all status transitions to frontend.
4. Keep SSE temporarily if desired.

## Phase 2 (Cost cut)
1. Replace SSE with polling deltas.
2. Shrink persisted payload schema.
3. Add aggressive retention/archival policy.

## Phase 3 (Routing spend elimination)
1. Remove external routing calls.
2. Start with direct connector.
3. Optionally add local road graph worker later.

---

## Operational Tradeoffs

## What you gain
- Lower backend compute and connection overhead
- Simpler API and lower maintenance burden
- Better scaling economics for low/medium traffic

## What you accept
- More client complexity
- Slightly weaker strict cross-device determinism (unless deterministic route generation is enforced)
- Polling latency vs instant server push

---

## Data Consistency Model (Frontend-heavy)

1. Flush creation is persisted first.
2. All clients fetch immutable events.
3. Each client simulates local movement from same inputs.
4. No server-authoritative moving state required.

To tighten cross-device consistency, keep:
- stable route algorithm version (`route_version`)
- deterministic tie-breaking
- optional seed value stored with event

---

## Security + Cost Alignment

Even in low-cost mode:

1. Keep CORS strict by default.
2. Add authentication before public launch.
3. Avoid `ALLOW_ALL_CORS` in internet-facing environments.

Security failures can become the most expensive “cost event”.

---

## Suggested Final Target (Practical Minimum)

- Backend: append-only event storage + delta read API
- Sync: polling deltas every 10-20s
- Routing: client-side only (direct connector initially)
- Simulation: entirely client-side
- Persistence: minimal event payload

This gives the lowest practical backend cost while still supporting shared multi-user live maps.
