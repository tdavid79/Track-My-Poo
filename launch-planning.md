# Launch Planning

## Public Service Cost Estimate (Current App)

### Architecture baseline
- Frontend: Vite/React static app
- API: Node/Express
- Data: SQLite (currently file-backed)
- Realtime: SSE
- Routing: currently OSRM demo endpoint
- Basemap: CARTO raster tiles

## Monthly cost bands

### 1) Lean public beta (single region, low traffic)
Estimated: **~$5-$30/month**

- Static frontend hosting can be free-tier.
- Small API + persistent volume typically low single-digit dollars.
- Basic uptime monitoring often free or very low cost.

### 2) Small production (commercial-safe)
Estimated: **~$40-$150/month**

- API compute + storage with headroom.
- Production-safe mapping terms/licensing.
- Replace demo routing with production-capable routing provider or self-hosted routing stack.

### 3) Hardened production (HA + stronger ops)
Estimated: **~$150-$600+/month**

- Multi-instance API and better failover.
- Managed database tier and backup posture.
- Better monitoring/alerting and operational tooling.

## Key cost drivers

1. Routing volume and provider choice.
2. Basemap licensing/usage terms.
3. API compute required for concurrent users + SSE fanout.
4. Storage growth and retention policy.
5. Reliability posture (single-instance vs HA).

## Important launch caveats

- The current OSRM demo endpoint is not suitable as a public production dependency.
- Basemap usage terms must be validated for your launch type (commercial/public).
- Current app remains dev/local-first until authentication/authorization is implemented.

## Forecast model

Use this practical formula:

`Total monthly = Hosting + DB/Storage + Map Tiles + Routing + Monitoring`

Starting assumptions for planning:
- Hosting + DB: `$5-$50`
- Map tiles: `$0-$25+` (provider/traffic dependent)
- Routing: `$0-$200+` (very traffic dependent)

## Next-step scenarios to model before launch

1. Low: ~1k flushes/month
2. Medium: ~10k flushes/month
3. High: ~100k flushes/month

For each scenario, capture:
- expected routing requests/month
- average concurrent active flushes
- expected SSE client concurrency
- projected monthly cost by provider option

## Recommended pre-launch decisions

1. Choose production routing strategy (managed API vs self-hosted).
2. Confirm basemap provider terms and expected pricing.
3. Decide target reliability tier (beta vs production vs HA).
4. Implement auth before public internet exposure.
