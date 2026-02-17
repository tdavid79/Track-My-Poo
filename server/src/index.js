import express from "express";
import cors from "cors";
import Database from "better-sqlite3";

const PORT = Number(process.env.PORT || 8787);
const DB_PATH = process.env.FLUSH_DB_PATH || "./data/flushes.db";

const app = express();
app.use(cors());
app.use(express.json({ limit: "2mb" }));
const sseClients = new Set();

const db = new Database(DB_PATH);
db.pragma("journal_mode = WAL");
db.exec(`
CREATE TABLE IF NOT EXISTS flush_runs (
  id TEXT PRIMARY KEY,
  user_name TEXT NOT NULL,
  origin_lat REAL NOT NULL,
  origin_lng REAL NOT NULL,
  created_at TEXT NOT NULL,
  started_at TEXT NOT NULL,
  status TEXT NOT NULL,
  route_version INTEGER NOT NULL,
  street_route_json TEXT NOT NULL,
  street_speed_mps REAL NOT NULL,
  street_total_m REAL NOT NULL,
  street_eta_s REAL NOT NULL,
  pipe_plan_json TEXT NOT NULL,
  pipe_base_speed_mps REAL NOT NULL,
  pipe_total_m REAL NOT NULL,
  pipe_eta_s REAL NOT NULL,
  routing_status TEXT NOT NULL,
  fallback_reason TEXT,
  fallback_bridge_json TEXT,
  terminal_node_json TEXT,
  contact_json TEXT,
  error_message TEXT,
  updated_at TEXT NOT NULL
);
`);

function metersBetween(a, b) {
  const lat1 = (a.lat * Math.PI) / 180;
  const lat2 = (b.lat * Math.PI) / 180;
  const dLat = lat2 - lat1;
  const dLng = ((b.lng - a.lng) * Math.PI) / 180;
  const x = dLng * Math.cos((lat1 + lat2) / 2);
  const y = dLat;
  const R = 6371000;
  return Math.sqrt(x * x + y * y) * R;
}

function routeDistanceMeters(route) {
  if (!Array.isArray(route) || route.length < 2) return 0;
  let d = 0;
  for (let i = 1; i < route.length; i++) d += metersBetween(route[i - 1], route[i]);
  return d;
}

function parseRunRow(row) {
  return {
    id: row.id,
    user_name: row.user_name,
    origin_lat: row.origin_lat,
    origin_lng: row.origin_lng,
    created_at: row.created_at,
    started_at: row.started_at,
    status: row.status,
    route_version: row.route_version,
    street_route: JSON.parse(row.street_route_json || "[]"),
    street_speed_mps: row.street_speed_mps,
    street_total_m: row.street_total_m,
    street_eta_s: row.street_eta_s,
    pipe_plan: JSON.parse(row.pipe_plan_json || "[]"),
    pipe_base_speed_mps: row.pipe_base_speed_mps,
    pipe_total_m: row.pipe_total_m,
    pipe_eta_s: row.pipe_eta_s,
    routing_status: row.routing_status,
    fallback_reason: row.fallback_reason,
    fallback_bridge: row.fallback_bridge_json ? JSON.parse(row.fallback_bridge_json) : null,
    terminal_node: row.terminal_node_json ? JSON.parse(row.terminal_node_json) : null,
    contact: row.contact_json ? JSON.parse(row.contact_json) : null,
    error_message: row.error_message,
    updated_at: row.updated_at
  };
}

function broadcastSse(eventName, payload) {
  const data = `event: ${eventName}\ndata: ${JSON.stringify(payload)}\n\n`;
  for (const client of Array.from(sseClients)) {
    try {
      client.write(data);
    } catch {
      sseClients.delete(client);
    }
  }
}

app.get("/api/time", (_req, res) => {
  res.json({ now: new Date().toISOString() });
});

app.get("/api/events", (req, res) => {
  res.setHeader("Content-Type", "text/event-stream");
  res.setHeader("Cache-Control", "no-cache, no-transform");
  res.setHeader("Connection", "keep-alive");
  res.setHeader("X-Accel-Buffering", "no");
  res.flushHeaders?.();
  res.write(`event: connected\ndata: ${JSON.stringify({ now: new Date().toISOString() })}\n\n`);
  sseClients.add(res);
  req.on("close", () => {
    sseClients.delete(res);
  });
});

app.get("/api/flushes", (req, res) => {
  const status = req.query.status ? String(req.query.status) : null;
  const rows = status
    ? db.prepare("SELECT * FROM flush_runs WHERE status = ? ORDER BY started_at ASC").all(status)
    : db.prepare("SELECT * FROM flush_runs ORDER BY started_at ASC").all();
  res.json(rows.map(parseRunRow));
});

app.post("/api/flushes", (req, res) => {
  const body = req.body || {};
  if (!body.id || !body.origin || typeof body.origin.lat !== "number" || typeof body.origin.lng !== "number") {
    res.status(400).json({ error: "invalid payload" });
    return;
  }

  const now = new Date().toISOString();
  const startedAt = body.startedAt || now;
  const streetRoute = Array.isArray(body.streetRoute) ? body.streetRoute : [];
  const pipePlan = Array.isArray(body.pipePlan) ? body.pipePlan : [];
  const streetSpeed = Number(body.streetSpeedMps || 1.1);
  const pipeSpeed = Number(body.pipeBaseSpeedMps || 0.6);
  const streetTotal = routeDistanceMeters(streetRoute);
  const pipeTotal = routeDistanceMeters(pipePlan);
  const streetEta = streetSpeed > 0 ? streetTotal / streetSpeed : 0;
  const pipeEta = pipeSpeed > 0 ? pipeTotal / pipeSpeed : 0;

  db.prepare(`
    INSERT INTO flush_runs (
      id, user_name, origin_lat, origin_lng, created_at, started_at, status, route_version,
      street_route_json, street_speed_mps, street_total_m, street_eta_s,
      pipe_plan_json, pipe_base_speed_mps, pipe_total_m, pipe_eta_s,
      routing_status, fallback_reason, fallback_bridge_json, terminal_node_json, contact_json, error_message, updated_at
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    ON CONFLICT(id) DO UPDATE SET
      user_name = excluded.user_name,
      origin_lat = excluded.origin_lat,
      origin_lng = excluded.origin_lng,
      started_at = excluded.started_at,
      status = excluded.status,
      route_version = excluded.route_version,
      street_route_json = excluded.street_route_json,
      street_speed_mps = excluded.street_speed_mps,
      street_total_m = excluded.street_total_m,
      street_eta_s = excluded.street_eta_s,
      pipe_plan_json = excluded.pipe_plan_json,
      pipe_base_speed_mps = excluded.pipe_base_speed_mps,
      pipe_total_m = excluded.pipe_total_m,
      pipe_eta_s = excluded.pipe_eta_s,
      routing_status = excluded.routing_status,
      fallback_reason = excluded.fallback_reason,
      fallback_bridge_json = excluded.fallback_bridge_json,
      terminal_node_json = excluded.terminal_node_json,
      contact_json = excluded.contact_json,
      error_message = excluded.error_message,
      updated_at = excluded.updated_at
  `).run(
    String(body.id),
    String(body.userName || "User"),
    Number(body.origin.lat),
    Number(body.origin.lng),
    now,
    startedAt,
    "active",
    1,
    JSON.stringify(streetRoute),
    streetSpeed,
    streetTotal,
    streetEta,
    JSON.stringify(pipePlan),
    pipeSpeed,
    pipeTotal,
    pipeEta,
    String(body.routingStatus || "incomplete"),
    String(body.fallbackReason || "none"),
    body.fallbackBridge ? JSON.stringify(body.fallbackBridge) : null,
    body.terminalNode ? JSON.stringify(body.terminalNode) : null,
    body.contact ? JSON.stringify(body.contact) : null,
    null,
    now
  );

  const row = db.prepare("SELECT * FROM flush_runs WHERE id = ?").get(String(body.id));
  const parsed = parseRunRow(row);
  broadcastSse("flush_created", parsed);
  res.json(parsed);
});

app.patch("/api/flushes/:id/status", (req, res) => {
  const id = String(req.params.id || "");
  const status = String(req.body?.status || "");
  if (!id || !["active", "arrived", "error"].includes(status)) {
    res.status(400).json({ error: "invalid payload" });
    return;
  }
  const now = new Date().toISOString();
  db.prepare("UPDATE flush_runs SET status = ?, error_message = ?, updated_at = ? WHERE id = ?").run(
    status,
    req.body?.errorMessage ? String(req.body.errorMessage) : null,
    now,
    id
  );
  const row = db.prepare("SELECT * FROM flush_runs WHERE id = ?").get(id);
  if (!row) {
    res.status(404).json({ error: "not found" });
    return;
  }
  const parsed = parseRunRow(row);
  broadcastSse("flush_status_updated", {
    id: parsed.id,
    status: parsed.status,
    error_message: parsed.error_message,
    updated_at: parsed.updated_at
  });
  res.json(parsed);
});

setInterval(() => {
  for (const client of Array.from(sseClients)) {
    try {
      client.write(`event: heartbeat\ndata: ${JSON.stringify({ now: new Date().toISOString() })}\n\n`);
    } catch {
      sseClients.delete(client);
    }
  }
}, 25000);

app.listen(PORT, () => {
  console.log(`flush-server listening on :${PORT}`);
});
