import { randomUUID } from "crypto";
import express from "express";
import cors from "cors";
import Database from "better-sqlite3";

const PORT = Number(process.env.PORT || 8787);
const DB_PATH = process.env.FLUSH_DB_PATH || "./data/flushes.db";
const RETENTION_DAYS = Math.max(1, Number(process.env.RETENTION_DAYS || 30));
const RETENTION_SWEEP_MINUTES = Math.max(1, Number(process.env.RETENTION_SWEEP_MINUTES || 15));
const ALLOW_ALL_CORS = String(process.env.ALLOW_ALL_CORS || "").toLowerCase() === "true";
const DEFAULT_CORS_ORIGINS = ["http://localhost:5173", "http://127.0.0.1:5173"];
const CORS_ORIGINS = (process.env.CORS_ORIGINS || "")
  .split(",")
  .map((s) => s.trim())
  .filter(Boolean);
const ALLOWED_ORIGINS = new Set(CORS_ORIGINS.length > 0 ? CORS_ORIGINS : DEFAULT_CORS_ORIGINS);

const app = express();
app.use(
  cors({
    origin(origin, callback) {
      if (ALLOW_ALL_CORS || !origin || ALLOWED_ORIGINS.has(origin)) {
        callback(null, true);
        return;
      }
      callback(new Error("Not allowed by CORS"));
    }
  })
);
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
CREATE INDEX IF NOT EXISTS idx_flush_runs_status_started_at ON flush_runs(status, started_at);
CREATE INDEX IF NOT EXISTS idx_flush_runs_updated_at ON flush_runs(updated_at);
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

function safeJsonParse(raw, fallback, { runId, field, critical = false }) {
  if (raw === null || raw === undefined || raw === "") return fallback;
  try {
    return JSON.parse(raw);
  } catch (error) {
    console.warn("json_parse_failed", {
      runId,
      field,
      critical,
      error: String(error?.message || error)
    });
    return fallback;
  }
}

function parseRunRow(row) {
  const streetRoute = safeJsonParse(row.street_route_json, [], {
    runId: row.id,
    field: "street_route_json",
    critical: true
  });
  const pipePlan = safeJsonParse(row.pipe_plan_json, [], {
    runId: row.id,
    field: "pipe_plan_json",
    critical: true
  });
  const fallbackBridge = safeJsonParse(row.fallback_bridge_json, null, {
    runId: row.id,
    field: "fallback_bridge_json",
    critical: false
  });
  const terminalNode = safeJsonParse(row.terminal_node_json, null, {
    runId: row.id,
    field: "terminal_node_json",
    critical: false
  });
  const contact = safeJsonParse(row.contact_json, null, {
    runId: row.id,
    field: "contact_json",
    critical: false
  });

  const criticalInvalid =
    !Array.isArray(streetRoute) ||
    !Array.isArray(pipePlan) ||
    streetRoute.some((p) => typeof p?.lat !== "number" || typeof p?.lng !== "number") ||
    pipePlan.some((p) => typeof p?.lat !== "number" || typeof p?.lng !== "number");

  return {
    run: {
      id: row.id,
      user_name: row.user_name,
      origin_lat: row.origin_lat,
      origin_lng: row.origin_lng,
      created_at: row.created_at,
      started_at: row.started_at,
      status: row.status,
      route_version: row.route_version,
      street_route: streetRoute,
      street_speed_mps: row.street_speed_mps,
      street_total_m: row.street_total_m,
      street_eta_s: row.street_eta_s,
      pipe_plan: pipePlan,
      pipe_base_speed_mps: row.pipe_base_speed_mps,
      pipe_total_m: row.pipe_total_m,
      pipe_eta_s: row.pipe_eta_s,
      routing_status: row.routing_status,
      fallback_reason: row.fallback_reason,
      fallback_bridge: fallbackBridge,
      terminal_node: terminalNode,
      contact,
      error_message: row.error_message,
      updated_at: row.updated_at
    },
    criticalInvalid
  };
}

function normalizeRunRow(row) {
  const parsed = parseRunRow(row);
  if (parsed.criticalInvalid && row.status !== "error") {
    const now = new Date().toISOString();
    db.prepare("UPDATE flush_runs SET status = ?, error_message = ?, updated_at = ? WHERE id = ?").run(
      "error",
      "invalid_route_data",
      now,
      row.id
    );
    parsed.run.status = "error";
    parsed.run.error_message = "invalid_route_data";
    parsed.run.updated_at = now;
  }
  return parsed.run;
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
  const updatedAfter = req.query.updated_after ? String(req.query.updated_after) : null;
  const limitRaw = Number(req.query.limit ?? 200);
  const offsetRaw = Number(req.query.offset ?? 0);
  const limit = Number.isFinite(limitRaw) ? Math.max(1, Math.min(1000, Math.floor(limitRaw))) : 200;
  const offset = Number.isFinite(offsetRaw) ? Math.max(0, Math.floor(offsetRaw)) : 0;

  const where = [];
  const params = [];
  if (status) {
    where.push("status = ?");
    params.push(status);
  }
  if (updatedAfter) {
    where.push("updated_at > ?");
    params.push(updatedAfter);
  }

  const whereClause = where.length > 0 ? `WHERE ${where.join(" AND ")}` : "";
  const sql = `SELECT * FROM flush_runs ${whereClause} ORDER BY started_at ASC LIMIT ? OFFSET ?`;
  const rows = db.prepare(sql).all(...params, limit, offset);
  res.json(rows.map(normalizeRunRow));
});

app.post("/api/flushes", (req, res) => {
  const body = req.body || {};
  if (!body.origin || typeof body.origin.lat !== "number" || typeof body.origin.lng !== "number") {
    res.status(400).json({ error: "invalid payload" });
    return;
  }

  const id = body.id ? String(body.id) : randomUUID();
  const existing = db.prepare("SELECT id FROM flush_runs WHERE id = ?").get(id);
  if (existing) {
    res.status(409).json({ error: "id already exists", id });
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
  `).run(
    id,
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

  const row = db.prepare("SELECT * FROM flush_runs WHERE id = ?").get(id);
  const parsed = normalizeRunRow(row);
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

  const existing = db.prepare("SELECT * FROM flush_runs WHERE id = ?").get(id);
  if (!existing) {
    res.status(404).json({ error: "not found" });
    return;
  }

  const alreadyTerminal = existing.status === "arrived" || existing.status === "error";
  if (alreadyTerminal && existing.status === status) {
    const parsedExisting = normalizeRunRow(existing);
    res.json(parsedExisting);
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
  const parsed = normalizeRunRow(row);
  broadcastSse("flush_status_updated", {
    id: parsed.id,
    status: parsed.status,
    error_message: parsed.error_message,
    updated_at: parsed.updated_at
  });
  res.json(parsed);
});

function runRetentionSweep() {
  const cutoff = new Date(Date.now() - RETENTION_DAYS * 24 * 60 * 60 * 1000).toISOString();
  const result = db
    .prepare("DELETE FROM flush_runs WHERE status IN ('arrived','error') AND updated_at < ?")
    .run(cutoff);
  if (import.meta.env?.DEV || process.env.NODE_ENV !== "production") {
    if ((result?.changes || 0) > 0) {
      console.log(`[retention] deleted ${result.changes} rows older than ${RETENTION_DAYS}d`);
    }
  }
}

setInterval(() => {
  for (const client of Array.from(sseClients)) {
    try {
      client.write(`event: heartbeat\ndata: ${JSON.stringify({ now: new Date().toISOString() })}\n\n`);
    } catch {
      sseClients.delete(client);
    }
  }
}, 25000);

setInterval(runRetentionSweep, RETENTION_SWEEP_MINUTES * 60 * 1000);

app.listen(PORT, () => {
  console.log(`flush-server listening on :${PORT}`);
  console.log(`[cors] ${ALLOW_ALL_CORS ? "allow-all" : `allowlist=${Array.from(ALLOWED_ORIGINS).join(",")}`}`);
  console.log(`[retention] ${RETENTION_DAYS}d every ${RETENTION_SWEEP_MINUTES}m`);
});
