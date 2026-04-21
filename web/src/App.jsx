import { memo, useCallback, useEffect, useMemo, useRef, useState } from "react";
import "./App.css";

import "leaflet/dist/leaflet.css";
import { divIcon } from "leaflet";
import { MapContainer, TileLayer, GeoJSON, CircleMarker, Marker, Popup, Polyline, Tooltip, useMapEvents } from "react-leaflet";

const users = ["Tom", "Steph", "Molly", "Delilah", "Luella"];
const APP_LAST_UPDATED = "2026-02-12 09:05 UTC";
const PERF_MODE_DEFAULT = "mobile";
const ANIMATION_FPS_TARGET = 30;
const UI_SYNC_FPS = 6;
const SHOW_PIPE_GLOW_DEFAULT = false;
const SEGMENT_INDEX_CELL_M = 80;
const NODE_INDEX_CELL_M = 120;
const FALLBACK_MAX_BRIDGE_M = 250;
const ROUTING_FALLBACK_DEFAULT = "guarantee_endpoint";
const PIPE_DATASETS = [
  {
    id: "melbourne",
    label: "Melbourne",
    path: "/Sewerage_Network_Main_Pipelines.geojson",
    center: { lat: -37.885, lng: 145.01 }
  },
  {
    id: "gold_coast",
    label: "Gold Coast",
    path: "/goldcoast-sewer-pipes-non-pressurised.normalized.geojson",
    center: { lat: -28.03, lng: 153.39 }
  },
  {
    id: "bundaberg",
    label: "Bundaberg",
    path: "/bundaberg-sewerage-mains.normalized.geojson",
    center: { lat: -24.87, lng: 152.35 }
  }
];
const DEFAULT_PIPE_DATASET_ID = "melbourne";
const API_BASE_URL = import.meta.env.VITE_API_BASE_URL || "http://localhost:8787";
const TRUE_ENDPOINT_NAME_PRIORITY = [
  "WESTERN TRUNK SEWER",
  "SOUTH EASTERN TRUNK SEWER",
  "SOUTH EASTERN OUTFALL"
];
const MAX_CONNECTOR_VISITS = 50000;
const DEBUG_PIPE_HOPS = false;
const CONNECTOR_WARN_MS = 150;
const POO_ICON = divIcon({
  className: "poo-marker",
  html: "💩",
  iconSize: [24, 24],
  iconAnchor: [12, 12]
});

// Fallback centre (Melbourne / Elsternwick-ish) if geolocation is blocked/unavailable
const FALLBACK_CENTER = { lat: -37.885, lng: 145.01 };

// Public OSRM demo server (OK for prototyping; consider self-hosting for reliability/scale)
const OSRM_ROUTE_URL = "https://router.project-osrm.org/route/v1/driving";

// Street-route travel speed (m/s) approximation for suburban catchment/house-branch drains.
// Typical self-cleansing/flow velocities are often ~0.6–1.5 m/s; we use a mid value.
const STREET_SPEED_MPS = 1.1;

// Snap tolerance (metres) when determining pipe connectivity by endpoints
const NODE_SNAP_TOL_M = 8;

// Simulation safety clamps
const PIPE_SPEED_MIN_MPS = 0.2;

const R_MERC = 6378137;

function perfLog(label, payload) {
  if (!import.meta.env.DEV) return;
  if (payload === undefined) {
    console.log(`[PERF] ${label}`);
    return;
  }
  console.log(`[PERF] ${label}`, payload);
}

async function apiFetch(path, options = {}) {
  const res = await fetch(`${API_BASE_URL}${path}`, {
    ...options,
    headers: {
      "Content-Type": "application/json",
      ...(options.headers || {})
    }
  });
  if (!res.ok) {
    const text = await res.text();
    throw new Error(`${path} failed: ${res.status} ${text}`);
  }
  return res.status === 204 ? null : res.json();
}

function clamp(n, a, b) {
  return Math.max(a, Math.min(b, n));
}

function toNum(v) {
  const n = typeof v === "number" ? v : parseFloat(v);
  return Number.isFinite(n) ? n : null;
}

function normaliseSewerName(v) {
  return String(v || "")
    .toUpperCase()
    .replace(/\s+/g, " ")
    .replace(/[^\w\s]/g, "")
    .trim();
}

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

function bearingDeg(a, b) {
  const lat1 = (a.lat * Math.PI) / 180;
  const lat2 = (b.lat * Math.PI) / 180;
  const dLng = ((b.lng - a.lng) * Math.PI) / 180;

  const y = Math.sin(dLng) * Math.cos(lat2);
  const x = Math.cos(lat1) * Math.sin(lat2) - Math.sin(lat1) * Math.cos(lat2) * Math.cos(dLng);
  const brng = (Math.atan2(y, x) * 180) / Math.PI;
  return (brng + 360) % 360;
}

function angleDiffDeg(a, b) {
  let d = Math.abs(a - b) % 360;
  if (d > 180) d = 360 - d;
  return d;
}


function routeDistanceMeters(route) {
  if (!Array.isArray(route) || route.length < 2) return 0;
  let d = 0;
  for (let i = 1; i < route.length; i++) {
    d += metersBetween(route[i - 1], route[i]);
  }
  return d;
}

function interpolatePoint(a, b, f) {
  return {
    lat: a.lat + (b.lat - a.lat) * f,
    lng: a.lng + (b.lng - a.lng) * f
  };
}

function locateAlongPath(path, metersFromStart) {
  if (!Array.isArray(path) || path.length === 0) return { point: null, nextIdx: 0, traveledM: 0 };
  if (path.length === 1) return { point: path[0], nextIdx: 1, traveledM: 0 };
  const clamped = Math.max(0, metersFromStart);
  let rem = clamped;
  for (let i = 1; i < path.length; i++) {
    const seg = metersBetween(path[i - 1], path[i]);
    if (seg <= 0) continue;
    if (rem <= seg) {
      const f = rem / seg;
      return { point: interpolatePoint(path[i - 1], path[i], f), nextIdx: i, traveledM: clamped };
    }
    rem -= seg;
  }
  return { point: path[path.length - 1], nextIdx: path.length, traveledM: clamped };
}

function remainingDistanceOnPath(path, idx, currentLL) {
  if (!Array.isArray(path) || !currentLL) return 0;
  const target = path[idx];
  if (!target) return 0;
  let d = metersBetween(currentLL, target);
  for (let i = idx + 1; i < path.length; i++) {
    d += metersBetween(path[i - 1], path[i]);
  }
  return d;
}

function remainingTimeOnPath(path, idx, currentLL, byObjectId, fallbackSpeed) {
  if (!Array.isArray(path) || !currentLL) return 0;
  const target = path[idx];
  if (!target) return 0;

  const segSpeed = (waypoint) => {
    if (byObjectId && waypoint?.objectId != null) {
      const v = toNum(byObjectId.get(waypoint.objectId)?.properties?._v_half_mps);
      if (v > 0) return Math.max(PIPE_SPEED_MIN_MPS, v);
    }
    return fallbackSpeed;
  };

  let t = metersBetween(currentLL, target) / segSpeed(target);
  for (let i = idx + 1; i < path.length; i++) {
    t += metersBetween(path[i - 1], path[i]) / segSpeed(path[i]);
  }
  return t;
}

function formatEta(sec) {
  if (!Number.isFinite(sec) || sec < 0) return "—";
  const s = Math.max(0, Math.round(sec));
  if (s < 60) return `${s}s`;
  const h = Math.floor(s / 3600);
  const m = Math.floor((s % 3600) / 60);
  const ss = s % 60;
  if (h > 0) return `${h}:${String(m).padStart(2, "0")}:${String(ss).padStart(2, "0")}`;
  return `${m}:${String(ss).padStart(2, "0")}`;
}

function toDisplaySpeed(v) {
  return Number.isFinite(v) ? v.toFixed(2) : "—";
}

function projectToXYMeters(origin, p) {
  const lat0 = (origin.lat * Math.PI) / 180;
  const dLat = ((p.lat - origin.lat) * Math.PI) / 180;
  const dLng = ((p.lng - origin.lng) * Math.PI) / 180;
  const R = 6371000;
  return {
    x: dLng * Math.cos(lat0) * R,
    y: dLat * R
  };
}

function unprojectFromXYMeters(origin, xy) {
  const lat0 = (origin.lat * Math.PI) / 180;
  const R = 6371000;
  const dLat = xy.y / R;
  const dLng = xy.x / (Math.cos(lat0) * R);
  return {
    lat: origin.lat + (dLat * 180) / Math.PI,
    lng: origin.lng + (dLng * 180) / Math.PI
  };
}

function closestPointOnSegment(a, b, p) {
  // Work in a local metres-space around a (good for short segments)
  const origin = a;
  const A = projectToXYMeters(origin, a);
  const B = projectToXYMeters(origin, b);
  const P = projectToXYMeters(origin, p);

  const ABx = B.x - A.x;
  const ABy = B.y - A.y;

  const APx = P.x - A.x;
  const APy = P.y - A.y;

  const ab2 = ABx * ABx + ABy * ABy;
  const t = ab2 > 0 ? clamp((APx * ABx + APy * ABy) / ab2, 0, 1) : 0;

  const Q = { x: A.x + ABx * t, y: A.y + ABy * t };
  const qLL = unprojectFromXYMeters(origin, Q);

  const dx = P.x - Q.x;
  const dy = P.y - Q.y;
  const dist = Math.sqrt(dx * dx + dy * dy);

  return { point: qLL, dist, t };
}

function gridKey(pt, cellMeters) {
  const mPerDegLat = 111320;
  const mPerDegLng = 111320 * Math.cos((pt.lat * Math.PI) / 180);
  const x = Math.round((pt.lng * mPerDegLng) / cellMeters);
  const y = Math.round((pt.lat * mPerDegLat) / cellMeters);
  return `${x},${y}`;
}

function flattenFeatureCoords(ft) {
  const g = ft && ft.geometry;
  if (!g) return [];

  const toLL = (c) => ({ lat: c[1], lng: c[0] });

  if (g.type === "LineString") {
    return Array.isArray(g.coordinates) ? g.coordinates.map(toLL) : [];
  }

  if (g.type === "MultiLineString") {
    const parts = Array.isArray(g.coordinates) ? g.coordinates : [];
    const out = [];
    for (const part of parts) {
      if (!Array.isArray(part) || part.length < 2) continue;
      for (let i = 0; i < part.length; i++) {
        const ll = toLL(part[i]);
        const last = out[out.length - 1];
        if (last && metersBetween(last, ll) < 0.01) continue;
        out.push(ll);
      }
    }
    return out;
  }

  return [];
}


function parseDirFromProps(props) {
  const raw =
    props?.DIR ??
    props?.Dir ??
    props?.dir ??
    props?.DIRECTION ??
    props?.Direction ??
    props?.direction ??
    null;

  if (raw === null || raw === undefined) return null;

  const v = String(raw).trim().toLowerCase();

  if (v === "u_to_d" || v === "u-to-d" || v === "u to d" || v === "u2d" || v === "uto_d") return "u_to_d";
  if (v === "d_to_u" || v === "d-to-u" || v === "d to u" || v === "d2u" || v === "dto_u") return "d_to_u";

  return null;
}



function findNearestPipeContact(geojson, start) {
  const features = Array.isArray(geojson?.features) ? geojson.features : [];
  let best = null;

  for (const ft of features) {
    const g = ft?.geometry;
    if (!g) continue;

    const considerLineString = (coords, linePartIndex) => {
      for (let i = 0; i < coords.length - 1; i++) {
        const a = { lng: coords[i][0], lat: coords[i][1] };
        const b = { lng: coords[i + 1][0], lat: coords[i + 1][1] };
        const res = closestPointOnSegment(a, b, start);
        if (!best || res.dist < best.dist) {
          best = {
            dist: res.dist,
            point: res.point,
            feature: ft,
            partIndex: linePartIndex,
            segIndex: i,
            segA: a,
            segB: b
          };
        }
      }
    };

    if (g.type === "LineString") {
      considerLineString(g.coordinates || [], 0);
    } else if (g.type === "MultiLineString") {
      const lines = g.coordinates || [];
      for (let li = 0; li < lines.length; li++) {
        considerLineString(lines[li] || [], li);
      }
    }
  }

  return best;
}

function findNearestPipeContactWithIndex(features, segmentIndex, start) {
  if (!segmentIndex?.cells) return null;

  const originKey = segmentCellKeyFromLngLat(start.lng, start.lat, segmentIndex.cellM);
  const [cx, cy] = originKey.split(",").map(Number);
  let best = null;
  const maxRing = 12;

  for (let ring = 0; ring <= maxRing; ring++) {
    const seen = new Set();

    for (let x = cx - ring; x <= cx + ring; x++) {
      for (let y = cy - ring; y <= cy + ring; y++) {
        if (ring > 0 && x !== cx - ring && x !== cx + ring && y !== cy - ring && y !== cy + ring) continue;
        const key = `${x},${y}`;
        const segs = segmentIndex.cells.get(key);
        if (!segs) continue;

        for (const seg of segs) {
          const segKey = `${seg.featureIndex}:${seg.partIndex}:${seg.segIndex}`;
          if (seen.has(segKey)) continue;
          seen.add(segKey);

          const res = closestPointOnSegment(seg.a, seg.b, start);
          if (!best || res.dist < best.dist) {
            best = {
              dist: res.dist,
              point: res.point,
              feature: features[seg.featureIndex],
              partIndex: seg.partIndex,
              segIndex: seg.segIndex,
              segA: seg.a,
              segB: seg.b
            };
          }
        }
      }
    }

    if (best && best.dist <= (ring + 1) * segmentIndex.cellM) break;
  }

  return best;
}

async function fetchOsrmRoute(start, end) {
  const url =
    `${OSRM_ROUTE_URL}/` +
    `${start.lng},${start.lat};${end.lng},${end.lat}` +
    `?overview=full&geometries=geojson&alternatives=false&steps=false`;

  const res = await fetch(url);
  if (!res.ok) throw new Error(`OSRM route failed: ${res.status}`);
  const json = await res.json();

  const coords = json?.routes?.[0]?.geometry?.coordinates;
  if (!Array.isArray(coords) || coords.length < 2) throw new Error("OSRM returned no route geometry");

  // OSRM returns [lng, lat]
  return coords.map((c) => ({ lng: c[0], lat: c[1] }));
}

function mercatorMetersFromLngLat(lng, lat) {
  const x = (R_MERC * lng * Math.PI) / 180;
  const latClamped = clamp(lat, -85.05112878, 85.05112878);
  const y = R_MERC * Math.log(Math.tan(Math.PI / 4 + (latClamped * Math.PI) / 360));
  return { x, y };
}

function nodeKeyFromLngLat(lng, lat, tolM) {
  const m = mercatorMetersFromLngLat(lng, lat);
  const kx = Math.round(m.x / tolM);
  const ky = Math.round(m.y / tolM);
  return `${kx}_${ky}`;
}

function segmentCellKeyFromLngLat(lng, lat, cellM) {
  const m = mercatorMetersFromLngLat(lng, lat);
  const x = Math.floor(m.x / cellM);
  const y = Math.floor(m.y / cellM);
  return `${x},${y}`;
}

function buildSegmentSpatialIndex(features, cellM = SEGMENT_INDEX_CELL_M) {
  const cells = new Map();

  function pushSegment(seg, minX, minY, maxX, maxY) {
    for (let x = minX; x <= maxX; x++) {
      for (let y = minY; y <= maxY; y++) {
        const key = `${x},${y}`;
        const arr = cells.get(key);
        if (arr) arr.push(seg);
        else cells.set(key, [seg]);
      }
    }
  }

  features.forEach((ft, featureIndex) => {
    const g = ft?.geometry;
    if (!g) return;

    const addLine = (coords, partIndex) => {
      for (let i = 0; i < coords.length - 1; i++) {
        const a = { lng: coords[i][0], lat: coords[i][1] };
        const b = { lng: coords[i + 1][0], lat: coords[i + 1][1] };
        const am = mercatorMetersFromLngLat(a.lng, a.lat);
        const bm = mercatorMetersFromLngLat(b.lng, b.lat);
        const minX = Math.floor(Math.min(am.x, bm.x) / cellM);
        const maxX = Math.floor(Math.max(am.x, bm.x) / cellM);
        const minY = Math.floor(Math.min(am.y, bm.y) / cellM);
        const maxY = Math.floor(Math.max(am.y, bm.y) / cellM);
        pushSegment({ featureIndex, partIndex, segIndex: i, a, b }, minX, minY, maxX, maxY);
      }
    };

    if (g.type === "LineString") addLine(g.coordinates || [], 0);
    else if (g.type === "MultiLineString") {
      const lines = g.coordinates || [];
      for (let li = 0; li < lines.length; li++) addLine(lines[li] || [], li);
    }
  });

  return { cellM, cells };
}

function buildNodeSpatialIndex(nodes, cellM = NODE_INDEX_CELL_M) {
  const cells = new Map();
  for (const node of nodes) {
    const key = segmentCellKeyFromLngLat(node.lng, node.lat, cellM);
    const arr = cells.get(key);
    if (arr) arr.push(node);
    else cells.set(key, [node]);
  }
  return { cellM, cells };
}

function findNearestDownstreamNode(pointLL, nodeSpatialIndex, maxMeters, excludeKeys = new Set()) {
  if (!nodeSpatialIndex?.cells) return null;
  const originKey = segmentCellKeyFromLngLat(pointLL.lng, pointLL.lat, nodeSpatialIndex.cellM);
  const [cx, cy] = originKey.split(",").map(Number);
  const maxRing = Math.max(1, Math.ceil(maxMeters / nodeSpatialIndex.cellM));
  let best = null;
  let bestDist = Infinity;

  for (let ring = 0; ring <= maxRing; ring++) {
    for (let x = cx - ring; x <= cx + ring; x++) {
      for (let y = cy - ring; y <= cy + ring; y++) {
        if (ring > 0 && x !== cx - ring && x !== cx + ring && y !== cy - ring && y !== cy + ring) continue;
        const nodes = nodeSpatialIndex.cells.get(`${x},${y}`);
        if (!nodes) continue;
        for (const node of nodes) {
          if (excludeKeys.has(node.key)) continue;
          if (!Array.isArray(node.outObjectIds) || node.outObjectIds.length === 0) continue;
          const d = metersBetween(pointLL, { lat: node.lat, lng: node.lng });
          if (d < bestDist) {
            bestDist = d;
            best = node;
          }
        }
      }
    }
  }

  if (!best || bestDist > maxMeters) return null;
  return { node: best, dist: bestDist };
}

function nearestPointOnOrderedPipe(ord, fromPoint) {
  if (!Array.isArray(ord) || ord.length < 2 || !fromPoint) return null;
  let best = null;
  for (let i = 0; i < ord.length - 1; i++) {
    const a = ord[i];
    const b = ord[i + 1];
    const res = closestPointOnSegment(a, b, fromPoint);
    if (!best || res.dist < best.dist) {
      best = { point: res.point, dist: res.dist };
    }
  }
  return best;
}

function nearestNodeKeyForPoint(fromPoint, nodeIndex) {
  if (!fromPoint || !nodeIndex || nodeIndex.size === 0) return null;
  let bestKey = null;
  let bestDist = Infinity;
  for (const [key, n] of nodeIndex.entries()) {
    const d = metersBetween(fromPoint, { lat: n.lat, lng: n.lng });
    if (d < bestDist) {
      bestDist = d;
      bestKey = key;
    }
  }
  return bestKey;
}

class MinHeap {
  constructor() {
    this.data = [];
  }

  push(item) {
    this.data.push(item);
    this.#bubbleUp(this.data.length - 1);
  }

  pop() {
    if (this.data.length === 0) return null;
    const top = this.data[0];
    const end = this.data.pop();
    if (this.data.length > 0) {
      this.data[0] = end;
      this.#sinkDown(0);
    }
    return top;
  }

  get size() {
    return this.data.length;
  }

  #bubbleUp(n) {
    while (n > 0) {
      const p = Math.floor((n - 1) / 2);
      if (this.data[p].dist <= this.data[n].dist) break;
      [this.data[p], this.data[n]] = [this.data[n], this.data[p]];
      n = p;
    }
  }

  #sinkDown(n) {
    const len = this.data.length;
    while (true) {
      const l = 2 * n + 1;
      const r = l + 1;
      let smallest = n;
      if (l < len && this.data[l].dist < this.data[smallest].dist) smallest = l;
      if (r < len && this.data[r].dist < this.data[smallest].dist) smallest = r;
      if (smallest === n) break;
      [this.data[smallest], this.data[n]] = [this.data[n], this.data[smallest]];
      n = smallest;
    }
  }
}

function findBestPurpleConnectorPath({
  fromPoint,
  fromNodeKey,
  nodeAdj,
  reachableEntryNodeKeys,
  nodeIndex,
  pipeCanReachTerminal,
  pipeDistToTerminalM
}) {
  if (!fromPoint || !nodeAdj || !reachableEntryNodeKeys || !nodeIndex || !pipeCanReachTerminal || !pipeDistToTerminalM) return null;
  const t0 = performance.now();
  const startKey = fromNodeKey && nodeIndex.has(fromNodeKey) ? fromNodeKey : nearestNodeKeyForPoint(fromPoint, nodeIndex);
  if (!startKey) return null;

  const dist = new Map([[startKey, 0]]);
  const prev = new Map();
  const heap = new MinHeap();
  heap.push({ key: startKey, dist: 0 });
  const visited = new Set();
  let visits = 0;

  while (heap.size > 0 && visits < MAX_CONNECTOR_VISITS) {
    visits += 1;
    const next = heap.pop();
    if (!next) break;
    const currKey = next.key;
    const currDist = next.dist;
    if (currDist > (dist.get(currKey) ?? Infinity)) continue;
    if (visited.has(currKey)) continue;
    visited.add(currKey);

    const edges = nodeAdj.get(currKey) || [];
    for (const edge of edges) {
      const nextKey = edge.toKey;
      const nd = currDist + (edge.meters || 0);
      if (nd < (dist.get(nextKey) ?? Infinity)) {
        dist.set(nextKey, nd);
        prev.set(nextKey, { fromKey: currKey, edge });
        if (!visited.has(nextKey)) heap.push({ key: nextKey, dist: nd });
      }
    }
  }

  let best = null;
  for (const entryKey of reachableEntryNodeKeys) {
    if (!dist.has(entryKey)) continue;
    const entryNode = nodeIndex.get(entryKey);
    if (!entryNode || !Array.isArray(entryNode.outObjectIds) || entryNode.outObjectIds.length === 0) continue;

    let resumeStartPipeId = null;
    let downstreamM = Infinity;
    for (const oid of entryNode.outObjectIds) {
      if (!pipeCanReachTerminal.has(oid)) continue;
      const d = pipeDistToTerminalM.get(oid);
      if (!Number.isFinite(d)) continue;
      if (d < downstreamM) {
        downstreamM = d;
        resumeStartPipeId = oid;
      }
    }
    if (resumeStartPipeId === null) continue;

    const connectorM = dist.get(entryKey) ?? Infinity;
    const totalM = connectorM + downstreamM;
    if (!best || totalM < best.totalM || (totalM === best.totalM && connectorM < best.connectorMeters)) {
      best = { entryKey, resumeStartPipeId, connectorMeters: connectorM, totalM };
    }
  }
  if (!best) return null;

  const pathEdges = [];
  let k = best.entryKey;
  while (k !== startKey) {
    const link = prev.get(k);
    if (!link) break;
    pathEdges.push(link.edge);
    k = link.fromKey;
  }
  pathEdges.reverse();

  const connectorPathCoords = [];
  for (const edge of pathEdges) {
    const coords = edge.coords || [];
    for (let i = 0; i < coords.length; i++) {
      const pt = coords[i];
      const last = connectorPathCoords[connectorPathCoords.length - 1];
      if (last && metersBetween(last, pt) < 0.2) continue;
      connectorPathCoords.push(pt);
    }
  }
  const entryNode = nodeIndex.get(best.entryKey);
  const entryPoint = entryNode ? { lat: entryNode.lat, lng: entryNode.lng } : fromPoint;
  const elapsed = performance.now() - t0;
  if (import.meta.env.DEV && elapsed > CONNECTOR_WARN_MS) {
    console.warn("[CONNECTOR] slow solve", { ms: Math.round(elapsed), visits, startKey });
  }
  return {
    connectorPathCoords,
    connectorMeters: best.connectorMeters,
    entryNodeKey: best.entryKey,
    entryPoint,
    resumeStartPipeId: best.resumeStartPipeId
  };
}

function manningNFromMaterial(materialRaw) {
  const m = String(materialRaw || "").toUpperCase();

  if (m.includes("PVC") || m.includes("UPVC") || m.includes("HDPE") || m.includes("ABS")) return 0.009;
  if (m.includes("VC") || m.includes("VIT") || m.includes("CLAY")) return 0.011;
  if (m.includes("CON") || m.includes("RC") || m.includes("CONC")) return 0.013;
  if (m.includes("CI") || m.includes("DICL") || m.includes("IRON")) return 0.012;
  if (m.includes("GRP")) return 0.01;
  if (m.includes("BRICK") || m.includes("BWK") || m.includes("BLK")) return 0.015;

  return 0.013;
}

function dbgName(p) {
  const v = p?.SEWER_NAME ?? p?.SEWERNAME ?? "";
  return String(v).trim();
}

function computeHalfFullVelocityMps(props) {
  const n = manningNFromMaterial(props?.MATERIAL);

  const grade = toNum(props?.GRADE);
  const upIL = toNum(props?.UPSTREAM_IL);
  const downIL = toNum(props?.DOWNSTREAM_IL);
  const len = toNum(props?.PIPE_LENGTH);

  let S = null;
  if (grade !== null) {
    S = Math.abs(grade);
  } else if (upIL !== null && downIL !== null && len !== null && len > 0) {
    S = Math.abs((upIL - downIL) / len);
  }

  if (S === null || !Number.isFinite(S) || S <= 0) {
    return { n, S: S || 0, v: 0 };
  }

  const wMm = toNum(props?.PIPE_WIDTH);
  const hMm = toNum(props?.PIPE_HEIGHT);

  // Treat height==0 or missing as circular diameter=width
  const isCircular = wMm !== null && (hMm === null || hMm === 0);

  let R = null;

  if (isCircular) {
    const D = (wMm || 0) / 1000;
    if (D > 0) {
      // For a circular pipe: hydraulic radius R = D/4 for both full and exactly half-full
      R = D / 4;
    }
  } else {
    const w = (wMm || 0) / 1000;
    const h = (hMm || 0) / 1000;
    if (w > 0 && h > 0) {
      const A = w * h;
      const P = 2 * (w + h);
      R = P > 0 ? A / P : null;
    }
  }

  if (R === null || !Number.isFinite(R) || R <= 0) {
    return { n, S, v: 0 };
  }

  const v = (1 / n) * Math.pow(R, 2 / 3) * Math.sqrt(S);
  return { n, S, v: Number.isFinite(v) ? v : 0 };
}

function chooseNextPipeLowestDownIL(nextIds, byObjectId, currentProps) {
  if (!Array.isArray(nextIds) || nextIds.length === 0) return null;

  const currentName = normaliseSewerName(currentProps?.SEWER_NAME || currentProps?.SEWERNAME);

  // Prefer candidates with the same sewer/main name (helps across pump stations)
  let candidateIds = nextIds;
  if (currentName) {
    const sameName = nextIds.filter((id) => {
      const ft = byObjectId.get(id);
      const p = ft?.properties || {};
      const nm = normaliseSewerName(p.SEWER_NAME || p.SEWERNAME);
	  return nm && nm === currentName;

    });
    if (sameName.length > 0) candidateIds = sameName;
  }

  // 1) Prefer lowest downstream IL if available
  let bestId = null;
  let bestDown = Infinity;

  for (const id of candidateIds) {
    const ft = byObjectId.get(id);
    const p = ft?.properties || {};
    const d = toNum(p.DOWNSTREAM_IL);

    if (d !== null && d < bestDown) {
      bestDown = d;
      bestId = id;
    }
  }

  if (bestId !== null) return bestId;

  // 2) If no ILs, prefer segment candidate if present and in list
  const segCand = currentProps?._segment_candidate_objectid;
  if (segCand && candidateIds.includes(segCand)) return segCand;

  // 3) Otherwise, prefer longest pipe length
  let bestLenId = null;
  let bestLen = -Infinity;

  for (const id of candidateIds) {
    const ft = byObjectId.get(id);
    const p = ft?.properties || {};
    const len = toNum(p.PIPE_LENGTH);

    if (len !== null && len > bestLen) {
      bestLen = len;
      bestLenId = id;
    }
  }

  if (bestLenId !== null) return bestLenId;

  return candidateIds[0] ?? null;
}


function _chooseNextPipeWithLookahead(candidateIds, byObjectId, currProps, currId, prevId, visited) {
  const ids0 = Array.isArray(candidateIds) ? candidateIds : [];
  if (ids0.length === 0) return null;

  // Prefer not to bounce straight back to the immediately-previous pipe
  const idsNoPrev = ids0.filter((id) => id !== prevId);

  // Prefer unvisited candidates if any exist (but don't hard-fail if all are visited)
  const idsBase = idsNoPrev.length > 0 ? idsNoPrev : ids0;
  const idsUnvisited = idsBase.filter((id) => !visited.has(id));
  const ids = idsUnvisited.length > 0 ? idsUnvisited : idsBase;

  if (ids.length === 1) return ids[0];


  return chooseBestByLookahead(ids, byObjectId, currProps, currId, prevId, visited);
}

function chooseBestByLookahead(ids, byObjectId, currProps, currId, prevId, visited) {
  if (ids.length === 1) return ids[0];

  let bestId = null;
  let bestScore = Infinity;

  for (const id of ids) {
    const score = lookaheadScore(id, byObjectId, currProps, currId, prevId, visited, 10);
    if (score < bestScore) {
      bestScore = score;
      bestId = id;
    }
  }

  // Fallback if something weird happens
  if (bestId === null) bestId = chooseNextPipeLowestDownIL(ids, byObjectId, currProps);
  return bestId;
}

// Lower score is better
function lookaheadScore(startId, byObjectId, currProps, currId, prevId, visited, depth) {
  let total = 0;

  let hops = 0;
  let id = startId;
  let prev = currId;

  // Local cycle detection independent of global visited
  const local = new Set([currId, prevId]);

  let lastDown = toNum(currProps?.DOWNSTREAM_IL);

  while (id != null && hops < depth) {
    if (visited.has(id)) {
      total += 50; // avoid re-entering already-traced path
      break;
    }
    if (local.has(id)) {
      total += 200; // local cycle
      break;
    }
    local.add(id);

    const ft = byObjectId.get(id);
    if (!ft) {
      total += 100;
      break;
    }

    const p = ft.properties || {};
    const d = toNum(p.DOWNSTREAM_IL);

    // We do NOT enforce "downhill" here because pump stations can legitimately go uphill.
    // Only apply a tiny preference for pipes that have IL data (more deterministic).
    if (d === null) total += 2;

    lastDown = d !== null ? d : lastDown;

    const nextIds = Array.isArray(p._nextObjectIds) ? p._nextObjectIds : [];
    const stepIds = nextIds.filter((x) => x !== prev);
    const stepId = stepIds.length > 0 ? chooseNextPipeLowestDownIL(stepIds, byObjectId, p) : null;

    prev = id;
    id = stepId;
    hops += 1;
  }

  // Prefer paths that can continue (avoid dead-ends)
  total += (depth - hops) * 20;

  return total;
}

function _findNearestObjectIdBySewerNameFromByObjectId(byObjectId, pointLL, sewerNameRaw, excludeIds, maxMeters) {
  const target = String(sewerNameRaw || "").trim();
  if (!target) return null;

  let bestId = null;
  let bestDist = Infinity;

  for (const [id, ft] of byObjectId.entries()) {
    if (excludeIds && excludeIds.has(id)) continue;

    const p = ft?.properties || {};
    const nm = String(p.SEWER_NAME || p.SEWERNAME || "").trim();
    if (!nm || nm !== target) continue;

    const coords = flattenFeatureCoords(ft);
    if (!coords || coords.length < 2) continue;

    // distance to polyline (segment-by-segment)
    for (let i = 0; i < coords.length - 1; i++) {
      const a = coords[i];
      const b = coords[i + 1];
      const res = closestPointOnSegment(a, b, pointLL);
      if (res.dist < bestDist) {
        bestDist = res.dist;
        bestId = id;
      }
    }
  }

  if (bestId !== null && bestDist <= maxMeters) return { objectId: bestId, dist: bestDist };
  return null;
}


function orderedCoordsForPipe(ft) {
  const p = ft?.properties || {};
  const dir = String(p._dir || "u_to_d");
  const coords = flattenFeatureCoords(ft);
  return dir === "d_to_u" ? coords.slice().reverse() : coords;
}

function chooseNextPipeByBearing(nextIds, byObjectId, currOrderedCoords, prevId, visited) {
  const ids0 = Array.isArray(nextIds) ? nextIds : [];
  const ids1 = ids0.filter((id) => id !== prevId && !visited.has(id));
  const ids = ids1.length > 0 ? ids1 : ids0.filter((id) => id !== prevId);

  if (ids.length === 0) return null;
  if (ids.length === 1) return ids[0];

  if (!currOrderedCoords || currOrderedCoords.length < 2) {
    return ids.slice().sort((a, b) => a - b)[0] ?? null;
  }

  const n = currOrderedCoords.length;
  const a = currOrderedCoords[Math.max(0, n - 2)];
  const b = currOrderedCoords[n - 1];
  const currBrng = bearingDeg(a, b);

  let bestId = null;
  let bestDelta = Infinity;

  for (const id of ids) {
    const ft = byObjectId.get(id);
    if (!ft) continue;
    const ord = orderedCoordsForPipe(ft);
    if (ord.length < 2) continue;

    const candBrng = bearingDeg(ord[0], ord[1]);
    const delta = angleDiffDeg(currBrng, candBrng);
    if (delta < bestDelta) {
      bestDelta = delta;
      bestId = id;
    }
  }

  return bestId !== null ? bestId : (ids.slice().sort((a, b) => a - b)[0] ?? null);
}

function buildPipePlanFromObjectId(
  startObjectId,
  startPoint,
  byObjectId,
  nodeIndex,
  maxHops = 2000,
  initialVisited = null,
  pipeCanReachTerminal = null,
  nextHopToTerminal = null
) {
  // DIR-first traversal:
  // - Each pipe has an explicit DIR (u_to_d / d_to_u). We treat this as authoritative.
  // - Connectivity is: current pipe FLOW-END node -> next pipe FLOW-START node.
  // - `_nextObjectIds` is built from endpoint snapping + flow-start matching (plus a small fallback).
  const plan = [];
  const visited = initialVisited ? new Set(initialVisited) : new Set();
  const visitedCells = new Set();

  let currentId = startObjectId;
  let prevId = null;
  let first = true;
  let endReason = "missing_feature";
  let lastNodeKey = null;
  let lastObjectId = null;
  let terminalNode = null;

  while (currentId !== null && currentId !== undefined && visited.size < maxHops) {
    if (pipeCanReachTerminal && !pipeCanReachTerminal.has(currentId)) {
      endReason = "unreachable_subgraph";
      break;
    }
    if (visited.has(currentId)) {
      endReason = "loop";
      break;
    }
    const ft = byObjectId.get(currentId);
    if (!ft) {
      endReason = "missing_feature";
      break;
    }

    visited.add(currentId);
    lastObjectId = currentId;

    const ord = orderedCoordsForPipe(ft);
    if (ord.length < 2) {
      endReason = "missing_feature";
      break;
    }

    if (first && startPoint) {
      plan.push({ lng: startPoint.lng, lat: startPoint.lat, objectId: currentId });

      let nearestIdx = 0;
      let bestDist = Infinity;
      for (let i = 0; i < ord.length; i++) {
        const d = metersBetween(startPoint, ord[i]);
        if (d < bestDist) {
          bestDist = d;
          nearestIdx = i;
        }
      }

      for (let i = nearestIdx; i < ord.length; i++) {
        const k = gridKey(ord[i], 5);
        if (visitedCells.has(k)) continue;
        visitedCells.add(k);
        plan.push({ ...ord[i], objectId: currentId });
      }

      first = false;
    } else {
      const last = plan[plan.length - 1];
      for (let i = 0; i < ord.length; i++) {
        const pt = ord[i];
        if (last && metersBetween(last, pt) < 0.2) continue;
        const k = gridKey(pt, 5);
        if (visitedCells.has(k)) continue;
        visitedCells.add(k);
        plan.push({ ...pt, objectId: currentId });
      }
    }

    const p = ft.properties || {};
    const nextIds = Array.isArray(p._nextObjectIds) ? p._nextObjectIds : [];
    let nextId = null;
    if (nextHopToTerminal && nextHopToTerminal.has(currentId)) {
      const preferred = nextHopToTerminal.get(currentId);
      if (
        preferred !== null &&
        preferred !== undefined &&
        nextIds.includes(preferred) &&
        !visited.has(preferred) &&
        preferred !== prevId
      ) {
        nextId = preferred;
      }
    }
    if (nextId === null || nextId === undefined) {
      nextId = chooseNextPipeByBearing(nextIds, byObjectId, ord, prevId, visited);
    }
    lastNodeKey = p._downNodeKey || null;

    if (import.meta.env.DEV && DEBUG_PIPE_HOPS && visited.size < 120) {
      console.log(
        "[PIPEHOP] " +
          currentId +
          " -> " +
          nextId +
          ' | name="' +
          dbgName(p) +
          '" | candidates=[' +
          nextIds.join(", ") +
          "]"
      );
    }

    if (nextId === null || nextId === undefined) {
      const dn = lastNodeKey ? nodeIndex?.get(lastNodeKey) : null;
      const isTerminal = !!dn && Array.isArray(dn.outObjectIds) && dn.outObjectIds.length === 0 && Array.isArray(dn.inObjectIds) && dn.inObjectIds.length > 0;
      if (isTerminal) {
        endReason = "terminal";
        terminalNode = { key: dn.key, lat: dn.lat, lng: dn.lng };
      } else {
        endReason = "dead_end";
      }
      break;
    }

    prevId = currentId;
    currentId = nextId;
  }
  if (visited.size >= maxHops && endReason !== "terminal") endReason = "max_hops";

  return {
    coords: plan,
    endReason,
    lastNodeKey,
    lastPoint: plan.length > 0 ? plan[plan.length - 1] : startPoint,
    visitedObjectIds: Array.from(visited),
    lastObjectId,
    terminalNode
  };
}


function _findNearestNodeKeyWithinMeters(nodeIndex, fromKey, maxMeters) {
  const from = nodeIndex.get(fromKey);
  if (!from) return null;

  const fromLL = { lat: from.lat, lng: from.lng };

  let bestKey = null;
  let bestDist = Infinity;

  for (const [key, node] of nodeIndex.entries()) {
    if (key === fromKey) continue;
    if (!node || typeof node.lat !== "number" || typeof node.lng !== "number") continue;

    // Only consider nodes that have at least one outgoing pipe
    if (!Array.isArray(node.outObjectIds) || node.outObjectIds.length === 0) continue;

    const d = metersBetween(fromLL, { lat: node.lat, lng: node.lng });
    if (d <= maxMeters && d < bestDist) {
      bestDist = d;
      bestKey = key;
    }
  }

  return bestKey;
}

function _findNearestPipeObjectIdToPointWithinMeters(geojson, pointLL, excludeObjectId, maxMeters) {
  const features = Array.isArray(geojson?.features) ? geojson.features : [];

  let bestObjectId = null;
  let bestDist = Infinity;

  for (const ft of features) {
    const props = ft?.properties || {};
    const oid = toNum(props.OBJECTID);

    if (oid === null) continue;
    if (excludeObjectId !== null && oid === excludeObjectId) continue;

    const g = ft?.geometry;
    if (!g) continue;

    const considerLineString = (coords) => {
      for (let i = 0; i < coords.length - 1; i++) {
        const a = { lng: coords[i][0], lat: coords[i][1] };
        const b = { lng: coords[i + 1][0], lat: coords[i + 1][1] };
        const res = closestPointOnSegment(a, b, pointLL);
        if (res.dist < bestDist) {
          bestDist = res.dist;
          bestObjectId = oid;
        }
      }
    };

    if (g.type === "LineString") {
      considerLineString(g.coordinates || []);
    } else if (g.type === "MultiLineString") {
      const lines = g.coordinates || [];
      for (const line of lines) considerLineString(line || []);
    }
  }

  if (bestObjectId !== null && bestDist <= maxMeters) return { objectId: bestObjectId, dist: bestDist };
  return null;
}

function _findNearestPipeObjectIdBySewerNameWithinMeters(geojson, pointLL, sewerNameRaw, excludeObjectId, maxMeters) {
  const targetName = normaliseSewerName(sewerNameRaw);
  if (!targetName) return null;

  const features = Array.isArray(geojson?.features) ? geojson.features : [];

  let bestObjectId = null;
  let bestDist = Infinity;

  for (const ft of features) {
    const props = ft?.properties || {};
    const nm = normaliseSewerName(props.SEWER_NAME || props.SEWERNAME);
    if (!nm || nm !== targetName) continue;

    const oid = toNum(props.OBJECTID);
    if (oid === null) continue;
    if (excludeObjectId !== null && oid === excludeObjectId) continue;

    const g = ft?.geometry;
    if (!g) continue;

    const considerLineString = (coords) => {
      for (let i = 0; i < coords.length - 1; i++) {
        const a = { lng: coords[i][0], lat: coords[i][1] };
        const b = { lng: coords[i + 1][0], lat: coords[i + 1][1] };
        const res = closestPointOnSegment(a, b, pointLL);
        if (res.dist < bestDist) {
          bestDist = res.dist;
          bestObjectId = oid;
        }
      }
    };

    if (g.type === "LineString") {
      considerLineString(g.coordinates || []);
    } else if (g.type === "MultiLineString") {
      const lines = g.coordinates || [];
      for (const line of lines) considerLineString(line || []);
    }
  }

  if (bestObjectId !== null && bestDist <= maxMeters) return { objectId: bestObjectId, dist: bestDist };
  return null;
}

const PipeGeoJsonLayer = memo(function PipeGeoJsonLayer({ geojson, showPipeGlow, perfMode }) {
  useEffect(() => {
    perfLog("overlay checkpoint: pipe layer rendered", {
      perfMode,
      features: Array.isArray(geojson?.features) ? geojson.features.length : 0
    });
  }, [geojson, perfMode]);

  if (!geojson) return null;

  return (
    <GeoJSON
      data={geojson}
      style={(feature) => ({
        color: feature?.properties?._sharedDownstream ? "#007bff" : "#ff00ff",
        weight: perfMode === "mobile" ? 2.5 : 4,
        opacity: perfMode === "mobile" ? 0.8 : 0.95,
        className: showPipeGlow ? "pipe-glow" : undefined
      })}
      onEachFeature={(feature, layer) => {
        const p = feature?.properties || {};
        const v = toNum(p._v_half_mps);
        const vTxt = v !== null ? `${v.toFixed(2)} m/s` : "—";
        layer.bindPopup(
          `<div style="font-family: sans-serif; font-size: 12px;">
            <div><b>OBJECTID:</b> ${p.OBJECTID ?? "—"}</div>
            <div><b>SEWER_NAME:</b> ${p.SEWER_NAME ?? "—"}</div>
            <div><b>Material:</b> ${p.MATERIAL ?? "—"} <span style="opacity:0.7">(n=${p._manning_n ?? "—"})</span></div>
            <div><b>Size (W/H mm):</b> ${p.PIPE_WIDTH ?? "—"} / ${p.PIPE_HEIGHT ?? "—"}</div>
            <div><b>Pipe length:</b> ${p.PIPE_LENGTH ?? "—"}</div>
            <div><b>Slope (GRADE):</b> ${p.GRADE ?? "—"}</div>
            <div><b>Up IL / Down IL:</b> ${p.UPSTREAM_IL ?? "—"} / ${p.DOWNSTREAM_IL ?? "—"}</div>
            <div><b>Velocity (half-full):</b> ${vTxt}</div>
          </div>`
        );
      }}
    />
  );
});

const StreetRoutesLayer = memo(function StreetRoutesLayer({ points, showStreetRoutes }) {
  if (!showStreetRoutes) return null;

  return points
    .filter((p) => p.street?.visible && Array.isArray(p.street.route) && p.street.route.length > 1)
    .map((p) => (
      <Polyline
        key={`street-${p.id}`}
        positions={p.street.route.map((pt) => [pt.lat, pt.lng])}
        pathOptions={{
          color: "#8b5a2b",
          weight: 4,
          opacity: 0.8
        }}
      >
        <Popup>
          <div>
            <div>
              <b>{p.name}</b> street route
            </div>
            <div>Distance: {Math.round(p.street.distM || 0)} m</div>
            <div>Speed: {p.street.speedMps?.toFixed(2)} m/s</div>
            <div>ETA: {Math.round(p.street.etaS || 0)} s</div>
            <div>
              Destination pipe OBJECTID:{" "}
              {p.contact?.pipeObjectId !== null && p.contact?.pipeObjectId !== undefined ? p.contact.pipeObjectId : "—"}
            </div>
          </div>
        </Popup>
      </Polyline>
    ));
});

const PipePlansLayer = memo(function PipePlansLayer({ points, showPipePlans, byObjectId }) {
  if (!showPipePlans) return null;

  return points
    .filter((p) => Array.isArray(p.pipePlan) && p.pipePlan.length > 1)
    .map((p) => (
      <Polyline
        key={`pipeplan-${p.id}`}
        positions={p.pipePlan.map((pt) => [pt.lat, pt.lng])}
        pathOptions={{
          color: "#00aa00",
          weight: 5,
          opacity: 0.85
        }}
      >
        <Popup>
          {(() => {
            const startId = p.contact?.pipeObjectId ?? null;
            const startFt = startId !== null && byObjectId ? byObjectId.get(startId) : null;
            const sp = startFt?.properties || {};
            const v = typeof sp._v_half_mps === "number" ? sp._v_half_mps : parseFloat(sp._v_half_mps);
            const vTxt = Number.isFinite(v) ? `${v.toFixed(2)} m/s` : "—";
            return (
              <div style={{ fontFamily: "sans-serif", fontSize: 12 }}>
                <div><b>OBJECTID:</b> {sp.OBJECTID ?? "—"}</div>
                <div><b>SEWER_NAME:</b> {sp.SEWER_NAME ?? "—"}</div>
                <div><b>Material:</b> {sp.MATERIAL ?? "—"} <span style={{ opacity: 0.7 }}>(n={sp._manning_n ?? "—"})</span></div>
                <div><b>Size (W/H mm):</b> {sp.PIPE_WIDTH ?? "—"} / {sp.PIPE_HEIGHT ?? "—"}</div>
                <div><b>Pipe length:</b> {sp.PIPE_LENGTH ?? "—"}</div>
                <div><b>Slope (GRADE):</b> {sp.GRADE ?? "—"}</div>
                <div><b>Up IL / Down IL:</b> {sp.UPSTREAM_IL ?? "—"} / {sp.DOWNSTREAM_IL ?? "—"}</div>
                <div><b>Velocity (half-full):</b> {vTxt}</div>
              </div>
            );
          })()}
        </Popup>
      </Polyline>
    ));
});

const EndpointsLayer = memo(function EndpointsLayer({ terminalNodes, showEndpoints }) {
  if (!showEndpoints || !Array.isArray(terminalNodes) || terminalNodes.length === 0) return null;
  return terminalNodes.map((n) => (
    <CircleMarker
      key={`endpoint-${n.key}`}
      center={[n.lat, n.lng]}
      radius={6}
      pathOptions={{ color: "#00bcd4", fillColor: "#00bcd4", fillOpacity: 0.85, weight: 2 }}
    >
      <Popup>
        <div>
          <div><b>Endpoint node</b></div>
          <div>Key: {n.key}</div>
          <div>Incoming: {n.inCount}</div>
          <div>Outgoing: {n.outCount}</div>
          <div>Incoming OBJECTIDs: {n.inObjectIds.slice(0, 10).join(", ") || "—"}</div>
        </div>
      </Popup>
    </CircleMarker>
  ));
});

const FallbackBridgeLayer = memo(function FallbackBridgeLayer({ points, showFallbackBridges }) {
  if (!showFallbackBridges) return null;
  return points
    .filter(
      (p) =>
        p.fallbackBridge &&
        ((Array.isArray(p.fallbackBridge.path) && p.fallbackBridge.path.length > 1) ||
          (p.fallbackBridge.from && p.fallbackBridge.to))
    )
    .map((p) => (
      <Polyline
        key={`fallback-bridge-${p.id}`}
        positions={
          Array.isArray(p.fallbackBridge.path) && p.fallbackBridge.path.length > 1
            ? p.fallbackBridge.path.map((pt) => [pt.lat, pt.lng])
            : [
                [p.fallbackBridge.from.lat, p.fallbackBridge.from.lng],
                [p.fallbackBridge.to.lat, p.fallbackBridge.to.lng]
              ]
        }
        pathOptions={{
          color: p.fallbackBridge.mode === "guarantee_endpoint" ? "#ff9800" : "#ff2d2d",
          weight: 4,
          opacity: 0.9,
          dashArray: "8,8"
        }}
      >
        <Popup>
          <div>
            <div><b>Fallback bridge</b></div>
            <div>Mode: {p.fallbackBridge.mode}</div>
            <div>Reason: {p.fallbackBridge.reason || p.fallbackReason || "—"}</div>
            <div>Distance: {Math.round(p.fallbackBridge.meters || 0)} m</div>
          </div>
        </Popup>
      </Polyline>
    ));
});

const MovingPointsLayer = memo(function MovingPointsLayer({ points, showLabels, isMobileViewport }) {
  return points.map((p) => (
    <Marker
      key={p.id}
      position={[p.lat, p.lng]}
      icon={POO_ICON}
    >
      <Popup>
        <div>
          <div>
            <b>{p.name}</b>
          </div>
          <div>Mode: {p.mode}</div>
          <div>Routing: {p.routingStatus || "—"}</div>
          <div>Fallback used: {p.fallbackUsed ? "yes" : "no"}</div>
          {p.fallbackUsed && <div>Fallback reason: {p.fallbackReason || "—"}</div>}
          {p.terminalNode && <div>Terminal node: {p.terminalNode.key}</div>}
          {p.mode === "pipe" && p.pipe?.speedMps !== undefined && (
            <div>Pipe speed: {p.pipe.speedMps.toFixed(2)} m/s</div>
          )}
          {p.error && <div>{p.error}</div>}
        </div>
      </Popup>

      {showLabels && (
        <Tooltip permanent={!isMobileViewport} direction="right" offset={[10, 0]} opacity={0.9}>
          <div className="pointLabel">
            <div className="pointLabelName">{p.name}</div>
            <div className="pointLabelMeta">Started {p.initiatedAtLabel || "—"}</div>
            <div className="pointLabelMeta">
              v {toDisplaySpeed(p.currentVelocityBaseMps)} m/s
            </div>
            <div className="pointLabelMeta">ETA {formatEta(p.etaToDestinationSec)}</div>
          </div>
        </Tooltip>
      )}
    </Marker>
  ));
});

function SettingsModal({
  isOpen,
  onClose,
  locationId,
  setLocationId,
  locationOptions,
  perfMode,
  setPerfMode,
  showLabels,
  setShowLabels,
  showPipeGlow,
  setShowPipeGlow,
  showEndpoints,
  setShowEndpoints,
  showFallbackBridges,
  setShowFallbackBridges,
  routingFallbackMode,
  setRoutingFallbackMode,
  showStreetRoutes,
  setShowStreetRoutes,
  showPipePlans,
  setShowPipePlans,
  speedMult,
  cycleSpeed,
  clickToFlush,
  setClickToFlush
}) {
  if (!isOpen) return null;

  return (
    <div className="settingsModalBackdrop" onClick={onClose}>
      <div className="settingsModal" onClick={(e) => e.stopPropagation()}>
        <div className="settingsModalHeader">
          <h3>Settings</h3>
          <button className="settingsCloseBtn" onClick={onClose} aria-label="Close settings">
            x
          </button>
        </div>

        <div className="settingsSection">
          <h4>Location</h4>
          <label className="settingsFieldLabel" htmlFor="network-location-select">
            Sewer network dataset
          </label>
          <select
            id="network-location-select"
            className="settingsSelect"
            value={locationId}
            onChange={(e) => setLocationId(e.target.value)}
          >
            {locationOptions.map((opt) => (
              <option key={opt.id} value={opt.id}>
                {opt.label}
              </option>
            ))}
          </select>
        </div>

        <div className="settingsSection">
          <h4>Routing</h4>
          <button
            onClick={() =>
              setRoutingFallbackMode((m) =>
                m === "strict" ? "nearest_downstream_node" : m === "nearest_downstream_node" ? "guarantee_endpoint" : "strict"
              )
            }
          >
            Routing fallback:{" "}
            {routingFallbackMode === "strict"
              ? "Strict"
              : routingFallbackMode === "nearest_downstream_node"
                ? "Nearest downstream node"
                : "Guarantee endpoint"}
          </button>
        </div>

        <div className="settingsSection">
          <h4>Overlay Visibility</h4>
          <button onClick={() => setShowStreetRoutes((v) => !v)}>
            {showStreetRoutes ? "Street routes: ON" : "Street routes: OFF"}
          </button>
          <button onClick={() => setShowPipePlans((v) => !v)}>
            {showPipePlans ? "Pipe plans: ON" : "Pipe plans: OFF"}
          </button>
          <button onClick={() => setShowEndpoints((v) => !v)}>
            {showEndpoints ? "Endpoints: ON" : "Endpoints: OFF"}
          </button>
          <button onClick={() => setShowFallbackBridges((v) => !v)}>
            {showFallbackBridges ? "Fallback bridges: ON" : "Fallback bridges: OFF"}
          </button>
          <button onClick={() => setShowLabels((v) => !v)}>
            {showLabels ? "Labels: ON" : "Labels: OFF"}
          </button>
        </div>

        <div className="settingsSection">
          <h4>Performance</h4>
          <button
            onClick={() =>
              setPerfMode((m) => {
                const next = m === "mobile" ? "desktop" : "mobile";
                setShowPipeGlow(next === "desktop");
                setShowLabels(next !== "mobile");
                return next;
              })
            }
          >
            {perfMode === "mobile" ? "Perf mode: Mobile" : "Perf mode: Desktop"}
          </button>
          <button onClick={() => setShowPipeGlow((v) => !v)}>
            {showPipeGlow ? "Pipe glow: ON" : "Pipe glow: OFF"}
          </button>
        </div>

        <div className="settingsSection">
          <h4>Simulation</h4>
          <button onClick={cycleSpeed}>
            Speed: {speedMult}x
          </button>
          <button onClick={() => setClickToFlush((v) => !v)}>
            {clickToFlush ? "Click-to-flush: ON" : "Click-to-flush: OFF"}
          </button>
        </div>
      </div>
    </div>
  );
}

export default function App() {
  const storedDatasetId =
    typeof window !== "undefined" ? window.localStorage.getItem("flush:pipeDatasetId") : null;
  const initialPipeDatasetId = PIPE_DATASETS.some((d) => d.id === storedDatasetId)
    ? storedDatasetId
    : DEFAULT_PIPE_DATASET_ID;
  const storedLoc =
    typeof window !== "undefined" ? window.localStorage.getItem("flush:lastDeviceLoc") : null;
  const parsedStoredLoc = (() => {
    if (!storedLoc) return null;
    try {
      const obj = JSON.parse(storedLoc);
      if (typeof obj?.lat === "number" && typeof obj?.lng === "number") return obj;
    } catch {
      return null;
    }
    return null;
  })();

  const [flushes, setFlushes] = useState(0);
  const [pipeDatasetId, setPipeDatasetId] = useState(initialPipeDatasetId);
  const selectedPipeDataset = useMemo(
    () => PIPE_DATASETS.find((d) => d.id === pipeDatasetId) || PIPE_DATASETS[0],
    [pipeDatasetId]
  );

  const [clickToFlush, setClickToFlush] = useState(false);
  const flushCounterRef = useRef(0);

  const [pipeData, setPipeData] = useState({
    datasetId: null,
    ready: false,
    geojson: null,
    bbox: null,
    count: 0,
    nodeCount: 0,
    byObjectId: null,
    segmentIndex: null,
    nodeIndex: null,
    terminalNodes: [],
    trueTerminalNodes: [],
    downstreamNodes: [],
    nodeSpatialIndex: null,
    undirectedNodeAdj: null,
    reachableEntryNodeKeys: null,
    pipeCanReachTerminal: null,
    nextHopToTerminal: null,
    pipeDistToTerminalM: null,
    terminalPipeSet: null
  });

  // Device start location (from browser geolocation)
  const [deviceLoc, setDeviceLoc] = useState({
    ready: !!parsedStoredLoc,
    lat: parsedStoredLoc?.lat ?? FALLBACK_CENTER.lat,
    lng: parsedStoredLoc?.lng ?? FALLBACK_CENTER.lng
  });

  const [showStreetRoutes, setShowStreetRoutes] = useState(true);
  const [showPipePlans, setShowPipePlans] = useState(true);
  const [speedMult, setSpeedMult] = useState(1);
  const cycleSpeed = useCallback(() => setSpeedMult((v) => v === 1 ? 10 : v === 10 ? 100 : 1), []);
  const [perfMode, setPerfMode] = useState(PERF_MODE_DEFAULT);
  const isMobileViewport = useMemo(
    () => (typeof window !== "undefined" ? window.matchMedia("(max-width: 900px)").matches : false),
    []
  );
  const [showLabels, setShowLabels] = useState(!isMobileViewport);
  const [showPipeGlow, setShowPipeGlow] = useState(SHOW_PIPE_GLOW_DEFAULT);
  const [showEndpoints, setShowEndpoints] = useState(true);
  const [showFallbackBridges, setShowFallbackBridges] = useState(true);
  const [routingFallbackMode, setRoutingFallbackMode] = useState(ROUTING_FALLBACK_DEFAULT);
  const [isSettingsOpen, setIsSettingsOpen] = useState(false);
  const [pendingCreates, setPendingCreates] = useState([]);

  // People points
  // mode: "street" | "pipe" | "arrived" | "error"
  const [renderPoints, setRenderPoints] = useState([]);
  const pointsRef = useRef([]);
  const restoredOnceRef = useRef(false);
  const lastSyncedStatusRef = useRef(new Map());
  const lastServerUpdateRef = useRef(new Map());
  const reconcileInFlightRef = useRef(false);
  const lastSseReconcileMsRef = useRef(0);
  const initialViewportSetRef = useRef(false);
  const [mapReady, setMapReady] = useState(false);

  // Keep map instance so we can recenter once geolocation arrives
  const mapRef = useRef(null);

  const mutatePoints = useCallback((updater, sync = true) => {
    const next = updater(pointsRef.current);
    pointsRef.current = next;
    if (sync) setRenderPoints(next);
    return next;
  }, []);

  const clearAll = useCallback(() => {
    const active = pointsRef.current.filter((p) => p.id && p.mode !== "arrived" && p.mode !== "error");
    active.forEach((p) => {
      apiFetch(`/api/flushes/${encodeURIComponent(p.id)}/status`, {
        method: "PATCH",
        body: JSON.stringify({ status: "error", errorMessage: "cleared_by_user" })
      }).catch(() => {});
    });
    pointsRef.current = [];
    setRenderPoints([]);
    setPendingCreates([]);
    setFlushes(0);
    flushCounterRef.current = 0;
  }, []);

  useEffect(() => {
    try {
      window.localStorage.setItem("flush:pipeDatasetId", pipeDatasetId);
    } catch {
      // ignore storage errors
    }
  }, [pipeDatasetId]);

  useEffect(() => {
    mutatePoints(() => []);
    if (mapRef.current) {
      mapRef.current.setView([selectedPipeDataset.center.lat, selectedPipeDataset.center.lng], 7);
    }
    initialViewportSetRef.current = false;
  }, [selectedPipeDataset.id, selectedPipeDataset.center.lat, selectedPipeDataset.center.lng, mutatePoints]);

  useEffect(() => {
    if (!isSettingsOpen) return;
    const onKeyDown = (e) => {
      if (e.key === "Escape") setIsSettingsOpen(false);
    };
    window.addEventListener("keydown", onKeyDown);
    return () => window.removeEventListener("keydown", onKeyDown);
  }, [isSettingsOpen]);

  // 1) Load pipes GeoJSON from /public + compute velocities + direction + connectivity
  useEffect(() => {
    let cancelled = false;

    async function load() {
      try {
        const startedAt = performance.now();
        perfLog("load start", { path: selectedPipeDataset.path, location: selectedPipeDataset.id });
        setPipeData((prev) => ({
          ...prev,
          datasetId: selectedPipeDataset.id,
          ready: false
        }));
        const res = await fetch(selectedPipeDataset.path);
        if (!res.ok) throw new Error(`GeoJSON fetch failed: ${res.status}`);
        const gj = await res.json();

        const features = Array.isArray(gj.features) ? gj.features : [];

        let minLat = Infinity;
        let minLng = Infinity;
        let maxLat = -Infinity;
        let maxLng = -Infinity;

        function scanCoords(coords) {
          // coords = [lng, lat]
          const lng = coords?.[0];
          const lat = coords?.[1];
          if (typeof lat !== "number" || typeof lng !== "number") return;
          if (lat < minLat) minLat = lat;
          if (lat > maxLat) maxLat = lat;
          if (lng < minLng) minLng = lng;
          if (lng > maxLng) maxLng = lng;
        }

        const nodeIndex = new Map();
        const byObjectId = new Map();

        function ensureNode(key, lng, lat) {
          if (!nodeIndex.has(key)) {
            nodeIndex.set(key, { key, lng, lat, inObjectIds: [], outObjectIds: [] });
          }
          return nodeIndex.get(key);
        }

        // Pass 1: compute bbox + per-pipe velocity + DIR + endpoint node keys (DIR-first)
        for (const ft of features) {
          const g = ft?.geometry;
          if (!g) continue;

          if (g.type === "LineString") {
            for (const c of g.coordinates) scanCoords(c);
          } else if (g.type === "MultiLineString") {
            for (const line of g.coordinates) {
              for (const c of line) scanCoords(c);
            }
          }

          const props = ft.properties || {};
          const objectId = toNum(props.OBJECTID);

          // Geometry endpoints in file order
          let geomStart = null;
          let geomEnd = null;

          if (g.type === "LineString") {
            const coords = g.coordinates || [];
            if (coords.length >= 2) {
              geomStart = coords[0];
              geomEnd = coords[coords.length - 1];
            }
          } else if (g.type === "MultiLineString") {
            const lines = g.coordinates || [];
            if (lines.length > 0) {
              const first = lines[0] || [];
              const last = lines[lines.length - 1] || [];
              if (first.length >= 1 && last.length >= 1) {
                geomStart = first[0];
                geomEnd = last[last.length - 1];
              }
            }
          }

          // Compute Manning velocity (half-full assumption)
          const hv = computeHalfFullVelocityMps(props);
          props._manning_n = hv.n;
          props._slope_S = hv.S;
          props._v_half_mps = hv.v;

          // Direction: DIR is authoritative if present. If DIR is missing in the source data,
          // we assume geometry is already stored in upstream->downstream order (u_to_d).
          const dirFromData = parseDirFromProps(props);

          let dir = "u_to_d";
          let dirSource = "default";
          if (dirFromData) {
            dir = dirFromData;
            dirSource = "DIR";
          }

          props._dir = dir;
          props._dir_source = dirSource;

          const sewerNameNorm = normaliseSewerName(props.SEWER_NAME || props.SEWERNAME);
          props._sewer_name_norm = sewerNameNorm;

          if (objectId !== null && geomStart && geomEnd) {
            const a = { lng: geomStart[0], lat: geomStart[1] };
            const b = { lng: geomEnd[0], lat: geomEnd[1] };

            // Flow endpoints derived strictly from DIR:
            // u_to_d: flowStart = geomStart, flowEnd = geomEnd
            // d_to_u: flowStart = geomEnd,   flowEnd = geomStart
            const flowStart = dir === "u_to_d" ? a : b;
            const flowEnd = dir === "u_to_d" ? b : a;

            const upKey = nodeKeyFromLngLat(flowStart.lng, flowStart.lat, NODE_SNAP_TOL_M);
            const downKey = nodeKeyFromLngLat(flowEnd.lng, flowEnd.lat, NODE_SNAP_TOL_M);

            props._upNodeKey = upKey;
            props._downNodeKey = downKey;

            const upNode = ensureNode(upKey, flowStart.lng, flowStart.lat);
            const downNode = ensureNode(downKey, flowEnd.lng, flowEnd.lat);

            upNode.outObjectIds.push(objectId);
            downNode.inObjectIds.push(objectId);

            byObjectId.set(objectId, ft);
          }

          ft.properties = props;
        }

        // Pass 2: directed next connections strictly by node-match (no distance fallback).
        for (const ft of features) {
          const props = ft?.properties || {};
          const objectId = toNum(props.OBJECTID);
          const downKey = props._downNodeKey;

          if (objectId === null || !downKey) continue;

          const downNode = nodeIndex.get(downKey);

          const next = Array.isArray(downNode?.outObjectIds)
            ? downNode.outObjectIds.filter((id) => id !== objectId)
            : [];

          props._nextObjectIds = next;

          ft.properties = props;
        }

        const allPipeIds = Array.from(byObjectId.keys());
        const nextByPipe = new Map();
        const reverseByPipe = new Map();
        const undirectedNodeAdj = new Map();
        const pushAdj = (fromKey, edge) => {
          const arr = undirectedNodeAdj.get(fromKey);
          if (arr) arr.push(edge);
          else undirectedNodeAdj.set(fromKey, [edge]);
        };
        for (const id of allPipeIds) reverseByPipe.set(id, []);
        for (const id of allPipeIds) {
          const ft = byObjectId.get(id);
          const next = Array.isArray(ft?.properties?._nextObjectIds) ? ft.properties._nextObjectIds.slice() : [];
          nextByPipe.set(id, next);
          for (const n of next) {
            if (!reverseByPipe.has(n)) reverseByPipe.set(n, []);
            reverseByPipe.get(n).push(id);
          }

          const p = ft?.properties || {};
          const upKey = p._upNodeKey;
          const downKey = p._downNodeKey;
          const ord = orderedCoordsForPipe(ft);
          const meters = routeDistanceMeters(ord);
          if (upKey && downKey && ord.length > 1) {
            const rev = ord.slice().reverse();
            pushAdj(upKey, { toKey: downKey, objectId: id, meters, coords: ord });
            pushAdj(downKey, { toKey: upKey, objectId: id, meters, coords: rev });
          }
        }


        const terminalNodes = [];
        const downstreamNodes = [];
        for (const node of nodeIndex.values()) {
          const outCount = Array.isArray(node.outObjectIds) ? node.outObjectIds.length : 0;
          const inCount = Array.isArray(node.inObjectIds) ? node.inObjectIds.length : 0;
          const row = {
            key: node.key,
            lat: node.lat,
            lng: node.lng,
            inCount,
            outCount,
            inObjectIds: (node.inObjectIds || []).slice(),
            outObjectIds: (node.outObjectIds || []).slice()
          };
          if (outCount > 0) downstreamNodes.push(row);
          if (outCount === 0 && inCount > 0) terminalNodes.push(row);
        }
        const terminalNodeKeys = new Set(terminalNodes.map((n) => n.key));
        const terminalPipeSet = new Set();
        for (const [id, ft] of byObjectId.entries()) {
          const downKey = ft?.properties?._downNodeKey;
          if (downKey && terminalNodeKeys.has(downKey)) terminalPipeSet.add(id);
        }

        // Reduce sink endpoints to the 3 primary processing destinations by trunk-level reach.
        const terminalReachByPipe = new Map();
        for (const tid of terminalPipeSet) {
          const seen = new Set([tid]);
          const q = [tid];
          while (q.length > 0) {
            const curr = q.shift();
            const parents = reverseByPipe.get(curr) || [];
            for (const p of parents) {
              if (seen.has(p)) continue;
              seen.add(p);
              q.push(p);
            }
          }
          terminalReachByPipe.set(tid, seen.size);
        }

        const trunkBest = new Map();
        for (const tid of terminalPipeSet) {
          const ft = byObjectId.get(tid);
          const props = ft?.properties || {};
          const downKey = props._downNodeKey;
          if (!downKey) continue;
          const trunk = normaliseSewerName(props.SEWER_NAME || props.SEWERNAME || "UNKNOWN");
          const reach = terminalReachByPipe.get(tid) || 0;
          const prev = trunkBest.get(trunk);
          if (!prev || reach > prev.reach) trunkBest.set(trunk, { trunk, tid, downKey, reach });
        }
        const selected = [];
        for (const name of TRUE_ENDPOINT_NAME_PRIORITY) {
          const hit = trunkBest.get(name);
          if (hit) selected.push(hit);
        }
        if (selected.length < 3) {
          const used = new Set(selected.map((x) => x.trunk));
          const extras = Array.from(trunkBest.values())
            .filter((x) => !used.has(x.trunk))
            .sort((a, b) => b.reach - a.reach)
            .slice(0, 3 - selected.length);
          selected.push(...extras);
        }
        const trueTerminalNodeKeys = new Set(selected.slice(0, 3).map((x) => x.downKey));
        const trueTerminalNodes = terminalNodes.filter((n) => trueTerminalNodeKeys.has(n.key));
        const trueTerminalPipeSet = new Set();
        for (const [id, ft] of byObjectId.entries()) {
          const downKey = ft?.properties?._downNodeKey;
          if (downKey && trueTerminalNodeKeys.has(downKey)) trueTerminalPipeSet.add(id);
        }

        const pipeCanReachTerminal = new Set(trueTerminalPipeSet);
        const queue = Array.from(trueTerminalPipeSet);
        const distToTerminal = new Map();
        for (const id of trueTerminalPipeSet) distToTerminal.set(id, 0);
        while (queue.length > 0) {
          const curr = queue.shift();
          const parents = reverseByPipe.get(curr) || [];
          for (const p of parents) {
            if (pipeCanReachTerminal.has(p)) continue;
            pipeCanReachTerminal.add(p);
            distToTerminal.set(p, (distToTerminal.get(curr) || 0) + 1);
            queue.push(p);
          }
        }

        const nextHopToTerminal = new Map();
        for (const id of allPipeIds) {
          const next = nextByPipe.get(id) || [];
          const reachableNext = next.filter((n) => pipeCanReachTerminal.has(n));
          if (reachableNext.length === 0) {
            nextHopToTerminal.set(id, null);
            continue;
          }
          let best = reachableNext[0];
          let bestDist = distToTerminal.get(best) ?? Number.MAX_SAFE_INTEGER;
          for (let i = 1; i < reachableNext.length; i++) {
            const cand = reachableNext[i];
            const d = distToTerminal.get(cand) ?? Number.MAX_SAFE_INTEGER;
            if (d < bestDist) {
              bestDist = d;
              best = cand;
            }
          }
          nextHopToTerminal.set(id, best);
        }

        const pipeLengthById = new Map();
        for (const id of allPipeIds) {
          const ft = byObjectId.get(id);
          pipeLengthById.set(id, routeDistanceMeters(orderedCoordsForPipe(ft)));
        }
        const pipeDistToTerminalM = new Map();
        const dfsDist = (id, stack = new Set()) => {
          if (pipeDistToTerminalM.has(id)) return pipeDistToTerminalM.get(id);
          if (!pipeCanReachTerminal.has(id)) return Infinity;
          if (stack.has(id)) return Infinity;
          stack.add(id);
          const own = pipeLengthById.get(id) || 0;
          const nxt = nextHopToTerminal.get(id);
          let total = own;
          if (nxt !== null && nxt !== undefined) {
            const dNext = dfsDist(nxt, stack);
            total = Number.isFinite(dNext) ? own + dNext : own;
          }
          stack.delete(id);
          pipeDistToTerminalM.set(id, total);
          return total;
        };
        for (const id of allPipeIds) dfsDist(id);

        const reachableEntryNodeKeys = new Set();
        for (const [key, n] of nodeIndex.entries()) {
          const out = Array.isArray(n.outObjectIds) ? n.outObjectIds : [];
          if (out.some((oid) => pipeCanReachTerminal.has(oid))) reachableEntryNodeKeys.add(key);
        }

        const bbox =
          isFinite(minLat) && isFinite(minLng) && isFinite(maxLat) && isFinite(maxLng)
            ? { minLat, minLng, maxLat, maxLng }
            : null;
        const segmentIndex = buildSegmentSpatialIndex(features);
        const nodeSpatialIndex = buildNodeSpatialIndex(downstreamNodes);
        perfLog("load done", {
          path: selectedPipeDataset.path,
          location: selectedPipeDataset.id,
          features: features.length,
          cells: segmentIndex.cells.size,
          terminalNodes: terminalNodes.length,
          trueTerminalNodes: trueTerminalNodes.length,
          trueTerminals: selected.slice(0, 3).map((x) => ({ name: x.trunk, reach: x.reach })),
          reachablePipes: pipeCanReachTerminal.size,
          avgToTerminalM:
            pipeCanReachTerminal.size > 0
              ? Math.round(
                  Array.from(pipeCanReachTerminal).reduce((acc, id) => acc + (pipeDistToTerminalM.get(id) || 0), 0) /
                    pipeCanReachTerminal.size
                )
              : 0,
          ms: Math.round(performance.now() - startedAt)
        });

        if (cancelled) return;

        setPipeData({
          datasetId: selectedPipeDataset.id,
          ready: true,
          geojson: gj,
          bbox,
          count: features.length,
          nodeCount: nodeIndex.size,
          byObjectId,
          segmentIndex,
          nodeIndex,
          terminalNodes,
          trueTerminalNodes,
          downstreamNodes,
          nodeSpatialIndex,
          undirectedNodeAdj,
          reachableEntryNodeKeys,
          pipeCanReachTerminal,
          nextHopToTerminal,
          pipeDistToTerminalM,
          terminalPipeSet: trueTerminalPipeSet
        });
      } catch (e) {
        if (cancelled) return;
        console.error(e);
        setPipeData({
          datasetId: selectedPipeDataset.id,
          ready: false,
          geojson: null,
          bbox: null,
          count: 0,
          nodeCount: 0,
          byObjectId: null,
          segmentIndex: null,
          nodeIndex: null,
          terminalNodes: [],
          trueTerminalNodes: [],
          downstreamNodes: [],
          nodeSpatialIndex: null,
          undirectedNodeAdj: null,
          reachableEntryNodeKeys: null,
          pipeCanReachTerminal: null,
          nextHopToTerminal: null,
          pipeDistToTerminalM: null,
          terminalPipeSet: null
        });
      }
    }

    load();
    return () => {
      cancelled = true;
    };
  }, [selectedPipeDataset.id, selectedPipeDataset.path]);

  useEffect(() => {
    if (!mapReady || !mapRef.current) return;
    if (!pipeData.ready || !pipeData.bbox) return;
    if (pipeData.datasetId !== selectedPipeDataset.id) return;

    const { minLat, minLng, maxLat, maxLng } = pipeData.bbox;
    mapRef.current.fitBounds(
      [
        [minLat, minLng],
        [maxLat, maxLng]
      ],
      { padding: [30, 30], maxZoom: 13 }
    );
    initialViewportSetRef.current = true;
  }, [mapReady, pipeData.ready, pipeData.bbox, pipeData.datasetId, selectedPipeDataset.id]);

  // 2) Ask browser for device location; use it as spawn point
  useEffect(() => {
    if (!("geolocation" in navigator)) return;

    navigator.geolocation.getCurrentPosition(
      (pos) => {
        const lat = pos.coords.latitude;
        const lng = pos.coords.longitude;

        setDeviceLoc({
          ready: true,
          lat,
          lng
        });
        try {
          window.localStorage.setItem("flush:lastDeviceLoc", JSON.stringify({ lat, lng }));
        } catch {
          // ignore storage errors
        }

        if (mapRef.current && !initialViewportSetRef.current) {
          mapRef.current.setView([lat, lng], 14);
          initialViewportSetRef.current = true;
        }
      },
      () => {
        // Keep fallback centre
      },
      {
        enableHighAccuracy: true,
        timeout: 8000,
        maximumAge: 0
      }
    );
  }, []);

  useEffect(() => {
    if (initialViewportSetRef.current) return;
    if (!mapReady || !mapRef.current) return;

    const coords = [];
    for (const p of renderPoints) {
      if (typeof p.lat === "number" && typeof p.lng === "number") coords.push({ lat: p.lat, lng: p.lng });
      if (Array.isArray(p.street?.route)) coords.push(...p.street.route);
      if (Array.isArray(p.pipePlan)) coords.push(...p.pipePlan);
      if (Array.isArray(p.fallbackBridge?.path)) coords.push(...p.fallbackBridge.path);
    }

    const map = mapRef.current;
    if (coords.length >= 2) {
      let minLat = Infinity;
      let minLng = Infinity;
      let maxLat = -Infinity;
      let maxLng = -Infinity;
      for (const c of coords) {
        if (typeof c.lat !== "number" || typeof c.lng !== "number") continue;
        if (c.lat < minLat) minLat = c.lat;
        if (c.lat > maxLat) maxLat = c.lat;
        if (c.lng < minLng) minLng = c.lng;
        if (c.lng > maxLng) maxLng = c.lng;
      }
      if (isFinite(minLat) && isFinite(minLng) && isFinite(maxLat) && isFinite(maxLng)) {
        map.fitBounds(
          [
            [minLat, minLng],
            [maxLat, maxLng]
          ],
          { padding: [30, 30], maxZoom: 14 }
        );
        initialViewportSetRef.current = true;
        return;
      }
    }

    if (coords.length === 1) {
      map.setView([coords[0].lat, coords[0].lng], 14);
      initialViewportSetRef.current = true;
      return;
    }

    if (deviceLoc.ready) {
      map.setView([deviceLoc.lat, deviceLoc.lng], 14);
      initialViewportSetRef.current = true;
    }
  }, [mapReady, renderPoints, deviceLoc.ready, deviceLoc.lat, deviceLoc.lng]);

  const buildPointFromPersistedRun = useCallback((run, nowMs) => {
    const startedAtMs = Date.parse(run.started_at || run.startedAt || run.created_at || new Date().toISOString());
    const elapsedSec = Math.max(0, (nowMs - startedAtMs) / 1000);
    const streetRoute = Array.isArray(run.street_route) ? run.street_route : [];
    const pipePlan = Array.isArray(run.pipe_plan) ? run.pipe_plan : [];
    const streetSpeed = Number(run.street_speed_mps || STREET_SPEED_MPS);
    const pipeSpeed = Number(run.pipe_base_speed_mps || PIPE_SPEED_MIN_MPS);
    const streetTotal = Number.isFinite(run.street_total_m) ? run.street_total_m : routeDistanceMeters(streetRoute);
    const pipeTotal = Number.isFinite(run.pipe_total_m) ? run.pipe_total_m : routeDistanceMeters(pipePlan);
    const streetEta = streetSpeed > 0 ? streetTotal / streetSpeed : 0;
    const pipeEta = pipeSpeed > 0 ? pipeTotal / pipeSpeed : 0;
    const routingStatus = run.routing_status || "incomplete";
    const startedLabel = new Date(startedAtMs).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit", second: "2-digit" });
    const base = {
      id: run.id,
      name: run.user_name || "User",
      street: null,
      contact: run.contact || null,
      pipe: null,
      pipePlan,
      error: run.error_message || null,
      routingStatus,
      fallbackUsed: !!run.fallback_bridge,
      fallbackReason: run.fallback_reason || "none",
      fallbackBridge: run.fallback_bridge || null,
      terminalNode: run.terminal_node || null,
      currentVelocityBaseMps: null,
      currentVelocitySimMps: null,
      etaToDestinationSec: null,
      persistedStatus: run.status || "active",
      serverUpdatedAtMs: Date.parse(run.updated_at || run.started_at || new Date().toISOString()),
      initiatedAtIso: run.started_at || null,
      initiatedAtLabel: startedLabel
    };

    if (run.status === "error") {
      return { ...base, mode: "error", lat: run.current_lat ?? run.origin_lat, lng: run.current_lng ?? run.origin_lng };
    }

    const totalEta = streetEta + pipeEta;
    if (elapsedSec >= totalEta) {
      const endPt = pipePlan[pipePlan.length - 1] || streetRoute[streetRoute.length - 1] || { lat: run.origin_lat, lng: run.origin_lng };
      return {
        ...base,
        mode: "arrived",
        lat: endPt.lat,
        lng: endPt.lng,
        currentVelocityBaseMps: 0,
        currentVelocitySimMps: 0,
        etaToDestinationSec: 0,
        persistedStatus: "arrived",
        serverUpdatedAtMs: Date.parse(run.updated_at || new Date().toISOString())
      };
    }

    if (elapsedSec < streetEta && streetRoute.length > 1) {
      const traveled = elapsedSec * streetSpeed;
      const at = locateAlongPath(streetRoute, traveled);
      const streetRemaining = Math.max(0, streetTotal - traveled);
      return {
        ...base,
        mode: "street",
        lat: at.point?.lat ?? run.origin_lat,
        lng: at.point?.lng ?? run.origin_lng,
        street: {
          route: streetRoute,
          idx: at.nextIdx,
          speedMps: streetSpeed,
          distM: streetTotal,
          etaS: streetEta,
          visible: true
        },
        currentVelocityBaseMps: streetSpeed,
        currentVelocitySimMps: streetSpeed,
        etaToDestinationSec: streetRemaining / streetSpeed + pipeEta,
        serverUpdatedAtMs: Date.parse(run.updated_at || new Date().toISOString())
      };
    }

    const pipeElapsed = Math.max(0, elapsedSec - streetEta);
    const pipeTraveled = pipeElapsed * pipeSpeed;
    const at = locateAlongPath(pipePlan, pipeTraveled);
    const pipeRemaining = Math.max(0, pipeTotal - pipeTraveled);
    return {
      ...base,
      mode: "pipe",
      lat: at.point?.lat ?? run.origin_lat,
      lng: at.point?.lng ?? run.origin_lng,
      street: streetRoute.length > 1 ? { route: streetRoute, idx: streetRoute.length, speedMps: streetSpeed, distM: streetTotal, etaS: streetEta, visible: false } : null,
      pipe: { objectId: run.contact?.pipeObjectId ?? null, idx: at.nextIdx, speedMps: pipeSpeed, segmentVelocityMps: pipeSpeed },
      currentVelocityBaseMps: pipeSpeed,
      currentVelocitySimMps: pipeSpeed,
      etaToDestinationSec: pipeSpeed > 0 ? pipeRemaining / pipeSpeed : null,
      serverUpdatedAtMs: Date.parse(run.updated_at || new Date().toISOString())
    };
  }, []);

  const buildPipeRouteResult = useCallback((objectId, contactPoint) => {
    if (!pipeData.byObjectId || !pipeData.nodeIndex || objectId === null || !contactPoint) {
      return {
        coords: [],
        routingStatus: "incomplete",
        fallbackUsed: false,
        fallbackReason: "missing_feature",
        fallbackBridge: null,
        terminalNode: null
      };
    }

    const strict = buildPipePlanFromObjectId(
      objectId,
      contactPoint,
      pipeData.byObjectId,
      pipeData.nodeIndex,
      2000,
      null,
      pipeData.pipeCanReachTerminal,
      routingFallbackMode === "guarantee_endpoint" ? pipeData.nextHopToTerminal : null
    );

    if (strict.endReason === "terminal") {
      return {
        coords: strict.coords,
        routingStatus: "strict_arrived",
        fallbackUsed: false,
        fallbackReason: "none",
        fallbackBridge: null,
        terminalNode: strict.terminalNode
      };
    }

    const toFallbackReason = (endReason) => {
      if (endReason === "loop") return "loop_detected";
      if (endReason === "max_hops") return "max_hops_reached";
      if (endReason === "unreachable_subgraph") return "unreachable_subgraph";
      return "no_next_edge";
    };

    if (routingFallbackMode === "strict") {
      return {
        coords: strict.coords,
        routingStatus: "incomplete",
        fallbackUsed: false,
        fallbackReason: toFallbackReason(strict.endReason),
        fallbackBridge: null,
        terminalNode: null
      };
    }

    const bridgeFrom = strict.lastPoint || contactPoint;
    const connector =
      routingFallbackMode === "guarantee_endpoint"
        ? findBestPurpleConnectorPath({
            fromPoint: bridgeFrom,
            fromNodeKey: strict.lastNodeKey,
            nodeAdj: pipeData.undirectedNodeAdj,
            reachableEntryNodeKeys: pipeData.reachableEntryNodeKeys,
            nodeIndex: pipeData.nodeIndex,
            pipeCanReachTerminal: pipeData.pipeCanReachTerminal,
            pipeDistToTerminalM: pipeData.pipeDistToTerminalM
          })
        : null;

    let resumeStartId = null;
    let entryPoint = bridgeFrom;

    if (routingFallbackMode === "guarantee_endpoint") {
      if (!connector || !connector.resumeStartPipeId) {
        return {
          coords: strict.coords,
          routingStatus: "incomplete",
          fallbackUsed: false,
          fallbackReason: "no_connector_path",
          fallbackBridge: null,
          terminalNode: null
        };
      }
      resumeStartId = connector.resumeStartPipeId;
      entryPoint = connector.entryPoint || bridgeFrom;
    } else {
      const nearest = findNearestDownstreamNode(
        bridgeFrom,
        pipeData.nodeSpatialIndex,
        FALLBACK_MAX_BRIDGE_M,
        new Set(strict.lastNodeKey ? [strict.lastNodeKey] : [])
      );
      if (!nearest || !nearest.node || !Array.isArray(nearest.node.outObjectIds) || nearest.node.outObjectIds.length === 0) {
        return {
          coords: strict.coords,
          routingStatus: "incomplete",
          fallbackUsed: false,
          fallbackReason: toFallbackReason(strict.endReason),
          fallbackBridge: null,
          terminalNode: null
        };
      }
      const lastFt = strict.lastObjectId !== null && strict.lastObjectId !== undefined ? pipeData.byObjectId.get(strict.lastObjectId) : null;
      const outIdsRaw = nearest.node.outObjectIds.slice();
      const outIds = outIdsRaw;
      if (outIds.length === 0) {
        return {
          coords: strict.coords,
          routingStatus: "incomplete",
          fallbackUsed: false,
          fallbackReason: "unreachable_subgraph",
          fallbackBridge: null,
          terminalNode: null
        };
      }
      resumeStartId =
        outIds.length === 1
          ? outIds[0]
          : chooseNextPipeLowestDownIL(outIds, pipeData.byObjectId, lastFt?.properties || {});
      entryPoint = { lat: nearest.node.lat, lng: nearest.node.lng };
    }

    if (resumeStartId === null || resumeStartId === undefined) {
      return {
        coords: strict.coords,
        routingStatus: "incomplete",
        fallbackUsed: false,
        fallbackReason: "no_next_edge",
        fallbackBridge: null,
        terminalNode: null
      };
    }

    const resumeFt = pipeData.byObjectId.get(resumeStartId);
    const resumeOrd = orderedCoordsForPipe(resumeFt);
    const bridgeContact = nearestPointOnOrderedPipe(resumeOrd, entryPoint);
    const resumeStartPoint = bridgeContact?.point || entryPoint;
    const resumed = buildPipePlanFromObjectId(
      resumeStartId,
      resumeStartPoint,
      pipeData.byObjectId,
      pipeData.nodeIndex,
      2000,
      strict.visitedObjectIds,
      routingFallbackMode === "guarantee_endpoint" ? pipeData.pipeCanReachTerminal : null,
      routingFallbackMode === "guarantee_endpoint" ? pipeData.nextHopToTerminal : null
    );

    const merged = strict.coords.slice();
    const bridgePath = [bridgeFrom];
    if (routingFallbackMode === "guarantee_endpoint" && Array.isArray(connector?.connectorPathCoords)) {
      for (const pt of connector.connectorPathCoords) {
        const last = bridgePath[bridgePath.length - 1];
        if (last && metersBetween(last, pt) < 0.2) continue;
        bridgePath.push(pt);
      }
    } else {
      const last = bridgePath[bridgePath.length - 1];
      if (!last || metersBetween(last, entryPoint) > 0.2) bridgePath.push(entryPoint);
    }
    {
      const last = bridgePath[bridgePath.length - 1];
      if (!last || metersBetween(last, resumeStartPoint) > 0.2) bridgePath.push(resumeStartPoint);
    }
    for (const pt of bridgePath) {
      const last = merged[merged.length - 1];
      if (last && metersBetween(last, pt) < 0.2) continue;
      merged.push(pt);
    }
    if (Array.isArray(resumed.coords) && resumed.coords.length > 0) {
      for (let i = 1; i < resumed.coords.length; i++) merged.push(resumed.coords[i]);
    }

    const bridge = {
      from: bridgeFrom,
      to: resumeStartPoint,
      meters: routeDistanceMeters(bridgePath),
      mode: routingFallbackMode,
      reason: toFallbackReason(strict.endReason),
      path: bridgePath
    };

    return {
      coords: merged,
      routingStatus:
        resumed.endReason === "terminal"
          ? routingFallbackMode === "guarantee_endpoint"
            ? "guaranteed_arrived"
            : "fallback_arrived"
          : "incomplete",
      fallbackUsed: true,
      fallbackReason: resumed.endReason === "terminal" ? "none" : toFallbackReason(resumed.endReason),
      fallbackBridge: bridge,
      terminalNode: resumed.terminalNode || null
    };
  }, [
    pipeData.byObjectId,
    pipeData.nodeIndex,
    pipeData.nodeSpatialIndex,
    pipeData.undirectedNodeAdj,
    pipeData.reachableEntryNodeKeys,
    pipeData.pipeCanReachTerminal,
    pipeData.nextHopToTerminal,
    pipeData.pipeDistToTerminalM,
    routingFallbackMode
  ]);

  async function createPersistedFlushFromOrigin({ startLL, name, startedAtIso, requestedId }) {
    if (!pipeData.geojson) throw new Error("Pipe network not ready");
    const t0 = performance.now();
    const features = Array.isArray(pipeData.geojson?.features) ? pipeData.geojson.features : [];
    const contact =
      findNearestPipeContactWithIndex(features, pipeData.segmentIndex, startLL) ||
      findNearestPipeContact(pipeData.geojson, startLL);
    if (!contact || !contact.point) throw new Error("No pipes found");

    const props = contact.feature?.properties || {};
    const objectId = toNum(props.OBJECTID);
    const contactPipeV = Math.max(PIPE_SPEED_MIN_MPS, toNum(props._v_half_mps) || PIPE_SPEED_MIN_MPS);
    const route = await fetchOsrmRoute(startLL, contact.point);
    const pipeRoute = objectId !== null ? buildPipeRouteResult(objectId, contact.point) : null;
    const persisted = await apiFetch("/api/flushes", {
      method: "POST",
      body: JSON.stringify({
        id: requestedId || undefined,
        userName: name,
        origin: startLL,
        startedAt: startedAtIso || new Date().toISOString(),
        streetRoute: route,
        streetSpeedMps: STREET_SPEED_MPS,
        pipePlan: pipeRoute?.coords || [],
        pipeBaseSpeedMps: contactPipeV,
        routingStatus: pipeRoute?.routingStatus || "incomplete",
        fallbackReason: pipeRoute?.fallbackReason || "none",
        fallbackBridge: pipeRoute?.fallbackBridge || null,
        terminalNode: pipeRoute?.terminalNode || null,
        contact: { point: contact.point, pipeObjectId: objectId, pipeVelocityMps: contactPipeV }
      })
    });
    const point = buildPointFromPersistedRun(persisted, Date.now());
    if (!point) throw new Error("Unable to rehydrate persisted flush");
    perfLog("flush route ready", {
      pointId: point.id,
      ms: Math.round(performance.now() - t0),
      routeMeters: Math.round(routeDistanceMeters(route))
    });
    return point;
  }

  async function startFlushCreate(pending) {
    setPendingCreates((prev) =>
      prev.map((x) => (x.requestId === pending.requestId ? { ...x, isSaving: true, error: null } : x))
    );
    try {
      const point = await createPersistedFlushFromOrigin({
        startLL: pending.origin,
        name: pending.name,
        startedAtIso: pending.startedAtIso
      });
      mutatePoints((prev) => {
        const idx = prev.findIndex((p) => p.id === point.id);
        if (idx === -1) return [...prev, point];
        const next = prev.slice();
        next[idx] = { ...next[idx], ...point };
        return next;
      });
      setPendingCreates((prev) => prev.filter((x) => x.requestId !== pending.requestId));
      setFlushes((n) => n + 1);
    } catch (e) {
      setPendingCreates((prev) =>
        prev.map((x) =>
          x.requestId === pending.requestId
            ? { ...x, isSaving: false, error: String(e?.message || e) }
            : x
        )
      );
    }
  }

  function retryPendingCreate(requestId) {
    const pending = pendingCreates.find((x) => x.requestId === requestId);
    if (!pending || pending.isSaving) return;
    startFlushCreate(pending);
  }

  function addPointAt(lat, lng, name) {
    flushCounterRef.current += 1;
    const finalName = name && String(name).trim().length ? name : `Test ${flushCounterRef.current}`;
    const startedAtIso = new Date().toISOString();
    const requestId = `${Date.now()}-${Math.random()}`;
    const pending = {
      requestId,
      name: finalName,
      origin: { lat, lng },
      startedAtIso,
      isSaving: true,
      error: null
    };
    setPendingCreates((prev) => [...prev, pending]);
    startFlushCreate(pending);
  }

  // Convenience: add a point near the device location (tiny random offset)
  function addPoint(name) {
    const baseLat = deviceLoc.lat;
    const baseLng = deviceLoc.lng;

    const lat = baseLat + (Math.random() - 0.5) * 0.00008;
    const lng = baseLng + (Math.random() - 0.5) * 0.00008;

    addPointAt(lat, lng, name);
  }

  // Click-to-add handler (when enabled)
  function ClickToAddFlush() {
    useMapEvents({
      click(e) {
        if (!clickToFlush) return;
        const { lat, lng } = e.latlng;
        addPointAt(lat, lng, null);
      }
    });
    return null;
  }

  const reconcileActiveRuns = useCallback(async ({ replace = false, updatedAfter = null } = {}) => {
    if (reconcileInFlightRef.current) return;
    reconcileInFlightRef.current = true;
    try {
      const nowResp = await apiFetch("/api/time");
      const params = new URLSearchParams({ status: "active", limit: "1000" });
      if (updatedAfter) params.set("updated_after", updatedAfter);
      const runs = await apiFetch(`/api/flushes?${params.toString()}`);
      const nowMs = Date.parse(nowResp?.now || new Date().toISOString());
      const incoming = (Array.isArray(runs) ? runs : [])
        .map((r) => {
          const point = buildPointFromPersistedRun(r, nowMs);
          if (!point?.id) return null;
          const ts = Date.parse(r.updated_at || r.started_at || new Date().toISOString());
          return { point, ts };
        })
        .filter(Boolean);

      mutatePoints((prev) => {
        const next = replace ? [] : prev.slice();
        const indexById = new Map(next.map((p, i) => [p.id, i]));
        for (const { point, ts } of incoming) {
          const oldTs = lastServerUpdateRef.current.get(point.id) ?? -Infinity;
          if (ts < oldTs) continue;
          lastServerUpdateRef.current.set(point.id, ts);
          const idx = indexById.get(point.id);
          if (idx === undefined) {
            indexById.set(point.id, next.length);
            next.push(point);
          } else {
            next[idx] = { ...next[idx], ...point };
          }
        }
        return next;
      });
    } finally {
      reconcileInFlightRef.current = false;
    }
  }, [buildPointFromPersistedRun, mutatePoints]);

  useEffect(() => {
    if (!pipeData.ready || restoredOnceRef.current) return;
    let cancelled = false;
    (async () => {
      try {
        if (cancelled) return;
        await reconcileActiveRuns({ replace: true });
        if (cancelled) return;
        restoredOnceRef.current = true;
      } catch (e) {
        if (cancelled) return;
        console.warn("rehydrate failed", e);
      }
    })();
    return () => {
      cancelled = true;
    };
  }, [pipeData.ready, reconcileActiveRuns]);

  useEffect(() => {
    if (!pipeData.ready) return;
    const es = new EventSource(`${API_BASE_URL}/api/events`);

    es.addEventListener("flush_created", (evt) => {
      try {
        const run = JSON.parse(evt.data);
        const nowMs = Date.now();
        const point = buildPointFromPersistedRun(run, nowMs);
        if (!point?.id) return;
        const newTs = Date.parse(run.updated_at || run.started_at || new Date().toISOString());
        const oldTs = lastServerUpdateRef.current.get(point.id) ?? -Infinity;
        if (newTs < oldTs) return;
        lastServerUpdateRef.current.set(point.id, newTs);
        mutatePoints((prev) => {
          const idx = prev.findIndex((p) => p.id === point.id);
          if (idx === -1) return [...prev, point];
          const next = prev.slice();
          next[idx] = { ...next[idx], ...point };
          return next;
        });
      } catch (e) {
        console.warn("flush_created parse failed", e);
      }
    });

    es.addEventListener("connected", () => {
      const latest = Array.from(lastServerUpdateRef.current.values()).reduce((m, v) => Math.max(m, v), -Infinity);
      const updatedAfter = Number.isFinite(latest) ? new Date(latest).toISOString() : null;
      reconcileActiveRuns({ replace: false, updatedAfter }).catch((e) => {
        console.warn("sse connected reconcile failed", e);
      });
    });

    es.addEventListener("flush_status_updated", (evt) => {
      try {
        const msg = JSON.parse(evt.data);
        const id = msg?.id;
        if (!id) return;
        const newTs = Date.parse(msg.updated_at || new Date().toISOString());
        const oldTs = lastServerUpdateRef.current.get(id) ?? -Infinity;
        if (newTs < oldTs) return;
        lastServerUpdateRef.current.set(id, newTs);
        mutatePoints((prev) =>
          prev.map((p) => {
            if (p.id !== id) return p;
            if (msg.status === "arrived") {
              return {
                ...p,
                persistedStatus: "arrived",
                mode: "arrived",
                etaToDestinationSec: 0,
                currentVelocityBaseMps: 0,
                currentVelocitySimMps: 0
              };
            }
            if (msg.status === "error") {
              return {
                ...p,
                persistedStatus: "error",
                mode: "error",
                error: msg.error_message || p.error || "server_error"
              };
            }
            return { ...p, persistedStatus: "active" };
          })
        );
      } catch (e) {
        console.warn("flush_status_updated parse failed", e);
      }
    });

    es.onerror = () => {
      const now = Date.now();
      if (now - lastSseReconcileMsRef.current < 5000) return;
      lastSseReconcileMsRef.current = now;
      const latest = Array.from(lastServerUpdateRef.current.values()).reduce((m, v) => Math.max(m, v), -Infinity);
      const updatedAfter = Number.isFinite(latest) ? new Date(latest).toISOString() : null;
      reconcileActiveRuns({ replace: false, updatedAfter }).catch((e) => {
        console.warn("sse drift reconcile failed", e);
      });
    };

    return () => {
      es.close();
    };
  }, [pipeData.ready, buildPointFromPersistedRun, mutatePoints, reconcileActiveRuns]);

  useEffect(() => {
    const terminalish = renderPoints.filter(
      (p) => p?.id && p.persistedStatus === "active" && (p.mode === "arrived" || p.mode === "error")
    );
    if (terminalish.length === 0) return;
    terminalish.forEach((p) => {
      const targetStatus = p.mode === "arrived" ? "arrived" : "error";
      const already = lastSyncedStatusRef.current.get(p.id);
      if (already === targetStatus) return;
      lastSyncedStatusRef.current.set(p.id, targetStatus);
      apiFetch(`/api/flushes/${encodeURIComponent(p.id)}/status`, {
        method: "PATCH",
        body: JSON.stringify({
          status: targetStatus,
          errorMessage: p.mode === "error" ? p.error || "simulation_error" : null
        })
      }).catch((e) => {
        console.warn("status sync failed", e);
      });
    });
  }, [renderPoints]);

  // 4) Animate dots: street mode then pipe mode
  useEffect(() => {
    let rafId = 0;
    let lastTs = 0;
    let lastUiSyncTs = 0;
    let lastPerfLogTs = 0;

    const frameStep = (ts) => {
      if (!lastTs) lastTs = ts;
      const dtMs = ts - lastTs;
      const targetFps = perfMode === "mobile" ? ANIMATION_FPS_TARGET : 60;
      const targetFrameMs = 1000 / targetFps;
      if (dtMs < targetFrameMs) {
        rafId = requestAnimationFrame(frameStep);
        return;
      }
      lastTs = ts;
      const cappedDtMs = Math.min(100, dtMs);
      const withTelemetry = (obj, base, sim, eta) => ({
        ...obj,
        currentVelocityBaseMps: Number.isFinite(base) ? base : null,
        currentVelocitySimMps: Number.isFinite(sim) ? sim : null,
        etaToDestinationSec: Number.isFinite(eta) ? Math.max(0, eta) : null
      });

      let changed = false;
      const frameStart = performance.now();

      const nextPoints = pointsRef.current.map((pt) => {
        if (pt.mode === "error") return withTelemetry(pt, null, null, null);
        if (pt.mode === "arrived") return withTelemetry(pt, 0, 0, 0);

        if (pt.mode === "street" && pt.street && Array.isArray(pt.street.route)) {
          const route = pt.street.route;
          const idx = pt.street.idx || 1;
          const target = route[idx];
          if (!target) return pt;

          const here = { lat: pt.lat, lng: pt.lng };
          const stepMeters = pt.street.speedMps * speedMult * (cappedDtMs / 1000);
          const dist = metersBetween(here, target);

          if (dist <= stepMeters) {
            const nextIdx = idx + 1;
            const atEnd = nextIdx >= route.length;
            const moved = {
              ...pt,
              lat: target.lat,
              lng: target.lng,
              street: { ...pt.street, idx: nextIdx }
            };

            changed = true;
            if (!atEnd) return moved;

            const objectId = moved.contact?.pipeObjectId;
            if (!pipeData.byObjectId || objectId === null || !Array.isArray(moved.pipePlan) || moved.pipePlan.length < 2) {
              return withTelemetry({ ...moved, mode: "error", error: "Pipe network not ready" }, null, null, null);
            }

            const ft = pipeData.byObjectId.get(objectId);
            const props = ft?.properties || {};
            const vRaw = toNum(props._v_half_mps) || 0;
            const v = Math.max(PIPE_SPEED_MIN_MPS, vRaw);
            const simV = v * speedMult;
            const here2 = { lat: moved.lat, lng: moved.lng };
            const eta = remainingTimeOnPath(moved.pipePlan, 1, here2, pipeData.byObjectId, v);

            return withTelemetry({
              ...moved,
              mode: "pipe",
              street: moved.street ? { ...moved.street, visible: false } : moved.street,
              pipe: { objectId, idx: 1, speedMps: v, segmentVelocityMps: v },
              pipePlan: moved.pipePlan
            }, v, simV, eta);
          }

          const f = stepMeters / dist;
          changed = true;
          const nextStreet = {
            ...pt,
            lat: pt.lat + (target.lat - pt.lat) * f,
            lng: pt.lng + (target.lng - pt.lng) * f
          };
          const baseV = pt.street.speedMps;
          const simV = baseV * speedMult;
          const remainingStreetM = remainingDistanceOnPath(route, idx, { lat: nextStreet.lat, lng: nextStreet.lng });
          const pipeBaseV = toNum(pt.pipe?.speedMps) || (toNum(pt.contact?.pipeVelocityMps) || PIPE_SPEED_MIN_MPS);
          const streetEta = baseV > 0 ? remainingStreetM / baseV : null;
          const pipeEta = Array.isArray(pt.pipePlan) && pt.pipePlan.length > 0
            ? remainingTimeOnPath(pt.pipePlan, 0, pt.pipePlan[0], pipeData.byObjectId, pipeBaseV)
            : null;
          const eta = streetEta !== null && pipeEta !== null ? streetEta + pipeEta : streetEta ?? pipeEta;
          return withTelemetry(nextStreet, baseV, simV, eta);
        }

        if (pt.mode === "pipe" && pt.pipePlan && Array.isArray(pt.pipePlan)) {
          const plan = pt.pipePlan;
          const idx = pt.pipe?.idx || 1;
          const target = plan[idx];
          if (!target) {
            if (pt.routingStatus === "incomplete") {
              return withTelemetry({ ...pt, mode: "error", error: "Incomplete route to endpoint" }, null, null, null);
            }
            return withTelemetry({ ...pt, mode: "arrived" }, 0, 0, 0);
          }

          let speed = pt.pipe?.speedMps || 0.6;
          const objectId = target?.objectId ?? pt.pipe?.objectId;
          if (pipeData.byObjectId && objectId !== null && objectId !== undefined) {
            const ft = pipeData.byObjectId.get(objectId);
            const props = ft?.properties || {};
            const vRaw = toNum(props._v_half_mps) || speed;
            speed = Math.max(PIPE_SPEED_MIN_MPS, vRaw);
          }

          const here = { lat: pt.lat, lng: pt.lng };
          const stepMeters = speed * speedMult * (cappedDtMs / 1000);
          const dist = metersBetween(here, target);

          if (dist <= stepMeters) {
            const nextIdx = idx + 1;
            const atEnd = nextIdx >= plan.length;
            changed = true;
            const nextPipe = {
              ...pt,
              lat: target.lat,
              lng: target.lng,
              pipe: { ...pt.pipe, idx: nextIdx, speedMps: speed, objectId: objectId ?? pt.pipe?.objectId },
              mode: atEnd ? "arrived" : "pipe"
            };
            if (atEnd) return withTelemetry(nextPipe, 0, 0, 0);
            const simV = speed * speedMult;
            const eta = remainingTimeOnPath(plan, nextIdx, { lat: nextPipe.lat, lng: nextPipe.lng }, pipeData.byObjectId, speed);
            return withTelemetry(nextPipe, speed, simV, eta);
          }

          const f = stepMeters / dist;
          changed = true;
          const movingPipe = {
            ...pt,
            lat: pt.lat + (target.lat - pt.lat) * f,
            lng: pt.lng + (target.lng - pt.lng) * f,
            pipe: { ...pt.pipe, speedMps: speed }
          };
          const simV = speed * speedMult;
          const eta = remainingTimeOnPath(plan, idx, { lat: movingPipe.lat, lng: movingPipe.lng }, pipeData.byObjectId, speed);
          return withTelemetry(movingPipe, speed, simV, eta);
        }

        return withTelemetry(pt, null, null, null);
      });

      pointsRef.current = nextPoints;

      const uiSyncPeriodMs = 1000 / UI_SYNC_FPS;
      if (changed && ts - lastUiSyncTs >= uiSyncPeriodMs) {
        lastUiSyncTs = ts;
        setRenderPoints(nextPoints);
      }

      if (ts - lastPerfLogTs >= 2000) {
        lastPerfLogTs = ts;
        perfLog("animation tick", {
          points: nextPoints.length,
          frameMs: Math.round(performance.now() - frameStart),
          targetFps
        });
      }

      rafId = requestAnimationFrame(frameStep);
    };

    rafId = requestAnimationFrame(frameStep);
    return () => cancelAnimationFrame(rafId);
  }, [perfMode, pipeData.byObjectId, speedMult]);

  const pipeStats = useMemo(() => {
    if (!pipeData.ready) return "Pipes: loading…";
    return `Pipes: ${pipeData.count.toLocaleString()} | Nodes: ${pipeData.nodeCount.toLocaleString()}`;
  }, [pipeData.ready, pipeData.count, pipeData.nodeCount]);
  const trackedByUser = useMemo(() => {
    const counts = Object.fromEntries(users.map((u) => [u, 0]));
    for (const p of renderPoints) {
      if (!(p.name in counts)) continue;
      if (p.mode === "arrived" || p.mode === "error") continue;
      counts[p.name] += 1;
    }
    return counts;
  }, [renderPoints]);

  const recenterToDevice = useCallback(() => {
    const map = mapRef.current;
    if (!map) return;
    if (deviceLoc.ready) {
      map.setView([deviceLoc.lat, deviceLoc.lng], 14);
      return;
    }
    if (!("geolocation" in navigator)) return;
    navigator.geolocation.getCurrentPosition(
      (pos) => {
        const lat = pos.coords.latitude;
        const lng = pos.coords.longitude;
        setDeviceLoc({ ready: true, lat, lng });
        try {
          window.localStorage.setItem("flush:lastDeviceLoc", JSON.stringify({ lat, lng }));
        } catch {
          // ignore storage errors
        }
        map.setView([lat, lng], 14);
      },
      () => {}
    );
  }, [deviceLoc.ready, deviceLoc.lat, deviceLoc.lng]);

  return (
    <div className="layout">
      <div className="sidebar">
        <div className="sidebarTop">
          <div className="counterSub">Updated: {APP_LAST_UPDATED}</div>
          <div className="counter">Flushes: {flushes}</div>
          <div className="counterSub">Location: {selectedPipeDataset.label}</div>
          <div className="counterSub">{pipeStats}</div>
          {pendingCreates.length > 0 && (
            <div className="counterSub">
              Saving flushes: {pendingCreates.filter((p) => p.isSaving).length}
            </div>
          )}
          {pendingCreates.map((p) => (
            <div key={p.requestId} className="counterSub">
              {p.name}: {p.isSaving ? "Saving flush..." : `Save failed (${p.error || "unknown"})`}
              {!p.isSaving && (
                <>
                  {" "}
                  <button className="inlineRetryBtn" onClick={() => retryPendingCreate(p.requestId)}>Retry</button>
                </>
              )}
            </div>
          ))}

          {users.map((u) => (
            <button key={u} onClick={() => addPoint(u)}>
              {u} ({trackedByUser[u] || 0} tracking)
            </button>
          ))}
        </div>

        <div className="sidebarBottom">
          <div className="sidebarSectionTitle">Simulation</div>
          <button onClick={cycleSpeed}>
            Speed: {speedMult}x
          </button>
          <button onClick={() => setClickToFlush((v) => !v)}>
            {clickToFlush ? "Click-to-flush: ON" : "Click-to-flush: OFF"}
          </button>
          <button onClick={clearAll}>
            Clear All
          </button>
        </div>
      </div>

      <div className="map">
        <button className="settingsFab" onClick={() => setIsSettingsOpen(true)} aria-label="Open settings">
          Settings
        </button>
        <button className="recenterFab" onClick={recenterToDevice} aria-label="Recenter to my location">
          My location
        </button>
        <MapContainer
          center={[selectedPipeDataset.center.lat, selectedPipeDataset.center.lng]}
          zoom={13}
          preferCanvas
          style={{ height: "100%", width: "100%" }}
          whenCreated={(map) => {
            mapRef.current = map;
            setMapReady(true);
          }}
        >
          <TileLayer
            attribution='&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors &copy; <a href="https://carto.com/attributions">CARTO</a>'
            url="https://{s}.basemaps.cartocdn.com/rastertiles/voyager_nolabels/{z}/{x}/{y}{r}.png"
          />
          <ClickToAddFlush />

          <PipeGeoJsonLayer
            geojson={pipeData.geojson}
            showPipeGlow={perfMode === "desktop" && showPipeGlow}
            perfMode={perfMode}
          />
          <EndpointsLayer terminalNodes={pipeData.trueTerminalNodes} showEndpoints={showEndpoints} />
          <StreetRoutesLayer points={renderPoints} showStreetRoutes={showStreetRoutes} />
          <PipePlansLayer points={renderPoints} showPipePlans={showPipePlans} byObjectId={pipeData.byObjectId} />
          <FallbackBridgeLayer points={renderPoints} showFallbackBridges={showFallbackBridges} />
          <MovingPointsLayer points={renderPoints} showLabels={showLabels} isMobileViewport={isMobileViewport} />
        </MapContainer>

        <SettingsModal
          isOpen={isSettingsOpen}
          onClose={() => setIsSettingsOpen(false)}
          locationId={pipeDatasetId}
          setLocationId={setPipeDatasetId}
          locationOptions={PIPE_DATASETS}
          perfMode={perfMode}
          setPerfMode={setPerfMode}
          showLabels={showLabels}
          setShowLabels={setShowLabels}
          showPipeGlow={showPipeGlow}
          setShowPipeGlow={setShowPipeGlow}
          showEndpoints={showEndpoints}
          setShowEndpoints={setShowEndpoints}
          showFallbackBridges={showFallbackBridges}
          setShowFallbackBridges={setShowFallbackBridges}
          routingFallbackMode={routingFallbackMode}
          setRoutingFallbackMode={setRoutingFallbackMode}
          showStreetRoutes={showStreetRoutes}
          setShowStreetRoutes={setShowStreetRoutes}
          showPipePlans={showPipePlans}
          setShowPipePlans={setShowPipePlans}
          speedMult={speedMult}
          cycleSpeed={cycleSpeed}
          clickToFlush={clickToFlush}
          setClickToFlush={setClickToFlush}
        />
      </div>
    </div>
  );
}
