import { useEffect, useMemo, useRef, useState } from "react";
import "./App.css";

import "leaflet/dist/leaflet.css";
import { MapContainer, TileLayer, GeoJSON, CircleMarker, Popup, Polyline, Tooltip } from "react-leaflet";

const users = ["Tom", "Steph", "Molly", "Delilah", "Luella"];

// Fallback centre (Elsternwick-ish) if geolocation is blocked/unavailable
const FALLBACK_CENTER = { lat: -37.885, lng: 145.01 };

// Public OSRM demo server (OK for prototyping; consider self-hosting for reliability/scale)
const OSRM_ROUTE_URL = "https://router.project-osrm.org/route/v1/driving";

// Street-route travel speed (m/s) approximation for suburban catchment/house-branch drains.
// Typical self-cleansing/flow velocities are often ~0.6–1.5 m/s; we use a mid value.
const STREET_SPEED_MPS = 1.1;

// Snap tolerance (metres) when determining pipe connectivity by endpoints
// Node snapping tolerance (metres). The sewer network often has endpoints digitised a few
// metres apart at complex structures (e.g. pump stations). A slightly larger tolerance
// reduces "bouncing" between near-identical junction nodes.
const NODE_SNAP_TOL_M = 5;

// Simulation safety clamps
const PIPE_SPEED_MIN_MPS = 0.2;
const PIPE_SPEED_MAX_MPS = 3.0;

const R_MERC = 6378137;

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

function routeDistanceMeters(route) {
  if (!Array.isArray(route) || route.length < 2) return 0;
  let d = 0;
  for (let i = 1; i < route.length; i++) {
    d += metersBetween(route[i - 1], route[i]);
  }
  return d;
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

  // Convert raw [lng,lat] arrays to {lat,lng}
  const toLL = (c) => ({ lat: c[1], lng: c[0] });

  if (g.type === "LineString") {
    return Array.isArray(g.coordinates) ? g.coordinates.map(toLL) : [];
  }

  if (g.type === "MultiLineString") {
    const parts = Array.isArray(g.coordinates) ? g.coordinates : [];
    // Return the single longest part (prevents stitching loops)
    let best = [];
    let bestLen = -1;

    for (const part of parts) {
      if (!Array.isArray(part) || part.length < 2) continue;
      const len = part.length;
      if (len > bestLen) {
        bestLen = len;
        best = part;
      }
    }

    return bestLen > 0 ? best.map(toLL) : [];
  }

  return [];
}


function parseDirFromProps(props) {
  // DIR may be supplied in the source data (e.g. "u_to_d" or "d_to_u").
  // Accept a few common key variants and normalise.
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


function featureEndpointsLngLat(ft) {
  const g = ft?.geometry;
  if (!g) return { start: null, end: null };

  if (g.type === "LineString") {
    const coords = g.coordinates || [];
    if (coords.length >= 2) return { start: coords[0], end: coords[coords.length - 1] };
    return { start: null, end: null };
  }

  if (g.type !== "MultiLineString") return { start: null, end: null };

  const lines = Array.isArray(g.coordinates) ? g.coordinates : [];
  if (lines.length === 0) return { start: null, end: null };

  // MultiLineString handling:
  // Many assets represent complex structures (e.g. pump stations) as multiple parts.
  // To avoid choosing the wrong endpoints, derive endpoints from the graph of part endpoints:
  // - Count how many times each endpoint coordinate appears (snapped to a small tolerance).
  // - True endpoints usually appear once (degree 1). For a connected chain, there should be 2.
  // - If the geometry is a loop (no degree-1 endpoints), fall back to first/last of the longest part.
  const END_TOL_M = 0.25;

  const endpoints = [];
  for (const part of lines) {
    if (!Array.isArray(part) || part.length < 2) continue;
    endpoints.push(part[0], part[part.length - 1]);
  }
  if (endpoints.length < 2) return { start: null, end: null };

  const counts = new Map();
  const keyOf = (c) => nodeKeyFromLngLat(c[0], c[1], END_TOL_M);
  for (const c of endpoints) {
    const k = keyOf(c);
    counts.set(k, (counts.get(k) || 0) + 1);
  }

  const degree1 = endpoints.filter((c) => (counts.get(keyOf(c)) || 0) === 1);

  const dist2 = (a, b) => {
    const A = mercatorMetersFromLngLat(a[0], a[1]);
    const B = mercatorMetersFromLngLat(b[0], b[1]);
    const dx = A.x - B.x;
    const dy = A.y - B.y;
    return dx * dx + dy * dy;
  };

  if (degree1.length >= 2) {
    // Choose the two farthest degree-1 endpoints (stable even if there are >2 due to digitising quirks)
    let bestA = degree1[0];
    let bestB = degree1[1];
    let bestD = dist2(bestA, bestB);

    for (let i = 0; i < degree1.length; i++) {
      for (let j = i + 1; j < degree1.length; j++) {
        const d = dist2(degree1[i], degree1[j]);
        if (d > bestD) {
          bestD = d;
          bestA = degree1[i];
          bestB = degree1[j];
        }
      }
    }
    return { start: bestA, end: bestB };
  }

  // Loop or fully connected multi-part: fall back to longest part endpoints
  let bestPart = null;
  let bestLen2 = -1;
  for (const part of lines) {
    if (!Array.isArray(part) || part.length < 2) continue;
    const a = part[0];
    const b = part[part.length - 1];
    const d = dist2(a, b);
    if (d > bestLen2) {
      bestLen2 = d;
      bestPart = part;
    }
  }

  if (bestPart) return { start: bestPart[0], end: bestPart[bestPart.length - 1] };
  return { start: null, end: null };
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

function bearingDeg(a, b) {
  const lat1 = (a.lat * Math.PI) / 180;
  const lat2 = (b.lat * Math.PI) / 180;
  const dLng = ((b.lng - a.lng) * Math.PI) / 180;

  const y = Math.sin(dLng) * Math.cos(lat2);
  const x =
    Math.cos(lat1) * Math.sin(lat2) -
    Math.sin(lat1) * Math.cos(lat2) * Math.cos(dLng);

  const brng = (Math.atan2(y, x) * 180) / Math.PI;
  return (brng + 360) % 360;
}

function angleDiffDeg(a, b) {
  const d = Math.abs(a - b) % 360;
  return d > 180 ? 360 - d : d;
}

function orderedCoordsForPipe(ft) {
  const p = ft?.properties || {};
  const coords = flattenFeatureCoords(ft);
  if (coords.length < 2) return [];
  const dir = String(p._dir || "u_to_d");
  return dir === "d_to_u" ? coords.slice().reverse() : coords;
}

function chooseNextPipeDirOnly(nextIds, byObjectId, currOrderedCoords, prevId, visited) {
  const ids0 = Array.isArray(nextIds) ? nextIds : [];
  const ids1 = ids0.filter((id) => id !== prevId && !visited.has(id));
  const ids = ids1.length > 0 ? ids1 : ids0.filter((id) => id !== prevId);

  if (ids.length === 0) return null;
  if (ids.length === 1) return ids[0];

  // Direction continuity: pick the candidate whose initial bearing best matches the
  // current pipe's terminal bearing (downstream end). This avoids "bouncing" at dense nodes
  // while staying strictly within DIR-defined connectivity.
  const n = currOrderedCoords.length;
  const a = currOrderedCoords[Math.max(0, n - 2)];
  const b = currOrderedCoords[n - 1];
  const currBrng = bearingDeg(a, b);

  let bestId = null;
  let bestDelta = Infinity;

  for (const id of ids) {
    const ft = byObjectId.get(id);
    const ord = orderedCoordsForPipe(ft);
    if (ord.length < 2) continue;

    const candBrng = bearingDeg(ord[0], ord[1]);
    const delta = angleDiffDeg(currBrng, candBrng);

    if (delta < bestDelta) {
      bestDelta = delta;
      bestId = id;
    }
  }

  if (bestId !== null) return bestId;

  // Last resort: stable deterministic choice
  return ids.slice().sort((x, y) => x - y)[0] ?? null;
}


function buildPipePlanFromObjectId(startObjectId, startPoint, byObjectId, maxHops = 2000) {
  // DIR-only traversal:
  // - The directed graph is encoded in each feature's `_nextObjectIds` which is computed
  //   strictly from endpoint node connectivity (upNode -> downNode) based on `_dir`.
  // - No virtual links, no nearest-segment snaps, no name jumps, no IL heuristics.
  const plan = [];
  const visited = new Set();

  let currentId = startObjectId;
  let prevId = null;

  let first = true;

  // Light de-dup to avoid repeated points at joins (visual noise)
  const visitedCells = new Set();

  for (let hop = 0; hop < maxHops; hop++) {
    if (currentId == null) break;
    if (visited.has(currentId)) break;

    const ft = byObjectId.get(currentId);
    if (!ft) break;

    visited.add(currentId);

    const ord = orderedCoordsForPipe(ft);
    if (ord.length < 2) break;

    if (first && startPoint) {
      // Insert snap point, then follow this pipe from the nearest coord onward (downstream).
      plan.push({ lng: startPoint.lng, lat: startPoint.lat });

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
        plan.push(ord[i]);
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
        plan.push(pt);
      }
    }

    const props = ft.properties || {};
    const nextIds = Array.isArray(props._nextObjectIds) ? props._nextObjectIds : [];

    const nextId = chooseNextPipeDirOnly(nextIds, byObjectId, ord, prevId, visited);

    // Debug
    if (visited.size < 80) {
      const currName = dbgName(props);
      const cand = nextIds.join(", ");
      console.log(
        "[PIPEHOP] " +
          currentId +
          " -> " +
          nextId +
          ' | name="' +
          currName +
          '" | candidates=[' +
          cand +
          "]"
      );
    }

    prevId = currentId;
    currentId = nextId;
  }

  return plan;
}




export default function App() {
  const [flushes, setFlushes] = useState(0);

  const [pipeData, setPipeData] = useState({
    ready: false,
    geojson: null,
    bbox: null,
    count: 0,
    nodeCount: 0,
    byObjectId: null
  });

  // Device start location (from browser geolocation)
  const [deviceLoc, setDeviceLoc] = useState({
    ready: false,
    lat: FALLBACK_CENTER.lat,
    lng: FALLBACK_CENTER.lng
  });

  const [showStreetRoutes, setShowStreetRoutes] = useState(true);
  const [showPipePlans, setShowPipePlans] = useState(true);
  const [speed10x, setSpeed10x] = useState(false);

  // People points
  // mode: "street" | "pipe" | "arrived" | "error"
  const [points, setPoints] = useState([]);

  // Keep map instance so we can recenter once geolocation arrives
  const mapRef = useRef(null);

  // 1) Load pipes GeoJSON from /public + compute velocities + direction + connectivity
  useEffect(() => {
    let cancelled = false;

    async function load() {
      try {
        const res = await fetch("/Sewerage_Network_Main_Pipelines.geojson");
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

// DIR-only connectivity with endpoint merging:
// Some real-world junctions (e.g. pump stations, chambers) have pipe endpoints digitised
// a few to many metres apart, so strict endpoint equality breaks the directed graph.
// Option B: merge ONLY endpoints that are within MERGE_RADIUS_M of each other, then build
// directed adjacency strictly by DIR using these merged endpoint clusters.
const MERGE_RADIUS_M = 20;

// Union-Find for clustering endpoints
class UF {
  constructor(n) {
    this.p = Array.from({ length: n }, (_, i) => i);
    this.r = Array(n).fill(0);
  }
  find(x) {
    while (this.p[x] !== x) {
      this.p[x] = this.p[this.p[x]];
      x = this.p[x];
    }
    return x;
  }
  union(a, b) {
    let ra = this.find(a);
    let rb = this.find(b);
    if (ra === rb) return;
    if (this.r[ra] < this.r[rb]) [ra, rb] = [rb, ra];
    this.p[rb] = ra;
    if (this.r[ra] === this.r[rb]) this.r[ra]++;
  }
}

// Spatial hash to find nearby endpoints efficiently (Mercator metres)
function cellKeyForMeters(m, cellSize) {
  const cx = Math.floor(m.x / cellSize);
  const cy = Math.floor(m.y / cellSize);
  return `${cx}_${cy}`;
}

const endpointRecords = []; // { ft, objectId, upLL, downLL }

// Pass 1: compute bbox + per-pipe velocity + DIR + store endpoints (do NOT build nodes yet)
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

  // Determine endpoints for this feature (robust for MultiLineString)
  const ep = featureEndpointsLngLat(ft);
  const start = ep.start;
  const end = ep.end;

  // Compute Manning velocity (half-full assumption)
  const hv = computeHalfFullVelocityMps(props);
  props._manning_n = hv.n;
  props._slope_S = hv.S;
  props._v_half_mps = hv.v;

  // Determine direction.
  const dirFromData = parseDirFromProps(props);
  const upIL = toNum(props.UPSTREAM_IL);
  const downIL = toNum(props.DOWNSTREAM_IL);

  let dir = "u_to_d";
  let dirSource = "default";
  if (dirFromData) {
    dir = dirFromData;
    dirSource = "DIR";
  } else if (upIL !== null && downIL !== null) {
    dir = upIL >= downIL ? "u_to_d" : "d_to_u";
    dirSource = "IL";
  }

  props._dir = dir;
  props._dir_source = dirSource;

  if (objectId !== null && start && end) {
    const startLL = { lng: start[0], lat: start[1] };
    const endLL = { lng: end[0], lat: end[1] };

    // FLOW ENDPOINTS:
    // In this dataset, DIR indicates whether the geometry runs Up->Down ("u_to_d")
    // or Down->Up ("d_to_u"). In both cases the FLOW follows the geometry order:
    //   flowStart = geometry start, flowEnd = geometry end.
    //
    // Only when DIR is missing do we fall back to IL/default inference, where the
    // geometry order may not match flow and we may need to reverse.
    const upLL = (dirSource === "DIR") ? startLL : (dir === "u_to_d" ? startLL : endLL);   // flow-start node
    const downLL = (dirSource === "DIR") ? endLL : (dir === "u_to_d" ? endLL : startLL);  // flow-end node

    endpointRecords.push({ ft, objectId, upLL, downLL });
    byObjectId.set(objectId, ft);
  }

  ft.properties = props;
}

// Cluster all endpoints (up + down) by MERGE_RADIUS_M in Mercator metres
const endpoints = []; // { lng, lat, mx, my, recIndex, which }
for (let i = 0; i < endpointRecords.length; i++) {
  const r = endpointRecords[i];
  const upM = mercatorMetersFromLngLat(r.upLL.lng, r.upLL.lat);
  const dnM = mercatorMetersFromLngLat(r.downLL.lng, r.downLL.lat);
  endpoints.push({ lng: r.upLL.lng, lat: r.upLL.lat, m: upM, recIndex: i, which: "up" });
  endpoints.push({ lng: r.downLL.lng, lat: r.downLL.lat, m: dnM, recIndex: i, which: "down" });
}

const uf = new UF(endpoints.length);
const grid = new Map();
const cellSize = MERGE_RADIUS_M;

function addToGrid(idx) {
  const e = endpoints[idx];
  const k = cellKeyForMeters(e.m, cellSize);
  if (!grid.has(k)) grid.set(k, []);
  grid.get(k).push(idx);
}

for (let i = 0; i < endpoints.length; i++) addToGrid(i);

function distM(i, j) {
  const a = endpoints[i].m;
  const b = endpoints[j].m;
  const dx = a.x - b.x;
  const dy = a.y - b.y;
  return Math.sqrt(dx * dx + dy * dy);
}

// For each cell, compare to self + 8 neighbors
for (const [k, idxs] of grid.entries()) {
  const [cxStr, cyStr] = k.split("_");
  const cx = parseInt(cxStr, 10);
  const cy = parseInt(cyStr, 10);

  for (let ox = -1; ox <= 1; ox++) {
    for (let oy = -1; oy <= 1; oy++) {
      const nk = `${cx + ox}_${cy + oy}`;
      const other = grid.get(nk);
      if (!other) continue;

      for (const i of idxs) {
        for (const j of other) {
          if (j <= i) continue; // avoid dup
          if (distM(i, j) <= MERGE_RADIUS_M) uf.union(i, j);
        }
      }
    }
  }
}

// Build cluster centroids (for stable node coords)
const cluster = new Map(); // root -> { sumLng, sumLat, n }
for (let i = 0; i < endpoints.length; i++) {
  const r = uf.find(i);
  const e = endpoints[i];
  const c = cluster.get(r) || { sumLng: 0, sumLat: 0, n: 0 };
  c.sumLng += e.lng;
  c.sumLat += e.lat;
  c.n += 1;
  cluster.set(r, c);
}

function clusterKey(root) {
  return `C${root}`;
}

// Assign up/down node keys to each pipe from clustered endpoints and build directed node index
for (let recIndex = 0; recIndex < endpointRecords.length; recIndex++) {
  const r = endpointRecords[recIndex];
  const ft = r.ft;
  const props = ft.properties || {};

  const upEndpointIdx = recIndex * 2;
  const downEndpointIdx = recIndex * 2 + 1;

  const upRoot = uf.find(upEndpointIdx);
  const dnRoot = uf.find(downEndpointIdx);

  const upK = clusterKey(upRoot);
  const dnK = clusterKey(dnRoot);

  const upC = cluster.get(upRoot);
  const dnC = cluster.get(dnRoot);

  props._upNodeKey = upK;
  props._downNodeKey = dnK;

  const upLng = upC ? upC.sumLng / upC.n : r.upLL.lng;
  const upLat = upC ? upC.sumLat / upC.n : r.upLL.lat;
  const dnLng = dnC ? dnC.sumLng / dnC.n : r.downLL.lng;
  const dnLat = dnC ? dnC.sumLat / dnC.n : r.downLL.lat;

  const upNode = ensureNode(upK, upLng, upLat);
  const downNode = ensureNode(dnK, dnLng, dnLat);

  upNode.outObjectIds.push(r.objectId);
  downNode.inObjectIds.push(r.objectId);

  ft.properties = props;
}

// Pass 2: compute next connections for each pipe (STRICT DIR CONNECTIVITY ON MERGED ENDPOINT NODES)
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
        const bbox =
          isFinite(minLat) && isFinite(minLng) && isFinite(maxLat) && isFinite(maxLng)
            ? { minLat, minLng, maxLat, maxLng }
            : null;

        if (cancelled) return;

        setPipeData({
          ready: true,
          geojson: gj,
          bbox,
          count: features.length,
          nodeCount: nodeIndex.size,
          byObjectId
        });
      } catch (e) {
        if (cancelled) return;
        console.error(e);
        setPipeData({
          ready: false,
          geojson: null,
          bbox: null,
          count: 0,
          nodeCount: 0,
          byObjectId: null
        });
      }
    }

    load();
    return () => {
      cancelled = true;
    };
  }, []);

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

        const map = mapRef.current;
        if (map) map.setView([lat, lng], 14);
      },
      () => {
        // Keep fallback centre
      },
      {
        enableHighAccuracy: true,
        timeout: 8000,
        maximumAge: 60000
      }
    );
  }, []);

  async function buildStreetRouteForPoint(pointId, startLL) {
    if (!pipeData.geojson) return;

    const contact = findNearestPipeContact(pipeData.geojson, startLL);
    if (!contact || !contact.point) {
      setPoints((prev) =>
        prev.map((pt) => (pt.id === pointId ? { ...pt, mode: "error", error: "No pipes found" } : pt))
      );
      return;
    }

    const props = contact.feature?.properties || {};
    const objectId = toNum(props.OBJECTID);

    try {
      const route = await fetchOsrmRoute(startLL, contact.point);
      const distM = routeDistanceMeters(route);
      const etaS = STREET_SPEED_MPS > 0 ? distM / STREET_SPEED_MPS : 0;
	  
	  const pipePlan =
	    pipeData.byObjectId && objectId !== null
		  ? buildPipePlanFromObjectId(objectId, contact.point, pipeData.byObjectId)
		  : null;
	  
      setPoints((prev) =>
        prev.map((pt) =>
          pt.id === pointId
            ? {
                ...pt,
                mode: "street",
                street: {
                  route,
                  idx: 1,
                  speedMps: STREET_SPEED_MPS,
                  distM,
                  etaS,
                  visible: true
                },
                contact: {
                  point: contact.point,
                  pipeObjectId: objectId
                },
                pipe: null,
                pipePlan
              }
            : pt
        )
      );
    } catch (e) {
      console.error(e);
      setPoints((prev) =>
        prev.map((pt) =>
          pt.id === pointId ? { ...pt, mode: "error", error: String(e?.message || e) } : pt
        )
      );
    }
  }

  function enterPipeMode(pointId) {
    setPoints((prev) =>
      prev.map((pt) => {
        if (pt.id !== pointId) return pt;

        const contactPoint = pt.contact?.point;
        const objectId = pt.contact?.pipeObjectId;

        if (!pipeData.byObjectId || objectId === null || !contactPoint) {
          return { ...pt, mode: "error", error: "Pipe network not ready" };
        }

        const ft = pipeData.byObjectId.get(objectId);
        const props = ft?.properties || {};

        const vRaw = toNum(props._v_half_mps) || 0;
        const v = clamp(vRaw, PIPE_SPEED_MIN_MPS, PIPE_SPEED_MAX_MPS);

        const plan = buildPipePlanFromObjectId(objectId, contactPoint, pipeData.byObjectId);

        return {
          ...pt,
          mode: "pipe",
          street: pt.street ? { ...pt.street, visible: false } : pt.street,
          pipe: {
            objectId,
            idx: 1,
            speedMps: v,
            segmentVelocityMps: v
          },
          pipePlan: plan
        };
      })
    );
  }

  // 3) Add a dot and immediately create its street route to nearest pipe
  function addPoint(name) {
    const baseLat = deviceLoc.lat;
    const baseLng = deviceLoc.lng;

    // Tiny random starting offset (~ a few metres)
    const lat = baseLat + (Math.random() - 0.5) * 0.00008;
    const lng = baseLng + (Math.random() - 0.5) * 0.00008;

    const id = Date.now() + Math.random();

    setFlushes((n) => n + 1);

    setPoints((p) => [
      ...p,
      {
        id,
        name,
        lat,
        lng,
        mode: "street",
        street: null,
        contact: null,
        pipe: null,
        pipePlan: null,
        error: null
      }
    ]);

    if (pipeData.geojson) {
      buildStreetRouteForPoint(id, { lat, lng });
    }
  }

  // If a point was added before pipes loaded, route it once pipes arrive
  useEffect(() => {
    if (!pipeData.geojson) return;

    const unrouted = points.filter((p) => p.mode === "street" && !p.street && !p.error);
    if (unrouted.length === 0) return;

    for (const p of unrouted) {
      buildStreetRouteForPoint(p.id, { lat: p.lat, lng: p.lng });
    }
  }, [pipeData.geojson]); // eslint-disable-line react-hooks/exhaustive-deps

  // 4) Animate dots: street mode then pipe mode
  useEffect(() => {
    const TICK_MS = 80;
    const timer = setInterval(() => {
      setPoints((prev) =>
        prev.map((pt) => {
          if (pt.mode === "error" || pt.mode === "arrived") return pt;

          // Street movement
          if (pt.mode === "street" && pt.street && Array.isArray(pt.street.route)) {
            const route = pt.street.route;
            const idx = pt.street.idx || 1;
            const target = route[idx];

            if (!target) {
              // Arrived at contact point; switch to pipe mode
              return pt;
            }

            const here = { lat: pt.lat, lng: pt.lng };
            const speedMult = speed10x ? 10 : 1;
            const stepMeters = (pt.street.speedMps * speedMult * TICK_MS) / 1000;
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

              if (atEnd) {
                // We reached the final street route point (contact); enter pipe mode next tick
                setTimeout(() => enterPipeMode(pt.id), 0);
              }

              return moved;
            }

            const f = stepMeters / dist;
            const lat = pt.lat + (target.lat - pt.lat) * f;
            const lng = pt.lng + (target.lng - pt.lng) * f;

            return { ...pt, lat, lng };
          }

          // Pipe movement
          if (pt.mode === "pipe" && pt.pipePlan && Array.isArray(pt.pipePlan)) {
            const plan = pt.pipePlan;
            const idx = pt.pipe?.idx || 1;
            const target = plan[idx];

            if (!target) {
              return { ...pt, mode: "arrived" };
            }

            const here = { lat: pt.lat, lng: pt.lng };

            // Determine speed for current pipe feature (updates at junctions by re-reading properties)
            let speed = pt.pipe?.speedMps || 0.6;

            // If we can identify current feature by objectId and update speed from it:
            const objectId = pt.pipe?.objectId;
            if (pipeData.byObjectId && objectId !== null && objectId !== undefined) {
              const ft = pipeData.byObjectId.get(objectId);
              const props = ft?.properties || {};
              const vRaw = toNum(props._v_half_mps) || speed;
              speed = clamp(vRaw, PIPE_SPEED_MIN_MPS, PIPE_SPEED_MAX_MPS);
            }

            const speedMult = speed10x ? 10 : 1;
            const stepMeters = (speed * speedMult * TICK_MS) / 1000;
            const dist = metersBetween(here, target);

            if (dist <= stepMeters) {
              const nextIdx = idx + 1;
              const atEnd = nextIdx >= plan.length;

              return {
                ...pt,
                lat: target.lat,
                lng: target.lng,
                pipe: { ...pt.pipe, idx: nextIdx, speedMps: speed },
                mode: atEnd ? "arrived" : "pipe"
              };
            }

            const f = stepMeters / dist;
            const lat = pt.lat + (target.lat - pt.lat) * f;
            const lng = pt.lng + (target.lng - pt.lng) * f;

            return { ...pt, lat, lng, pipe: { ...pt.pipe, speedMps: speed } };
          }

          return pt;
        })
      );
    }, TICK_MS);

    return () => clearInterval(timer);
  }, [pipeData.byObjectId, speed10x]);

  const pipeStats = useMemo(() => {
    if (!pipeData.ready) return "Pipes: loading…";
    return `Pipes: ${pipeData.count.toLocaleString()} | Nodes: ${pipeData.nodeCount.toLocaleString()}`;
  }, [pipeData.ready, pipeData.count, pipeData.nodeCount]);

  const lastFew = useMemo(() => points.slice(-5), [points]);

  return (
    <div className="layout">
      <div className="sidebar">
        <div className="counter">Flushes: {flushes}</div>
        <div className="counterSub">{pipeStats}</div>

        <button onClick={() => setShowStreetRoutes((v) => !v)}>
          {showStreetRoutes ? "Hide street routes" : "Show street routes"}
        </button>

        <button onClick={() => setShowPipePlans((v) => !v)}>
          {showPipePlans ? "Hide pipe plan" : "Show pipe plan"}
        </button>

        <button onClick={() => setSpeed10x((v) => !v)}>
          {speed10x ? "Speed: 10×" : "Speed: 1×"}
        </button>

        {users.map((u) => (
          <button key={u} onClick={() => addPoint(u)}>
            {u}
          </button>
        ))}

        <pre>{JSON.stringify(lastFew, null, 2)}</pre>
      </div>

      <div className="map">
        <MapContainer
          center={[FALLBACK_CENTER.lat, FALLBACK_CENTER.lng]}
          zoom={13}
          style={{ height: "100%", width: "100%" }}
          whenCreated={(map) => {
            mapRef.current = map;
          }}
        >
          <TileLayer
            attribution='&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors &copy; <a href="https://carto.com/attributions">CARTO</a>'
            url="https://{s}.basemaps.cartocdn.com/rastertiles/voyager_nolabels/{z}/{x}/{y}{r}.png"
          />

          {pipeData.geojson && (
            <GeoJSON
              data={pipeData.geojson}
              style={() => ({
                color: "#ff00ff",
                weight: 4,
                opacity: 0.95,
                className: "pipe-glow"
              })}
              onEachFeature={(feature, layer) => {
                const p = feature?.properties || {};
                const v = toNum(p._v_half_mps);
                const vTxt = v !== null ? `${v.toFixed(2)} m/s` : "—";
                const next = Array.isArray(p._nextObjectIds) ? p._nextObjectIds.slice(0, 10).join(", ") : "—";

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
                    <div><b>Dir:</b> ${p._dir ?? "—"}</div>
                    <div><b>Next OBJECTIDs:</b> ${next}</div>
                  </div>`
                );
              }}
            />
          )}

          {showStreetRoutes &&
            points
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
                        {p.contact?.pipeObjectId !== null && p.contact?.pipeObjectId !== undefined
                          ? p.contact.pipeObjectId
                          : "—"}
                      </div>
                    </div>
                  </Popup>
                </Polyline>
              ))}

          {showPipePlans &&
            points
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
                      const startFt = startId !== null && pipeData.byObjectId ? pipeData.byObjectId.get(startId) : null;
                      const sp = startFt?.properties || {};

                      const v = typeof sp._v_half_mps === "number" ? sp._v_half_mps : parseFloat(sp._v_half_mps);
                      const vTxt = Number.isFinite(v) ? `${v.toFixed(2)} m/s` : "—";
                      const next = Array.isArray(sp._nextObjectIds) ? sp._nextObjectIds.slice(0, 10).join(", ") : "—";

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
                          <div><b>Dir:</b> {sp._dir ?? "—"}</div>
                          <div><b>Next OBJECTIDs:</b> {next}</div>                        </div>
                      );
                    })()}
                  </Popup>

                </Polyline>
              ))}


          {points.map((p) => (
            <CircleMarker
              key={p.id}
              center={[p.lat, p.lng]}
              radius={7}
              pathOptions={{
                color: "#6b1b1b",
                fillColor: "#6b1b1b",
                fillOpacity: 0.95,
                weight: 2
              }}
            >
              <Popup>
                <div>
                  <div>
                    <b>{p.name}</b>
                  </div>
                  <div>Mode: {p.mode}</div>
                  {p.mode === "pipe" && p.pipe?.speedMps !== undefined && (
                    <div>Pipe speed: {p.pipe.speedMps.toFixed(2)} m/s</div>
                  )}
                  {p.error && <div>{p.error}</div>}
                </div>
              </Popup>

              <Tooltip permanent direction="right" offset={[10, 0]} opacity={0.9}>
                {p.name}
              </Tooltip>
            </CircleMarker>
          ))}
        </MapContainer>
      </div>
    </div>
  );
}
