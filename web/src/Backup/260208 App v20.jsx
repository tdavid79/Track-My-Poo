import { useEffect, useMemo, useRef, useState } from "react";
import "./App.css";

import "leaflet/dist/leaflet.css";
import { MapContainer, TileLayer, GeoJSON, CircleMarker, Popup, Polyline, Tooltip, useMapEvents } from "react-leaflet";

const users = ["Tom", "Steph", "Molly", "Delilah", "Luella"];

// Fallback centre (Elsternwick-ish) if geolocation is blocked/unavailable
const FALLBACK_CENTER = { lat: -37.885, lng: 145.01 };

// Public OSRM demo server (OK for prototyping; consider self-hosting for reliability/scale)
const OSRM_ROUTE_URL = "https://router.project-osrm.org/route/v1/driving";

// Street-route travel speed (m/s) approximation for suburban catchment/house-branch drains.
// Typical self-cleansing/flow velocities are often ~0.6–1.5 m/s; we use a mid value.
const STREET_SPEED_MPS = 1.1;

// Snap tolerance (metres) when determining pipe connectivity by endpoints

// Simulation safety clamps
const PIPE_SPEED_MIN_MPS = 0.2;
const PIPE_SPEED_MAX_MPS = 3.0;


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


function chooseNextPipeWithLookahead(candidateIds, byObjectId, currProps, currId, prevId, visited) {
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

function orderedCoordsForPipe(ft) {
  return flattenFeatureCoords(ft);
}


const TARGET_PIPE_IDS = new Set([311851, 311905]); // Werribee, Peninsula

function pickCandidateOrder(candidates, byObjectId, currentFt) {
  // Preference: same SEWER_NAME, then larger pipes, then stable OBJECTID sort.
  const curP = currentFt?.properties || {};
  const curName = String(curP.SEWER_NAME || curP.SEWERNAME || "").trim();

  const scored = (candidates || []).map((id) => {
    const ft = byObjectId.get(id);
    const p = ft?.properties || {};
    const name = String(p.SEWER_NAME || p.SEWERNAME || "").trim();
    const sameName = curName && name && name === curName ? 1 : 0;

    const w = toNum(p.PIPE_WIDTH) ?? 0;
    const h = toNum(p.PIPE_HEIGHT) ?? 0;
    const area = Math.max(0, w) * Math.max(0, h);

    return { id, sameName, area };
  });

  scored.sort((a, b) => {
    if (b.sameName !== a.sameName) return b.sameName - a.sameName;
    if (b.area !== a.area) return b.area - a.area;
    return a.id - b.id;
  });

  return scored.map((s) => s.id);
}

function buildPipePlanFromObjectId(startObjectId, startPoint, byObjectId, maxSteps = 6000) {
  // Coordinate-graph traversal:
  // - For each pipe, FLOW is geometry order: first coord -> last coord.
  // - Next pipes are those whose START coord key matches current END coord key.
  // - At forks, we DFS with backtracking until we hit one of TARGET_PIPE_IDS.
  // - No NEXT OBJECTID field is trusted; `_nextObjectIds` is derived from endpoint matching.
  const plan = [];
  if (startObjectId === null || startObjectId === undefined) return plan;

  const frames = [];
  const path = [];
  const inPath = new Set();

  function getCandidates(ft, prevId) {
    const p = ft?.properties || {};
    const next = Array.isArray(p._nextObjectIds) ? p._nextObjectIds : [];
    const filtered = next.filter((id) => id !== prevId);
    return filtered;
  }

  // Seed
  let startFt = byObjectId.get(startObjectId);
  if (!startFt) return plan;

  frames.push({ id: startObjectId, prevId: null, idx: 0, ordered: null });
  path.push(startObjectId);
  inPath.add(startObjectId);

  let found = false;

  while (frames.length > 0 && path.length < maxSteps) {
    const top = frames[frames.length - 1];
    const ft = byObjectId.get(top.id);
    if (!ft) {
      // dead feature; backtrack
      frames.pop();
      inPath.delete(path.pop());
      continue;
    }

    if (TARGET_PIPE_IDS.has(top.id)) {
      found = true;
      break;
    }

    if (!top.ordered) {
      const candsRaw = getCandidates(ft, top.prevId);
      const cands = pickCandidateOrder(candsRaw, byObjectId, ft);
      top.ordered = cands;
      top.idx = 0;
    }

    if (top.idx >= top.ordered.length) {
      // backtrack
      frames.pop();
      inPath.delete(path.pop());
      continue;
    }

    const nextId = top.ordered[top.idx++];
    if (inPath.has(nextId)) continue;

    frames.push({ id: nextId, prevId: top.id, idx: 0, ordered: null });
    path.push(nextId);
    inPath.add(nextId);
  }

  // Build coordinate plan from the found path (or best-effort partial path)
  const pipeIds = path;

  const visitedCells = new Set();

  function pushPoint(pt) {
    const k = gridKey(pt, 5);
    if (visitedCells.has(k)) return;
    visitedCells.add(k);
    plan.push(pt);
  }

  for (let pi = 0; pi < pipeIds.length; pi++) {
    const id = pipeIds[pi];
    const ft = byObjectId.get(id);
    if (!ft) continue;

    const coords = orderedCoordsForPipe(ft);
    if (!coords || coords.length < 2) continue;

    if (pi === 0 && startPoint) {
      // Start at the contact point, then follow the first pipe from nearest vertex forward
      pushPoint({ lat: startPoint.lat, lng: startPoint.lng });

      let nearestIdx = 0;
      let bestDist = Infinity;
      for (let i = 0; i < coords.length; i++) {
        const d = metersBetween(startPoint, coords[i]);
        if (d < bestDist) {
          bestDist = d;
          nearestIdx = i;
        }
      }

      for (let i = nearestIdx; i < coords.length; i++) {
        const last = plan[plan.length - 1];
        if (last && metersBetween(last, coords[i]) < 0.2) continue;
        pushPoint(coords[i]);
      }
    } else {
      for (let i = 0; i < coords.length; i++) {
        const last = plan[plan.length - 1];
        if (last && metersBetween(last, coords[i]) < 0.2) continue;
        pushPoint(coords[i]);
      }
    }

    // Debug: log first ~120 hops
    if (pi < 120) {
      const p = ft.properties || {};
      const next = Array.isArray(p._nextObjectIds) ? p._nextObjectIds : [];
      console.log(
        "[PIPEHOP] " +
          id +
          " -> " +
          (pipeIds[pi + 1] ?? null) +
          ' | name="' +
          dbgName(p) +
          '" | candidates=[' +
          next.join(", ") +
          "]"
      );
    }
  }

  if (!found && pipeIds.length > 0) {
    const lastId = pipeIds[pipeIds.length - 1];
    console.warn("[PIPEPLAN] did not reach target. lastPipe=", lastId);
  }

  return plan;
}


function findNearestPipeObjectIdBySewerNameWithinMeters(geojson, pointLL, sewerNameRaw, excludeObjectId, maxMeters) {
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


export default function App() {
  const [flushes, setFlushes] = useState(0);

  const [clickToFlush, setClickToFlush] = useState(false);
  const flushCounterRef = useRef(0);

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

        
// Build a strict coordinate-connectivity graph:
// For each pipe feature, we treat geometry order as the flow direction:
//   flowStart = first coordinate, flowEnd = last coordinate.
// Then: next pipes are those whose flowStart matches current flowEnd (exact key match).
const startIndex = new Map(); // startKey -> [OBJECTID,...]
const byObjectId = new Map();

function addToIndex(key, objectId) {
  if (!key) return;
  if (!startIndex.has(key)) startIndex.set(key, []);
  startIndex.get(key).push(objectId);
}

// Pass 1: compute bbox + per-pipe velocity + START/END keys (geometry order)
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

  const coords = flattenFeatureCoords(ft);
  if (objectId === null || !coords || coords.length < 2) {
    ft.properties = props;
    continue;
  }

  // Manning velocity (half-full assumption)
  const hv = computeHalfFullVelocityMps(props);
  props._manning_n = hv.n;
  props._slope_S = hv.S;
  props._v_half_mps = hv.v;

  const sewerNameNorm = normaliseSewerName(props.SEWER_NAME || props.SEWERNAME);
  props._sewer_name_norm = sewerNameNorm;

  // Strict endpoints in geometry order (this is our flow definition)
  const flowStart = coords[0];
  const flowEnd = coords[coords.length - 1];

  const startKey = coordKeyFromLngLat(flowStart.lng, flowStart.lat, 6);
  const endKey = coordKeyFromLngLat(flowEnd.lng, flowEnd.lat, 6);

  props._startKey = startKey;
  props._endKey = endKey;

  addToIndex(startKey, objectId);
  byObjectId.set(objectId, ft);

  ft.properties = props;
}

// Pass 2: set derived next connections using strict key match
for (const [objectId, ft] of byObjectId.entries()) {
  const p = ft?.properties || {};
  const endKey = p._endKey;
  const next = endKey && startIndex.has(endKey) ? startIndex.get(endKey).filter((id) => id !== objectId) : [];
  p._nextObjectIds = next;
  ft.properties = p;
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
          nodeCount: startIndex.size,
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
  function addPointAt(lat, lng, name) {
    const id = Date.now() + Math.random();

    flushCounterRef.current += 1;
    const finalName = name && String(name).trim().length ? name : `Test ${flushCounterRef.current}`;

    setFlushes((n) => n + 1);

    setPoints((p) => [
      ...p,
      {
        id,
        name: finalName,
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

<button onClick={() => setSpeed10x((v) => !v)}>
          {speed10x ? "Speed: 10×" : "Speed: 1×"}
        </button>

        <button onClick={() => setClickToFlush((v) => !v)}>
          {clickToFlush ? "Click-to-flush: ON" : "Click-to-flush: OFF"}
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
          <ClickToAddFlush />

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
                    <div><b>Velocity (half-full):</b> ${vTxt}</div>                    <div><b>Next OBJECTIDs:</b> ${next}</div>
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
                          <div><b>Velocity (half-full):</b> {vTxt}</div>                          <div><b>Next OBJECTIDs:</b> {next}</div>
						  <div><b>Virtual next:</b> ${p._virtual_next_mode ?? "—"} ${p._virtual_next_dist_m ? `(${Number(p._virtual_next_dist_m).toFixed(1)} m)` : ""} ${p._virtual_next_radius_m ? `r=${p._virtual_next_radius_m} m` : ""}</div>
				          <div><b>Virtual next dist:</b> ${p._virtual_next_dist_m ?? "—"} m</div>



                        </div>
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
function coordKeyFromLngLat(lng, lat, decimals = 6) {
  if (typeof lng !== "number" || typeof lat !== "number") return null;
  return `${lng.toFixed(decimals)},${lat.toFixed(decimals)}`;
}


