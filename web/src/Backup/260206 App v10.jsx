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
const NODE_SNAP_TOL_M = 1;

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

  // 1) Prefer lowest downstream IL if available (only when DIR isn't explicitly provided).
  // Pump stations can legitimately go uphill, so IL is not a reliable tie-breaker when DIR exists.
  const currDirSource = String(currentProps?._dir_source || "");
  const anyDirProvided = candidateIds.some((id) => String(byObjectId.get(id)?.properties?._dir_source || "") === "DIR");

  if (currDirSource !== "DIR" && !anyDirProvided) {
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
  }

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

  // If the dataset provides explicit DIR, we must follow connectivity rather than
  // enforcing "downhill" by IL (pump stations can legitimately go uphill).
  // Only apply IL-based "downhill" heuristics when DIR was not provided.
  const currDown = toNum(currProps?.DOWNSTREAM_IL);
  const currDirSource = String(currProps?._dir_source || "");
  if (currDirSource !== "DIR" && currDown !== null) {
    const tol = 0.05; // metres
    const downhill = ids.filter((id) => {
      const ft = byObjectId.get(id);
      const d = toNum(ft?.properties?.DOWNSTREAM_IL);
      return d === null ? true : d <= currDown + tol;
    });
    if (downhill.length > 0 && downhill.length < ids.length) {
      // Only apply this filter if it actually removes some uphill options
      if (downhill.length === 1) return downhill[0];
      return chooseBestByLookahead(downhill, byObjectId, currProps, currId, prevId, visited);
    }
  }

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

  const useILHeuristics = String(currProps?._dir_source || "") !== "DIR";
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

    if (useILHeuristics) {
      if (lastDown !== null && d !== null) {
        const delta = d - lastDown; // negative is downhill (good)
        if (delta > 0.05) total += 1000 + delta * 200; // big penalty for uphill
        else total += delta * 10; // reward downhill (more negative)
      } else {
        // If no IL data, slightly penalise uncertainty
        total += 5;
      }
      lastDown = d !== null ? d : lastDown;
    } else {
      // DIR-driven traversal: don't score by IL (pump stations can go uphill).
      // Small constant to avoid preferring unknowns too strongly.
      total += 1;
    }

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

function findNearestObjectIdBySewerNameFromByObjectId(byObjectId, pointLL, sewerNameRaw, excludeIds, maxMeters) {
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


function buildPipePlanFromObjectId(startObjectId, startPoint, byObjectId, maxHops = 2000) {
  const plan = [];
  const visited = new Set();
  const visitedCells = new Set();


  let currentId = startObjectId;
  let first = true;
  let prevId = null;


  while (currentId !== null && !visited.has(currentId) && visited.size < maxHops) {
    visited.add(currentId);

    const ft = byObjectId.get(currentId);
    if (!ft) break;

    const p = ft.properties || {};
    const coords = flattenFeatureCoords(ft);

    if (coords.length < 2) break;

    // Enforce upstream->downstream coordinate order
    // If we computed _dir as d_to_u, reverse so plan always follows downstream direction.
    const dir = String(p._dir || "u_to_d");
    const ordered = dir === "d_to_u" ? coords.slice().reverse() : coords;

    if (first && startPoint) {
      // Insert the actual snap point, then continue from nearest index onward
      plan.push({ lng: startPoint.lng, lat: startPoint.lat });

      let nearestIdx = 0;
      let bestDist = Infinity;
      for (let i = 0; i < ordered.length; i++) {
        const d = metersBetween(startPoint, ordered[i]);
        if (d < bestDist) {
          bestDist = d;
          nearestIdx = i;
        }
      }

		for (let i = nearestIdx; i < ordered.length; i++) {
		  const k = gridKey(ordered[i], 5); // 5m cells
		  if (visitedCells.has(k)) continue;
		  visitedCells.add(k);
		  plan.push(ordered[i]);
		}

      first = false;
    } else {
      // Avoid duplicating the node at joins
      const last = plan[plan.length - 1];
      for (let i = 0; i < ordered.length; i++) {
        const pt = ordered[i];
        if (last && metersBetween(last, pt) < 0.2) continue;
		const k = gridKey(pt, 5);
		if (!visitedCells.has(k)) {
		  visitedCells.add(k);
		  plan.push(pt);
		}

      }
    }

    const nextIds = Array.isArray(p._nextObjectIds) ? p._nextObjectIds : [];
    let nextId = chooseNextPipeWithLookahead(nextIds, byObjectId, p, currentId, prevId, visited);

    // If chosen next is already visited, try an unvisited alternative from nextIds
    if (nextId !== null && visited.has(nextId)) {
      const altIds = nextIds.filter((id) => !visited.has(id));
      const alt = chooseNextPipeLowestDownIL(altIds, byObjectId, p);
      if (alt !== null) nextId = alt;
    }

    // If we still have no unvisited way forward, do a runtime "same SEWER_NAME" jump near downstream end
    if (nextId !== null && visited.has(nextId)) {
      const sewerName = p.SEWER_NAME || p.SEWERNAME;
      const endPt = ordered[ordered.length - 1];
      const exclude = new Set(Array.from(visited));
      exclude.add(currentId);

      const hit = findNearestObjectIdBySewerNameFromByObjectId(byObjectId, endPt, sewerName, exclude, 8000);
      if (hit) nextId = hit.objectId;
    }




	if (visited.size < 50) {
	  const currName = dbgName(p);
	  const currDown = toNum(p.DOWNSTREAM_IL);
	  const cand = nextIds.join(", ");

	  const ftNext = nextId !== null ? byObjectId.get(nextId) : null;
	  const pNext = ftNext?.properties || {};
	  const nextName = dbgName(pNext);
	  const nextDown = toNum(pNext.DOWNSTREAM_IL);

      console.log(
        "[PIPEHOP] " +
          currentId +
          " -> " +
          nextId +
          ' | name="' +
          currName +
          '" -> "' +
          nextName +
          '" | downIL=' +
          currDown +
          " -> " +
          nextDown +
          " | candidates=[" +
          cand +
          "] | nextLoaded=" +
          (!!ftNext)
      );

	}	

    prevId = currentId;
    currentId = nextId;

  }

  return plan;
}

function findNearestNodeKeyWithinMeters(nodeIndex, fromKey, maxMeters) {
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

function findNearestPipeObjectIdToPointWithinMeters(geojson, pointLL, excludeObjectId, maxMeters) {
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

        // Pass 1: compute bbox + per-pipe velocity + direction + endpoint node keys
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

          // Determine start/end coords for this feature
          let start = null;
          let end = null;

          if (g.type === "LineString") {
            const coords = g.coordinates || [];
            if (coords.length >= 2) {
              start = coords[0];
              end = coords[coords.length - 1];
            }
          } else if (g.type === "MultiLineString") {
            const lines = g.coordinates || [];
            if (lines.length > 0) {
              const first = lines[0] || [];
              const last = lines[lines.length - 1] || [];
              if (first.length >= 1 && last.length >= 1) {
                start = first[0];
                end = last[last.length - 1];
              }
            }
          }

          // Compute Manning velocity (half-full assumption)
          const hv = computeHalfFullVelocityMps(props);
          props._manning_n = hv.n;
          props._slope_S = hv.S;
          props._v_half_mps = hv.v;

          // Determine direction.
          // Priority:
          //   1) Explicit DIR field in the dataset (u_to_d / d_to_u)
          //   2) Fallback: infer from ILs (UPSTREAM_IL vs DOWNSTREAM_IL)
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

          if (start && end) {
            const startLL = { lng: start[0], lat: start[1] };
            const endLL = { lng: end[0], lat: end[1] };

            // If dir is d_to_u, swap so upLL/downLL align to IL direction
            const upLL = dir === "u_to_d" ? startLL : endLL;
            const downLL = dir === "u_to_d" ? endLL : startLL;

            const upKey = nodeKeyFromLngLat(upLL.lng, upLL.lat, NODE_SNAP_TOL_M);
            const downKey = nodeKeyFromLngLat(downLL.lng, downLL.lat, NODE_SNAP_TOL_M);

            props._dir = dir;
            props._dir_source = dirSource;
            props._upNodeKey = upKey;
            props._downNodeKey = downKey;

            if (objectId !== null) {
              const upNode = ensureNode(upKey, upLL.lng, upLL.lat);
              const downNode = ensureNode(downKey, downLL.lng, downLL.lat);

              upNode.outObjectIds.push(objectId);
              downNode.inObjectIds.push(objectId);

              byObjectId.set(objectId, ft);
            }
          }

          ft.properties = props;
        }

        // Pass 2: compute next connections for each pipe
        for (const ft of features) {
          const props = ft?.properties || {};
          const objectId = toNum(props.OBJECTID);
          const downKey = props._downNodeKey;

          if (objectId === null || !downKey) continue;

		  const downNode = nodeIndex.get(downKey);

		  let next = Array.isArray(downNode?.outObjectIds)
			? downNode.outObjectIds.filter((id) => id !== objectId)
			: [];
	  
      // --- Minimal next step: consider nearby segment only if it truly touches ---
      {
        const downNodeLL = nodeIndex.get(downKey);

        if (downNodeLL) {
          const hit = findNearestPipeObjectIdToPointWithinMeters(
            gj,
            { lat: downNodeLL.lat, lng: downNodeLL.lng },
            objectId,
            25
          );

          if (hit && hit.objectId && hit.dist <= 25) {
            if (!next.includes(hit.objectId)) {
              next = [...next, hit.objectId];
            }
            props._segment_candidate_objectid = hit.objectId;
            props._segment_candidate_dist_m = hit.dist;
            props._segment_candidate_used = true;
          }
        }
      }
	  
	  
	  
		  // --- Virtual connector: if no outgoing pipe, jump to nearest endpoint within 10 m ---
		if (next.length === 0) {
		  const radii = [5, 25, 100, 500];

		  for (const r of radii) {
			const nearKey = findNearestNodeKeyWithinMeters(nodeIndex, downKey, r);
			if (!nearKey) continue;

			const nearNode = nodeIndex.get(nearKey);
			const nearNext = Array.isArray(nearNode?.outObjectIds) ? nearNode.outObjectIds : [];

			const candidates = nearNext.filter((id) => id !== objectId);
			if (candidates.length > 0) {
			  next = candidates;
			  props._virtual_next_from_node = nearKey;
			  props._virtual_next_radius_m = r;
			  break;
			}
		  }
		}

      // --- Pump-station connector: ALWAYS add nearest pipe with same SEWER_NAME as an extra candidate ---
      {
        const downNodeLL = nodeIndex.get(downKey);
        const sewerName = props.SEWER_NAME || props.SEWERNAME;

        if (downNodeLL && sewerName) {
          const radiiByName = [50, 200, 500, 1500, 5000];

          for (const r of radiiByName) {
            const hit = findNearestPipeObjectIdBySewerNameWithinMeters(
              gj,
              { lat: downNodeLL.lat, lng: downNodeLL.lng },
              sewerName,
              objectId,
              r
            );

            if (hit) {
              // Add as an additional candidate (don't overwrite existing next[])
              if (!next.includes(hit.objectId)) {
                next = [...next, hit.objectId];
              }
              props._virtual_next_objectid = hit.objectId;
              props._virtual_next_dist_m = hit.dist;
              props._virtual_next_mode = "sewer_name";
              props._virtual_next_radius_m = r;
              break;
            }
          }
        }
      }

	  
	  
	  
      // --- Segment connector: if still no outgoing pipe, snap to nearest pipe SEGMENT ---
      if (next.length === 0) {
        const downNodeLL = nodeIndex.get(downKey);

        if (downNodeLL) {
          const segRadii = [250, 1000, 3000, 8000];

          for (const r of segRadii) {
            const hit = findNearestPipeObjectIdToPointWithinMeters(
              gj,
              { lat: downNodeLL.lat, lng: downNodeLL.lng },
              objectId,
              r
            );

            if (hit) {
              next = [hit.objectId];
              props._virtual_next_objectid = hit.objectId;
              props._virtual_next_dist_m = hit.dist;
              props._virtual_next_mode = "segment";
              props._virtual_next_radius_m = r;
              break;
            }
          }
        }
      }


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
                          <div><b>Next OBJECTIDs:</b> {next}</div>
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
