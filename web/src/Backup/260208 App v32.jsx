import React, { useEffect, useMemo, useRef, useState, useCallback } from "react";
import { MapContainer, TileLayer, GeoJSON, CircleMarker, Tooltip, useMapEvents } from "react-leaflet";
import L from "leaflet";
import "leaflet/dist/leaflet.css";

/**
 * App.jsx (single-file replacement)
 *
 * Fixes included:
 * - Green path is ONLY drawn using actual GeoJSON pipe geometries (no straight-line "teleporting").
 * - Next pipe is chosen ONLY by endpoint connectivity (downstream endpoint must match another pipe's upstream endpoint).
 * - Click anywhere on the map to drop a flush (and it follows the connected pipe network).
 * - Flush speed is scaled in real time using Manning velocity for a half-full circular pipe (fallbacks if attributes missing).
 *
 * GeoJSON is loaded from GEOJSON_URL (put the file in Vite's /public folder).
 */

const GEOJSON_URL = "/pipes.geojson";

// Styles
const PIPE_STYLE = () => ({
  color: "#ff00ff",
  weight: 4,
  opacity: 0.95
});

const PATH_STYLE = () => ({
  color: "#00aa00",
  weight: 6,
  opacity: 0.95
});

// Tuning
const NODE_TOL_METERS = 2.0;       // endpoint snap for connectivity
const SNAP_TO_PIPE_METERS = 25.0;  // click snap to nearest pipe
const MAX_HOPS = 5000;             // safety
const DEFAULT_MANNING_N = 0.013;
const DEFAULT_SLOPE = 0.001;
const DEFAULT_DIAM_MM = 300;

function toNum(v) {
  if (v === null || v === undefined) return null;
  if (typeof v === "number" && Number.isFinite(v)) return v;
  const s = String(v).trim();
  if (!s) return null;
  const n = Number(s);
  return Number.isFinite(n) ? n : null;
}

function propAny(props, keys) {
  for (const k of keys) {
    if (props && Object.prototype.hasOwnProperty.call(props, k)) return props[k];
  }
  return undefined;
}

function getObjectId(props) {
  const v = propAny(props, ["OBJECTID", "ObjectID", "objectid", "OBJECT_ID", "ID"]);
  const n = toNum(v);
  return n !== null ? n : null;
}

function getSewerName(props) {
  const v = propAny(props, ["SEWER_NAME", "SEWERNAME", "NAME", "SewerName", "sewer_name", "name"]);
  return v ? String(v) : "";
}

function getSlope(props) {
  const v = propAny(props, ["GRADE", "SLOPE", "Slope", "grade", "slope"]);
  const n = toNum(v);
  if (n !== null && n > 0) return n;
  return DEFAULT_SLOPE;
}

function getUpDownIL(props) {
  const up = toNum(propAny(props, ["UP_IL", "UPSTREAM_IL", "UP_IL_M", "UpIL", "upIL", "up_il"]));
  const dn = toNum(propAny(props, ["DOWN_IL", "DOWNSTREAM_IL", "DN_IL", "DownIL", "downIL", "down_il"]));
  return { upIL: up, downIL: dn };
}

function getDiamMm(props) {
  const direct = toNum(propAny(props, ["DIAMETER_MM", "DIAM_MM", "DIAMETER", "Diameter", "diameter", "DN", "dn"]));
  if (direct !== null && direct > 0) return direct;

  const w = toNum(propAny(props, ["WIDTH_MM", "W_MM", "WIDTH", "W", "width", "w"]));
  const h = toNum(propAny(props, ["HEIGHT_MM", "H_MM", "HEIGHT", "H", "height", "h"]));
  if (w !== null && h !== null && w > 0 && h > 0) return Math.sqrt(w * h);

  const sizeStr = propAny(props, ["SIZE", "Size", "size", "DIMENSIONS", "Dimensions", "dimensions"]);
  if (sizeStr) {
    const m = String(sizeStr).match(/(\d+(?:\.\d+)?)\s*\/\s*(\d+(?:\.\d+)?)/);
    if (m) {
      const ww = Number(m[1]);
      const hh = Number(m[2]);
      if (Number.isFinite(ww) && Number.isFinite(hh) && ww > 0 && hh > 0) return Math.sqrt(ww * hh);
    }
  }

  return DEFAULT_DIAM_MM;
}

// Half-full circular Manning velocity (m/s)
function manningHalfFullVelocityMps(diamMm, slope, n = DEFAULT_MANNING_N) {
  const D = Math.max(0.05, (diamMm || DEFAULT_DIAM_MM) / 1000.0);
  const S = Math.max(1e-6, slope || DEFAULT_SLOPE);
  const nn = Math.max(0.009, n || DEFAULT_MANNING_N);
  const R = D / 4.0;
  const v = (1.0 / nn) * Math.pow(R, 2.0 / 3.0) * Math.sqrt(S);
  return Math.max(0.05, v);
}

function ensureLatLng(lat, lng) {
  return L.latLng(lat, lng);
}

function geometryToPolylines(geom) {
  if (!geom) return [];
  if (geom.type === "LineString") {
    return [geom.coordinates.map((c) => ensureLatLng(c[1], c[0]))];
  }
  if (geom.type === "MultiLineString") {
    return geom.coordinates.map((line) => line.map((c) => ensureLatLng(c[1], c[0])));
  }
  return [];
}

// ---- Connectivity index (endpoint clustering within NODE_TOL_METERS) ----

function makeNodeIndex() {
  // Cluster endpoints in projected (EPSG:3857) metres.
  // This avoids long-distance merges caused by lat/long bucketing quirks.
  return { buckets: new Map(), nextId: 1 };
}

function projectMeters(ll) {
  const p = L.CRS.EPSG3857.project(L.latLng(ll[0], ll[1]));
  return [p.x, p.y];
}

function bucketKeyProjected(ll, tolM) {
  const [x, y] = projectMeters(ll);
  const bx = Math.round(x / tolM);
  const by = Math.round(y / tolM);
  return `${bx},${by}`;
}

function distMetersProjected(a, b) {
  const [ax, ay] = projectMeters(a);
  const [bx, by] = projectMeters(b);
  return Math.hypot(ax - bx, ay - by);
}

function getBucket(index, key) {
  let arr = index.buckets.get(key);
  if (!arr) {
    arr = [];
    index.buckets.set(key, arr);
  }
  return arr;
}

function nodeIdFor(ll, index, tolM) {
  const key = bucketKeyProjected(ll, tolM);
  const arr = getBucket(index, key);

  for (const n of arr) {
    if (distMetersProjected(n.ll, ll) <= tolM) return n.id;
  }

  const id = `N${index.nextId++}`;
  arr.push({ id, ll });
  return id;
}

function buildPipeRecords(geojson) {
  const nodeIndex = makeNodeIndex();
  const pipes = [];

  const features = geojson?.features || [];
  for (const f of features) {
    const polylines = geometryToPolylines(f.geometry);
    if (!polylines.length) continue;

    const props = f.properties || {};
    const objectId = getObjectId(props);
    const name = getSewerName(props);
    const slope = getSlope(props);
    const diamMm = getDiamMm(props);
    const { upIL, downIL } = getUpDownIL(props);

    for (let partIndex = 0; partIndex < polylines.length; partIndex += 1) {
      const latlngs = polylines[partIndex];
      if (!latlngs || latlngs.length < 2) continue;

      let oriented = latlngs;

      // Heuristic: ensure upstream IL is numerically higher than downstream IL; if not, flip geometry.
      // (e.g. -3.53 is "higher" than -3.77)
      if (upIL !== null && downIL !== null && upIL < downIL) {
        oriented = [...latlngs].reverse();
      }

      const up = oriented[0];
      const dn = oriented[oriented.length - 1];

      const upNode = nodeIdFor(up, nodeIndex, NODE_TOL_METERS);
      const dnNode = nodeIdFor(dn, nodeIndex, NODE_TOL_METERS);

      pipes.push({
        feature: f,
        objectId,
        name,
        slope,
        diamMm,
        upIL,
        downIL,
        partIndex,
        latlngs: oriented,
        upNode,
        dnNode
      });
    }
  }

  // adjacency: node -> outgoing pipes (flow direction)
  const outByNode = new Map();
  for (const p of pipes) {
    if (!outByNode.has(p.upNode)) outByNode.set(p.upNode, []);
    outByNode.get(p.upNode).push(p);
  }

  return { pipes, outByNode };
}

function chooseNextPipe(current, candidates) {
  if (!candidates || !candidates.length) return null;

  // Avoid immediate self loop
  const filtered = candidates.filter((c) => !(c.objectId === current.objectId && c.partIndex === current.partIndex));
  const pool = filtered.length ? filtered : candidates;

  // Prefer same sewer name
  const sameName = pool.filter((c) => c.name && current.name && c.name === current.name);
  const primary = sameName.length ? sameName : pool;

  // Score by similarity (keeps trunk continuity when multiple joins exist)
  let best = primary[0];
  let bestScore = Infinity;

  for (const c of primary) {
    const ds = Math.abs((c.slope || DEFAULT_SLOPE) - (current.slope || DEFAULT_SLOPE));
    const dd = Math.abs((c.diamMm || DEFAULT_DIAM_MM) - (current.diamMm || DEFAULT_DIAM_MM));
    const score = ds * 1000 + dd * 0.001;
    if (score < bestScore) {
      best = c;
      bestScore = score;
    }
  }

  return best;
}

function buildDownstreamPath(startPipe, outByNode) {
  const path = [];
  const seen = new Set();

  let cur = startPipe;
  let hops = 0;

  while (cur && hops < MAX_HOPS) {
    const key = `${cur.objectId ?? "null"}:${cur.partIndex}:${cur.upNode}:${cur.dnNode}`;
    if (seen.has(key)) break;
    seen.add(key);

    path.push(cur);

    const candidates = outByNode.get(cur.dnNode) || [];
    cur = chooseNextPipe(cur, candidates);
    hops += 1;
  }

  return path;
}

// ---- Click-to-pipe snapping (no skipping across land) ----

function pointToSegmentPixels(p, a, b) {
  const x = p.x, y = p.y;
  const x1 = a.x, y1 = a.y;
  const x2 = b.x, y2 = b.y;

  const dx = x2 - x1;
  const dy = y2 - y1;

  if (dx === 0 && dy === 0) {
    const ddx = x - x1;
    const ddy = y - y1;
    return Math.sqrt(ddx * ddx + ddy * ddy);
  }

  const t = ((x - x1) * dx + (y - y1) * dy) / (dx * dx + dy * dy);
  const tt = Math.max(0, Math.min(1, t));
  const projx = x1 + tt * dx;
  const projy = y1 + tt * dy;

  const ddx = x - projx;
  const ddy = y - projy;
  return Math.sqrt(ddx * ddx + ddy * ddy);
}

function pointToPolylineMeters(map, latlng, latlngs) {
  const p = map.latLngToLayerPoint(latlng);
  let min = Infinity;

  for (let i = 0; i < latlngs.length - 1; i += 1) {
    const a = map.latLngToLayerPoint(latlngs[i]);
    const b = map.latLngToLayerPoint(latlngs[i + 1]);
    const d = pointToSegmentPixels(p, a, b);
    if (d < min) min = d;
  }

  if (!Number.isFinite(min)) return Infinity;

  // Approx convert px->m at current view
  const p1 = map.layerPointToLatLng(L.point(0, 0));
  const p2 = map.layerPointToLatLng(L.point(1, 0));
  const metersPerPixel = p1.distanceTo(p2);

  return min * metersPerPixel;
}

function findNearestPipe(map, latlng, pipes) {
  let best = null;
  let bestDist = Infinity;

  for (const p of pipes) {
    const d = pointToPolylineMeters(map, latlng, p.latlngs);
    if (d < bestDist) {
      bestDist = d;
      best = p;
    }
  }

  if (best && bestDist <= SNAP_TO_PIPE_METERS) return { pipe: best, distM: bestDist };
  return { pipe: null, distM: Infinity };
}

function projectPointToSegment(p, a, b) {
  const x = p.x, y = p.y;
  const x1 = a.x, y1 = a.y;
  const x2 = b.x, y2 = b.y;

  const dx = x2 - x1;
  const dy = y2 - y1;

  if (dx === 0 && dy === 0) return { x: x1, y: y1, t: 0 };

  const t = ((x - x1) * dx + (y - y1) * dy) / (dx * dx + dy * dy);
  const tt = Math.max(0, Math.min(1, t));
  return { x: x1 + tt * dx, y: y1 + tt * dy, t: tt };
}

function nearestPointOnPolyline(map, latlng, latlngs) {
  const p = map.latLngToLayerPoint(latlng);

  let best = null;
  let bestPix = Infinity;
  let bestIndex = 0;
  let bestT = 0;

  for (let i = 0; i < latlngs.length - 1; i += 1) {
    const a = map.latLngToLayerPoint(latlngs[i]);
    const b = map.latLngToLayerPoint(latlngs[i + 1]);

    const proj = projectPointToSegment(p, a, b);
    const dx = p.x - proj.x;
    const dy = p.y - proj.y;
    const d = Math.sqrt(dx * dx + dy * dy);

    if (d < bestPix) {
      bestPix = d;
      best = proj;
      bestIndex = i;
      bestT = proj.t;
    }
  }

  if (!best) return null;

  let alongM = 0;
  for (let i = 0; i < bestIndex; i += 1) alongM += latlngs[i].distanceTo(latlngs[i + 1]);
  const segLenM = latlngs[bestIndex].distanceTo(latlngs[bestIndex + 1]);
  alongM += segLenM * bestT;

  return { alongM };
}

// ---- Flush animation (real-time scaled speed) ----

function polylineLengthM(latlngs) {
  let total = 0;
  for (let i = 0; i < latlngs.length - 1; i += 1) total += latlngs[i].distanceTo(latlngs[i + 1]);
  return total;
}

function latlngAtAlong(latlngs, alongM) {
  let remaining = Math.max(0, alongM);

  for (let i = 0; i < latlngs.length - 1; i += 1) {
    const a = latlngs[i];
    const b = latlngs[i + 1];
    const seg = a.distanceTo(b);

    if (seg <= 0) continue;

    if (remaining <= seg) {
      const t = remaining / seg;
      return ensureLatLng(a.lat + (b.lat - a.lat) * t, a.lng + (b.lng - a.lng) * t);
    }

    remaining -= seg;
  }

  return latlngs[latlngs.length - 1];
}

function useFlushAnimation(map, path, startAlongM) {
  const [flushPos, setFlushPos] = useState(null);
  const [debug, setDebug] = useState(null);

  const animRef = useRef({
    running: false,
    raf: 0,
    lastTs: 0,
    pipeIndex: 0,
    alongM: 0
  });

  const stop = useCallback(() => {
    const a = animRef.current;
    if (a.raf) cancelAnimationFrame(a.raf);
    a.running = false;
    a.raf = 0;
    a.lastTs = 0;
  }, []);

  useEffect(() => {
    stop();
    setFlushPos(null);
    setDebug(null);

    if (!map || !path || !path.length) return;

    const a = animRef.current;
    a.running = true;
    a.lastTs = 0;
    a.pipeIndex = 0;
    a.alongM = Math.max(0, startAlongM || 0);

    const step = (ts) => {
      if (!a.running) return;
      if (!a.lastTs) a.lastTs = ts;

      const dt = (ts - a.lastTs) / 1000.0;
      a.lastTs = ts;

      let idx = a.pipeIndex;
      let along = a.alongM;

      const curPipe = path[idx];
      const v = manningHalfFullVelocityMps(curPipe.diamMm, curPipe.slope, DEFAULT_MANNING_N);

      along += v * dt;

      // Advance across pipe boundaries using real pipe lengths
      while (idx < path.length) {
        const len = polylineLengthM(path[idx].latlngs);
        if (along <= len) break;
        along -= len;
        idx += 1;
      }

      // End
      if (idx >= path.length) {
        const last = path[path.length - 1];
        setFlushPos(last.latlngs[last.latlngs.length - 1]);
        setDebug({
          done: true,
          objectId: last.objectId,
          v,
          pipeIndex: path.length - 1
        });
        stop();
        return;
      }

      a.pipeIndex = idx;
      a.alongM = along;

      const p = path[idx];
      setFlushPos(latlngAtAlong(p.latlngs, along));
      setDebug({
        done: false,
        objectId: p.objectId,
        v,
        pipeIndex: idx
      });

      a.raf = requestAnimationFrame(step);
    };

    a.raf = requestAnimationFrame(step);

    return () => stop();
  }, [map, path, startAlongM, stop]);

  return { flushPos, debug };
}

// ---- Click handler ----

function MapClickHandler({ onClickLatLng }) {
  useMapEvents({
    click(e) {
      onClickLatLng(e.latlng);
    }
  });
  return null;
}

export default function App() {
  const [geojson, setGeojson] = useState(null);
  const [loadErr, setLoadErr] = useState("");
  const [map, setMap] = useState(null);

  const [selectedPipe, setSelectedPipe] = useState(null);
  const [path, setPath] = useState([]);
  const [clickLatLng, setClickLatLng] = useState(null);
  const [startAlongM, setStartAlongM] = useState(0);

  useEffect(() => {
    let cancelled = false;

    fetch(GEOJSON_URL)
      .then((r) => {
        if (!r.ok) throw new Error(`HTTP ${r.status}`);
        return r.json();
      })
      .then((j) => {
        if (cancelled) return;
        setGeojson(j);
        setLoadErr("");
      })
      .catch((e) => {
        if (cancelled) return;
        setLoadErr(String(e?.message || e));
      });

    return () => {
      cancelled = true;
    };
  }, []);

  const net = useMemo(() => {
    if (!geojson) return null;
    return buildPipeRecords(geojson);
  }, [geojson]);

  const pathGeoJson = useMemo(() => {
    if (!path || !path.length) return null;

    return {
      type: "FeatureCollection",
      features: path.map((p) => ({
        type: "Feature",
        properties: {
          OBJECTID: p.objectId,
          NAME: p.name,
          partIndex: p.partIndex
        },
        geometry: {
          type: "LineString",
          coordinates: p.latlngs.map((ll) => [ll.lng, ll.lat])
        }
      }))
    };
  }, [path]);

  const handleMapClick = useCallback(
    (latlng) => {
      if (!map || !net) return;

      // Restore: click anywhere to drop a flush
      setClickLatLng(latlng);

      // Snap click to nearest pipe (or do nothing if too far)
      const { pipe } = findNearestPipe(map, latlng, net.pipes);
      if (!pipe) {
        setSelectedPipe(null);
        setPath([]);
        return;
      }

      const np = nearestPointOnPolyline(map, latlng, pipe.latlngs);

      setSelectedPipe(pipe);

      // IMPORTANT: downstream path built ONLY via endpoint connectivity
      const pth = buildDownstreamPath(pipe, net.outByNode);
      setPath(pth);

      // Start flush at nearest location along first pipe
      setStartAlongM(np ? np.alongM : 0);
    },
    [map, net]
  );

  const { flushPos, debug } = useFlushAnimation(map, path, startAlongM);

  const initialCenter = useMemo(() => {
    if (!geojson?.features?.length) return [-37.81, 144.96];
    const f = geojson.features[0];
    const lines = geometryToPolylines(f.geometry);
    if (lines.length && lines[0].length) return [lines[0][0].lat, lines[0][0].lng];
    return [-37.81, 144.96];
  }, [geojson]);

  return (
    <div style={{ height: "100vh", width: "100vw" }}>
      <MapContainer
        center={initialCenter}
        zoom={11}
        style={{ height: "100%", width: "100%" }}
        whenCreated={setMap}
      >
        <TileLayer
          attribution="&copy; OpenStreetMap contributors"
          url="https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png"
        />

        <MapClickHandler onClickLatLng={handleMapClick} />

        {geojson && (
          <GeoJSON
            data={geojson}
            style={PIPE_STYLE}
            onEachFeature={(feature, layer) => {
              layer.on("click", (e) => handleMapClick(e.latlng));

              const props = feature.properties || {};
              const objectId = getObjectId(props);
              const name = getSewerName(props);
              const slope = getSlope(props);
              const diamMm = getDiamMm(props);
              const { upIL, downIL } = getUpDownIL(props);

              const popupLines = [
                `OBJECTID: ${objectId ?? "—"}`,
                `SEWER_NAME: ${name || "—"}`,
                `Diam (mm): ${Math.round(diamMm)}`,
                `Slope: ${slope}`,
                `Up IL / Down IL: ${upIL ?? "—"} / ${downIL ?? "—"}`,
                `Half-full v (m/s): ${manningHalfFullVelocityMps(diamMm, slope).toFixed(2)}`
              ];

              layer.bindPopup(popupLines.join("<br/>"));
            }}
          />
        )}

        {/* Green path overlays ONLY the existing pipe geometries */}
        {pathGeoJson && (
          <GeoJSON
            data={pathGeoJson}
            style={PATH_STYLE}
          />
        )}

        {/* Flush marker */}
        {flushPos && (
          <CircleMarker center={flushPos} radius={7}>
            <Tooltip direction="top" offset={[0, -8]} opacity={0.95} permanent>
              {debug?.done
                ? `Flush done (OBJECTID ${debug?.objectId ?? "—"})`
                : `Flush (OBJECTID ${debug?.objectId ?? "—"}) v=${debug?.v?.toFixed?.(2) ?? "—"} m/s`}
            </Tooltip>
          </CircleMarker>
        )}

        {/* Click marker */}
        {clickLatLng && (
          <CircleMarker center={clickLatLng} radius={5}>
            <Tooltip direction="top" offset={[0, -8]} opacity={0.95}>
              Click
            </Tooltip>
          </CircleMarker>
        )}
      </MapContainer>

      {(loadErr || !geojson) && (
        <div
          style={{
            position: "absolute",
            left: 12,
            bottom: 12,
            background: "rgba(255,255,255,0.92)",
            padding: "10px 12px",
            borderRadius: 8,
            fontFamily: "system-ui, -apple-system, Segoe UI, Roboto, sans-serif",
            fontSize: 13,
            lineHeight: 1.35,
            maxWidth: 520
          }}
        >
          {loadErr ? (
            <div>
              <div style={{ fontWeight: 700, marginBottom: 6 }}>GeoJSON load error</div>
              <div>{loadErr}</div>
              <div style={{ marginTop: 6 }}>
                Expected <code>{GEOJSON_URL}</code> to be served by Vite (place file in <code>public/</code>).
              </div>
            </div>
          ) : (
            <div>Loading GeoJSON…</div>
          )}
        </div>
      )}
    </div>
  );
}
