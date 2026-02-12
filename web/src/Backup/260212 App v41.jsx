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
const NODE_SNAP_TOL_M = 8;
const NODE_GAP_BRIDGE_MAX_M = 45;

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
@@ -790,50 +791,72 @@ export default function App() {
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
        const flowStartsByCell = new Map();

        function flowCellKeyFromLngLat(lng, lat, cellSizeM) {
          const m = mercatorMetersFromLngLat(lng, lat);
          return {
            key: `${Math.floor(m.x / cellSizeM)}_${Math.floor(m.y / cellSizeM)}`,
            mx: m.x,
            my: m.y
          };
        }

        function nearbyFlowCellKeys(mx, my, cellSizeM) {
          const cx = Math.floor(mx / cellSizeM);
          const cy = Math.floor(my / cellSizeM);
          const out = [];
          for (let dx = -1; dx <= 1; dx++) {
            for (let dy = -1; dy <= 1; dy++) {
              out.push(`${cx + dx}_${cy + dy}`);
            }
          }
          return out;
        }

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
@@ -869,82 +892,131 @@ export default function App() {
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

            props._flowStartLL = flowStart;
            props._flowEndLL = flowEnd;

            const upKey = nodeKeyFromLngLat(flowStart.lng, flowStart.lat, NODE_SNAP_TOL_M);
            const downKey = nodeKeyFromLngLat(flowEnd.lng, flowEnd.lat, NODE_SNAP_TOL_M);

            props._upNodeKey = upKey;
            props._downNodeKey = downKey;

            const upNode = ensureNode(upKey, flowStart.lng, flowStart.lat);
            const downNode = ensureNode(downKey, flowEnd.lng, flowEnd.lat);

            upNode.outObjectIds.push(objectId);
            downNode.inObjectIds.push(objectId);

            byObjectId.set(objectId, ft);

            const flowCell = flowCellKeyFromLngLat(flowStart.lng, flowStart.lat, NODE_GAP_BRIDGE_MAX_M);
            const arr = flowStartsByCell.get(flowCell.key) || [];
            arr.push({ objectId, lng: flowStart.lng, lat: flowStart.lat, mx: flowCell.mx, my: flowCell.my });
            flowStartsByCell.set(flowCell.key, arr);
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
          let next = Array.isArray(downNode?.outObjectIds)
            ? downNode.outObjectIds.filter((id) => id !== objectId)
            : [];

          // If strict node matching finds no continuation, bridge tiny endpoint gaps to
          // nearby downstream-start nodes so flow can continue on physically-adjacent pipes.
          if (next.length === 0 && props._flowEndLL) {
            const endPt = props._flowEndLL;
            const endM = mercatorMetersFromLngLat(endPt.lng, endPt.lat);
            const candidateIds = [];

            for (const key of nearbyFlowCellKeys(endM.x, endM.y, NODE_GAP_BRIDGE_MAX_M)) {
              const arr = flowStartsByCell.get(key);
              if (!arr) continue;

              for (const cand of arr) {
                if (cand.objectId === objectId) continue;
                const dMx = cand.mx - endM.x;
                const dMy = cand.my - endM.y;
                const dM = Math.sqrt(dMx * dMx + dMy * dMy);
                if (dM <= NODE_GAP_BRIDGE_MAX_M) {
                  candidateIds.push({ id: cand.objectId, dM });
                }
              }
            }

            if (candidateIds.length > 0) {
              const currentName = props._sewer_name_norm || "";

              let filtered = candidateIds;
              if (currentName) {
                const sameName = candidateIds.filter((cand) => {
                  const ft = byObjectId.get(cand.id);
                  const p = ft?.properties || {};
                  return (p._sewer_name_norm || "") === currentName;
                });
                if (sameName.length > 0) filtered = sameName;
              }

              filtered.sort((a, b) => a.dM - b.dM);
              next = Array.from(new Set(filtered.slice(0, 3).map((x) => x.id)));
              props._next_via_gap_bridge = true;
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