#!/usr/bin/env python3
"""
GeoJSON -> interactive SVG network map
- Alternating colours per pipe
- Small flow arrows placed along each pipe
- OBJECTID label appears on hover (no clutter)
- Infinite zoom (SVG), crisp text

Usage:
  python3 geojson_to_flow_svg.py /path/to/Sewerage_Network_Main_Pipelines.geojson output.svg
"""

import json, math, sys
from pathlib import Path

PALETTE = [
    "#1f77b4", "#ff7f0e", "#2ca02c", "#d62728",
    "#9467bd", "#8c564b", "#e377c2", "#7f7f7f",
]

def project_lonlat_to_local_m(coords_lonlat):
    """Equirectangular local projection to metres around dataset centroid."""
    lons = [p[0] for p in coords_lonlat]
    lats = [p[1] for p in coords_lonlat]
    lon0 = sum(lons) / len(lons)
    lat0 = sum(lats) / len(lats)
    lat0r = math.radians(lat0)
    R = 6371000.0

    def proj(lon, lat):
        x = math.radians(lon - lon0) * math.cos(lat0r) * R
        y = math.radians(lat - lat0) * R
        return (x, y)

    return proj, (lon0, lat0)

def lines_from_geojson(gj):
    """Yield (coords_lonlat, properties) for each feature line."""
    for feat in gj.get("features", []):
        geom = feat.get("geometry") or {}
        props = feat.get("properties") or {}
        t = geom.get("type")
        if t == "LineString":
            coords = geom.get("coordinates") or []
            if len(coords) >= 2:
                yield coords, props
        elif t == "MultiLineString":
            # Take each part as its own section (more correct than only the first)
            parts = geom.get("coordinates") or []
            for part in parts:
                if len(part) >= 2:
                    yield part, props

def polyline_length(pts):
    L = 0.0
    for i in range(1, len(pts)):
        dx = pts[i][0] - pts[i-1][0]
        dy = pts[i][1] - pts[i-1][1]
        L += math.hypot(dx, dy)
    return L

def point_and_tangent_at_fraction(pts, frac):
    """Return point (x,y) and unit tangent (tx,ty) at given fraction along polyline length."""
    total = polyline_length(pts)
    if total <= 0:
        return pts[0], (1.0, 0.0)
    target = total * frac
    acc = 0.0
    for i in range(1, len(pts)):
        x0, y0 = pts[i-1]
        x1, y1 = pts[i]
        seg = math.hypot(x1 - x0, y1 - y0)
        if seg <= 0:
            continue
        if acc + seg >= target:
            t = (target - acc) / seg
            x = x0 + (x1 - x0) * t
            y = y0 + (y1 - y0) * t
            tx = (x1 - x0) / seg
            ty = (y1 - y0) / seg
            return (x, y), (tx, ty)
        acc += seg
    # fallback end
    x0, y0 = pts[-2]
    x1, y1 = pts[-1]
    seg = math.hypot(x1 - x0, y1 - y0) or 1.0
    return (x1, y1), ((x1 - x0)/seg, (y1 - y0)/seg)

def svg_escape(s):
    return (str(s)
            .replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace('"', "&quot;")
            .replace("'", "&#39;"))

def main():
    if len(sys.argv) < 3:
        print("Usage: python3 geojson_to_flow_svg.py input.geojson output.svg", file=sys.stderr)
        sys.exit(1)

    in_path = Path(sys.argv[1])
    out_path = Path(sys.argv[2])

    gj = json.loads(in_path.read_text(encoding="utf-8"))

    # Gather all lon/lat points to build projection
    all_pts = []
    features = []
    for coords, props in lines_from_geojson(gj):
        features.append((coords, props))
        all_pts.extend(coords)

    if not all_pts:
        raise SystemExit("No LineString/MultiLineString features found.")

    proj, _ = project_lonlat_to_local_m(all_pts)

    # Project features into local metres
    projected = []
    xs, ys = [], []
    for coords, props in features:
        pts = [proj(lon, lat) for lon, lat in coords]
        projected.append((pts, props))
        for x, y in pts:
            xs.append(x); ys.append(y)

    xmin, xmax = min(xs), max(xs)
    ymin, ymax = min(ys), max(ys)

    pad = max(xmax - xmin, ymax - ymin) * 0.05 + 50  # metres padding
    xmin -= pad; xmax += pad
    ymin -= pad; ymax += pad

    width = xmax - xmin
    height = ymax - ymin

    # SVG header
    svg = []
    svg.append('<?xml version="1.0" encoding="UTF-8"?>')
    svg.append(
        f'<svg xmlns="http://www.w3.org/2000/svg" '
        f'viewBox="{xmin:.3f} {ymin:.3f} {width:.3f} {height:.3f}" '
        f'width="100%" height="100%" preserveAspectRatio="xMidYMid meet">'
    )

    # Styles: hover shows label, thicker on hover
    svg.append("""
  <style>
    .pipe { cursor: pointer; }
    .pipe-line { fill: none; stroke-width: 0.7; vector-effect: non-scaling-stroke; }
    .pipe-arrow { stroke-width: 0.45; vector-effect: non-scaling-stroke; }
    .pipe-label { font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial;
                  font-size: 6px; vector-effect: non-scaling-stroke;
                  paint-order: stroke; stroke: white; stroke-width: 2px; }
    .pipe .pipe-label { opacity: 0; }
    .pipe:hover .pipe-label { opacity: 1; }
    .pipe:hover .pipe-line { stroke-width: 1.2; }
  </style>
    """.rstrip())

    # Arrow marker uses currentColor via CSS "color:" on element
    svg.append("""
  <defs>
    <marker id="arrowHead" markerWidth="6" markerHeight="6" refX="5.2" refY="3"
            orient="auto" markerUnits="strokeWidth">
      <path d="M0,0 L6,3 L0,6 Z" fill="currentColor" />
    </marker>
  </defs>
    """.rstrip())

    # Draw each pipe
    for i, (pts, props) in enumerate(projected):
        colour = PALETTE[i % len(PALETTE)]
        oid = props.get("OBJECTID", "")
        oid_txt = svg_escape(oid)

        # Polyline points
        pts_str = " ".join(f"{x:.3f},{y:.3f}" for x, y in pts)

        # Determine how many arrows: 1 for short, up to 3 for long
        L = polyline_length(pts)
        arrow_fracs = [0.5]
        if L > 250: arrow_fracs = [0.33, 0.66]
        if L > 800: arrow_fracs = [0.25, 0.5, 0.75]

        # Label anchor at 50% and offset perpendicular (screen-space in projected metres)
        (mx, my), (tx, ty) = point_and_tangent_at_fraction(pts, 0.5)
        # Perpendicular
        nx, ny = -ty, tx
        # Alternate side to reduce local stacking; push a bit away from line
        side = 1 if (i % 2 == 0) else -1
        label_offset = 14.0  # metres
        lx = mx + nx * label_offset * side
        ly = my + ny * label_offset * side

        svg.append(f'  <g class="pipe" style="color:{colour}">')

        # Pipe line
        svg.append(f'    <polyline class="pipe-line" points="{pts_str}" stroke="{colour}" opacity="0.92" />')

        # Flow arrows: short tangential segments with arrowhead marker-end
        # Arrow segment length in metres (small, but visible due to non-scaling stroke)
        arrow_seg = 18.0
        for f in arrow_fracs:
            (ax, ay), (atx, aty) = point_and_tangent_at_fraction(pts, f)
            x0 = ax - atx * arrow_seg * 0.5
            y0 = ay - aty * arrow_seg * 0.5
            x1 = ax + atx * arrow_seg * 0.5
            y1 = ay + aty * arrow_seg * 0.5
            svg.append(
                f'    <line class="pipe-arrow" x1="{x1:.3f}" y1="{y1:.3f}" x2="{x0:.3f}" y2="{y0:.3f}" '
                f'stroke="{colour}" marker-start="url(#arrowHead)" opacity="0.9" />'
            )
            # Note: marker-start points in direction x1->x0; we want downstream (start->end).
            # Using marker-start with reversed line draws arrow pointing from x0->x1 effectively.

        # Hover label (OBJECTID)
        if oid_txt != "":
            svg.append(f'    <text class="pipe-label" x="{lx:.3f}" y="{ly:.3f}" fill="{colour}">{oid_txt}</text>')

        svg.append("  </g>")

    svg.append("</svg>")

    out_path.write_text("\n".join(svg), encoding="utf-8")
    print(f"Wrote: {out_path}")

if __name__ == "__main__":
    main()
