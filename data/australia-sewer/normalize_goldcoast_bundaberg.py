#!/usr/bin/env python3
import json
from pathlib import Path

import fiona
from fiona.transform import transform_geom


ROOT = Path(__file__).resolve().parent
RAW = ROOT / "raw"
OUT = ROOT / "normalized"
OUT.mkdir(parents=True, exist_ok=True)


def to_float(value):
    if value is None or value == "":
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def to_plain_geometry(geometry):
    if geometry is None:
        return None
    if hasattr(geometry, "__geo_interface__"):
        return geometry.__geo_interface__
    return geometry


def normalize_goldcoast():
    src = RAW / "goldcoast-sewer-pipes-non-pressurised.geojson"
    dst = OUT / "goldcoast-sewer-pipes-non-pressurised.normalized.geojson"

    data = json.loads(src.read_text(encoding="utf-8"))
    out_features = []
    for feat in data.get("features", []):
        props = feat.get("properties") or {}
        quality = []

        sewer_name = props.get("PIPE_NON_PRESSURE_USE") or props.get("GIS_DESCRIPTION") or "GOLD_COAST_NON_PRESSURE"
        if not props.get("PIPE_NON_PRESSURE_USE"):
            quality.append("MISSING_SEWER_NAME")

        normalized = {
            "OBJECTID": props.get("OBJECTID"),
            "SEWER_NAME": sewer_name,
            "MATERIAL": props.get("PIPE_NON_PRESSURE_MATERIAL"),
            "PIPE_LENGTH": to_float(props.get("LENGTH_M")) or to_float(props.get("Shape__Length")),
            "PIPE_WIDTH": to_float(props.get("DIAMETER_MM")),
            "PIPE_HEIGHT": 0.0,
            "GRADE": to_float(props.get("GRADE")),
            "UPSTREAM_IL": to_float(props.get("UPSTREAM_INVERT_LEVEL")),
            "DOWNSTREAM_IL": to_float(props.get("DOWNSTREAM_INVERT_LEVEL")),
            "_source": "goldcoast-sewer-pipes-non-pressurised",
            "_quality_flags": "|".join(["ZERO_HEIGHT_ASSUMED"] + quality),
        }

        out_features.append(
            {
                "type": "Feature",
                "properties": normalized,
                "geometry": to_plain_geometry(feat.get("geometry")),
            }
        )

    out = {"type": "FeatureCollection", "name": "goldcoast_sewer_non_pressure_normalized", "features": out_features}
    dst.write_text(json.dumps(out, ensure_ascii=True), encoding="utf-8")
    return len(out_features)


def normalize_bundaberg():
    gdb = RAW / "bundaberg" / "BRC_Sewerage_Network.gdb"
    dst = OUT / "bundaberg-sewerage-mains.normalized.geojson"

    out_features = []
    with fiona.open(gdb, layer="IN_Sewerage_Mains") as src:
        src_crs = src.crs_wkt or src.crs
        for feat in src:
            raw_geom = to_plain_geometry(feat.get("geometry"))
            if not raw_geom:
                continue
            props = feat.get("properties") or {}
            up_il = to_float(props.get("upstreamManholeIL"))
            down_il = to_float(props.get("downstreamManholeIL"))
            pipe_len = to_float(props.get("pipeLength")) or to_float(props.get("SHAPE_Length"))
            grade = None
            if pipe_len and pipe_len > 0 and up_il is not None and down_il is not None:
                grade = (up_il - down_il) / pipe_len

            sewer_name = (
                props.get("segmentID")
                or props.get("assetName")
                or props.get("assetClass")
                or props.get("assetType")
                or "BUNDABERG_SEWER_MAIN"
            )
            object_id = props.get("Asset_ID") or feat.get("id")

            quality_flags = ["ZERO_HEIGHT_ASSUMED"]
            if to_float(props.get("pipeDiameter")) is None and to_float(props.get("internalDiameter")) is None:
                quality_flags.append("NO_DIAMETER")
            if up_il is None or down_il is None:
                quality_flags.append("NO_INVERT_LEVELS")
            if grade is None:
                quality_flags.append("NO_GRADE")

            normalized = {
                "OBJECTID": object_id,
                "SEWER_NAME": sewer_name,
                "MATERIAL": props.get("pipeMaterial"),
                "PIPE_LENGTH": pipe_len,
                "PIPE_WIDTH": to_float(props.get("pipeDiameter")) or to_float(props.get("internalDiameter")),
                "PIPE_HEIGHT": 0.0,
                "GRADE": grade,
                "UPSTREAM_IL": up_il,
                "DOWNSTREAM_IL": down_il,
                "_source": "bundaberg-sewerage-network",
                "_quality_flags": "|".join(quality_flags),
            }

            out_features.append(
                {
                    "type": "Feature",
                    "properties": normalized,
                    "geometry": to_plain_geometry(transform_geom(src_crs, "EPSG:4326", raw_geom, antimeridian_cutting=False)),
                }
            )

    out = {"type": "FeatureCollection", "name": "bundaberg_sewer_mains_normalized", "features": out_features}
    dst.write_text(json.dumps(out, ensure_ascii=True), encoding="utf-8")
    return len(out_features)


def main():
    gc_count = normalize_goldcoast()
    brc_count = normalize_bundaberg()
    print(f"goldcoast normalized features: {gc_count}")
    print(f"bundaberg normalized features: {brc_count}")


if __name__ == "__main__":
    main()
