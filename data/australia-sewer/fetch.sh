#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RAW_DIR="$ROOT_DIR/raw"

mkdir -p "$RAW_DIR"

echo "[1/8] Fetching package manifests..."
curl -L --fail --silent --show-error \
  "https://data.gov.au/data/api/3/action/package_show?id=barwon-water-gravity-sewer-pipes" \
  -o "$RAW_DIR/barwon-water-gravity-sewer-pipes.package.json"
curl -L --fail --silent --show-error \
  "https://data.gov.au/data/api/3/action/package_show?id=chw-sewermains" \
  -o "$RAW_DIR/chw-sewermains.package.json"
curl -L --fail --silent --show-error \
  "https://data.gov.au/data/api/3/action/package_show?id=bundaberg-regional-council-sewerage-network" \
  -o "$RAW_DIR/bundaberg-sewerage-network.package.json"
curl -L --fail --silent --show-error \
  "https://data.gov.au/data/api/3/action/package_show?id=sewer-pipes-non-pressurised" \
  -o "$RAW_DIR/goldcoast-sewer-pipes-non-pressurised.package.json"
curl -L --fail --silent --show-error \
  "https://data.gov.au/data/api/3/action/package_show?id=underground-water-assets" \
  -o "$RAW_DIR/goldcoast-underground-water-assets.package.json"

echo "[2/8] Fetching Barwon Water GeoJSON..."
curl -L --fail --silent --show-error \
  "https://water-barwon.opendata.arcgis.com/api/download/v1/items/b1c3813db02f4d37a6d79d7986dbb59e/geojson?layers=4" \
  -o "$RAW_DIR/barwon-water-gravity-sewer-pipes.geojson"

echo "[3/8] Fetching Central Highlands Water GeoJSON..."
curl -L --fail --silent --show-error \
  "https://central-highlands-water-data-hub-chw.hub.arcgis.com/api/download/v1/items/9f4d0b99ed3b4184bc8a90276a7632aa/geojson?layers=0" \
  -o "$RAW_DIR/chw-sewermains.geojson"

echo "[4/8] Fetching Bundaberg package..."
curl -L --fail --silent --show-error \
  "https://data.gov.au/data/dataset/556a5b3a-5d4a-4248-8d22-cffbd326685c/resource/913257ec-9327-4e5a-900b-86bdf8e2ddd1/download/brc2020_sewerage_network.zip" \
  -o "$RAW_DIR/bundaberg-sewerage-network.zip"

echo "[5/8] Fetching Gold Coast non-pressurised sewer CSV..."
curl -L --fail --silent --show-error \
  "https://data.gov.au/data/dataset/572986be-105a-46b5-9e5f-96d6ac1ceeda/resource/3ca54619-0323-40c8-b86a-99b0fcc929e3/download/sewerpipenonpressure.csv" \
  -o "$RAW_DIR/goldcoast-sewer-pipes-non-pressurised.csv"

echo "[6/8] Attempting WA Water Corporation direct downloads (often requires SSO)..."
set +e
curl -L --silent --show-error \
  "https://data-downloads.slip.wa.gov.au/WCORP-068/GeoJSON" \
  -o "$RAW_DIR/WCORP-068.geojson"
curl -L --silent --show-error \
  "https://data-downloads.slip.wa.gov.au/WCORP-069/GeoJSON" \
  -o "$RAW_DIR/WCORP-069.geojson"
set -e

echo "[7/8] Writing quick resource index..."
ruby -rjson -e 'Dir["'"$RAW_DIR"'/*.package.json"].sort.each do |f| j=JSON.parse(File.read(f)); puts "# #{File.basename(f)}"; (j.dig("result","resources")||[]).each { |r| fmt=(r["format"]||""); name=(r["name"]||""); url=(r["url"]||""); if fmt =~ /GeoJSON|WFS|ZIP|CSV/i || name =~ /sewer/i; puts [fmt,name,url].join("\t"); end }; puts; end' \
  > "$ROOT_DIR/docs/resource-index.tsv"

echo "[8/8] Done."
echo "Raw files are in: $RAW_DIR"
