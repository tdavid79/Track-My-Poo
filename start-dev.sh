#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SERVER_DIR="$ROOT_DIR/server"
WEB_DIR="$ROOT_DIR/web"

if [[ ! -f "$SERVER_DIR/package.json" ]]; then
  echo "Missing server/package.json"
  exit 1
fi

if [[ ! -f "$WEB_DIR/package.json" ]]; then
  echo "Missing web/package.json"
  exit 1
fi

if [[ ! -d "$SERVER_DIR/node_modules" ]]; then
  echo "[setup] Installing server dependencies..."
  (cd "$SERVER_DIR" && npm install)
fi

if [[ ! -d "$WEB_DIR/node_modules" ]]; then
  echo "[setup] Installing web dependencies..."
  (cd "$WEB_DIR" && npm install)
fi

cleanup() {
  echo
  echo "[shutdown] Stopping services..."
  [[ -n "${SERVER_PID:-}" ]] && kill "$SERVER_PID" 2>/dev/null || true
  [[ -n "${WEB_PID:-}" ]] && kill "$WEB_PID" 2>/dev/null || true
  wait 2>/dev/null || true
}
trap cleanup EXIT INT TERM

echo "[start] Starting API server on http://localhost:8787 ..."
(cd "$SERVER_DIR" && npm run dev) &
SERVER_PID=$!

echo "[start] Starting web app on http://localhost:5173 ..."
(cd "$WEB_DIR" && VITE_API_BASE_URL="http://localhost:8787" npm run dev) &
WEB_PID=$!

echo
echo "Running:"
echo "  API: http://localhost:8787"
echo "  Web: http://localhost:5173"
echo "Press Ctrl+C to stop both."
echo

wait
