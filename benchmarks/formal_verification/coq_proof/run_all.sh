#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/../../.." && pwd)"
cd "$ROOT"

# Activate the project venv so skydiscover-run is on PATH
source .venv/bin/activate

for bench in all_less_than insertion_sort regex_matcher; do
  echo "=== Starting $bench ==="
  skydiscover-run \
    "benchmarks/formal_verification/coq_proof/$bench/initial_program.v" \
    "benchmarks/formal_verification/coq_proof/$bench/evaluator.py" \
    --config "benchmarks/formal_verification/coq_proof/$bench/config.yaml" \
    -o "benchmarks/formal_verification/coq_proof/$bench/outputs" \
    &
done

echo "=== All three launched. Waiting... ==="
wait
echo "=== All done ==="
