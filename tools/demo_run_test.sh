#!/bin/sh
# Build once, then exercise the JSON-facing runner without exposing CV trees.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

# Requires holbuild, MLton, and Python 3 on PATH. Also checks native/HOL parity.
python3 tools/emit_run_test.py --smoke
runner="$root/tests/.emit/run-test"
fixture="$root/tests/fixtures/run_test_json/basic.json"

printf '\nRun the exported JSON fixture (three passes, two intentional failures):\n'
status=0
"$runner" "$fixture" || status=$?
if [ "$status" -ne 1 ]; then
    printf 'Expected fixture exit status 1; got %s\n' "$status" >&2
    exit 1
fi

printf '\nRun just the passing deployment/call case through stdin:\n'
# Exported files contain named tests and fixtures. A trace array is also accepted.
# Include the setup deployment before the call that depends on it.
python3 - "$fixture" <<'PY' | "$runner"
import json
import sys

with open(sys.argv[1]) as source:
    cases = json.load(source)
traces = cases["setup"]["traces"] + cases["test_basic_code"]["traces"]
json.dump(traces, sys.stdout)
PY

printf '\nDemo complete. Run your own export with:\n  %s path/to/export.json\n' "$runner"
