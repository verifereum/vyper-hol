# Membership in static arrays with default-valued slots

`test_in_static_array.json` is a Vyper functional-test export, in the same
format as `tests/vyper-test-exports`, recorded from the pinned compiler
(`VYPER_PIN`, `cd74ce4f`, `vyper 0.5.0a4+cd74ce4f`) running
`test_in_static_array.py` in Vyper's own test harness.
Its call traces therefore carry the outputs Vyper's EVM produced, which is
what the replay in `tests/vyperInStaticArrayTestScript.sml` checks the
interpreter against.

To regenerate, prepare the pinned Python 3.11.17 test environment described in
the repository README, then run from the vyper-hol root:

```sh
python tools/vyper_test_exports.py generate \
  --vyper-repo vyper-src --output /tmp/in-static-array-exports \
  --fixture tests/fixtures/exports/in_static_array/test_in_static_array.py
cp /tmp/in-static-array-exports/hol_fixtures/in_static_array/test_in_static_array.json* \
  tests/fixtures/exports/in_static_array/
```

The generator temporarily copies the test into the upstream harness, uses the
semantics profile (Venom/none/Prague/revm), and removes that copy afterwards.
Commit both the JSON and its `.provenance` sidecar. The source test's hash is
also checked during replay.
