# Membership in static arrays with default-valued slots

`test_in_static_array.json` is a Vyper functional-test export, in the same
format as `tests/vyper-test-exports`, recorded from the pinned compiler
(`VYPER_PIN`) running `test_in_static_array.py` in Vyper's own test harness.
Its call traces therefore carry the outputs Vyper's EVM produced, which is
what the replay in `tests/vyperInStaticArrayTestScript.sml` checks the
interpreter against.

To regenerate, copy `test_in_static_array.py` into
`tests/functional/codegen/` of a Vyper checkout at `VYPER_PIN`, install it
with its `test` dependency group, and run

```sh
pytest -s -n0 --export <dir> tests/functional/codegen/test_in_static_array.py
```

The export is then `<dir>/functional/codegen/test_in_static_array.json`.
