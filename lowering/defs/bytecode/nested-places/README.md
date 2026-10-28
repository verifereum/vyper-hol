# Nested-place regression sources

`sources/` contains the nested subscript, struct-field, HashMap and transient
storage witnesses for issue #558. `parity-fixtures.txt` lists the twelve
requested fixture families. These inputs are separate from the existing
101-fixture bytecode corpus.

The existing witness tool can prepare independent oracle inputs and probe the
HOL compiler. Run from the repository root with the pinned Vyper from
`VYPER_PIN` on PATH:

```sh
python3 lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --corpus nested-places --repo . \
  --fixtures lowering/defs/bytecode/nested-places/oracle
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --corpus nested-places --repo . \
  --fixtures lowering/defs/bytecode/nested-places/oracle \
  --output lowering/defs/bytecode/nested-places/actual
```

Use `--only SOURCE_STEM` with `probe` to select a witness. Inspect the generated
`actual/summary.txt` and `actual/status.json`: successful tool execution does
not imply that every witness matches. Oracle inputs and probe results are
local generated artifacts, not checked-in validation evidence.

Some witnesses also exercise independent features: For/Append/Pop (#559),
aggregate copies (#560), immutable aggregates (#563), internal struct returns
(#545), and nested tuples (#571). Keeping their sources does not assert that
those dependencies are implemented here.
