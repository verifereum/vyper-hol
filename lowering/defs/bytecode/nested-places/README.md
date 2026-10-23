# Nested-place validation (pending external dependencies)

These twelve source inputs are regression candidates, **not verified parity
fixtures**. No oracle bytes or MATCH claims are committed. They are intentionally
separate from the frozen 101-fixture corpus.

## Opt-in driver

`holbuild nestedPlaceCapabilityTheory` checks normal subprocess availability.
`holbuild nestedPlaceValidationTheory` invokes the existing independent pinned
Vyper preparation CLI, then probes one fixture in-process with the existing HOL
checker/compiler library. It never recursively invokes holbuild. The action is
explicitly impure and is not a default root. Its declared durable output is
`nested-places/validation.tar.gz`, containing independently generated `oracle/`
and separate HOL `actual/` files. Archive presence is not parity success: inspect
every stage status and compare both deployment and runtime bytecode.

The initial run with system Python 3.12.3 failed on missing `cbor2` metadata.
The operator then verified the existing complete environment at
`/home/lukasz/.local/share/uv/tools/vyper/bin/python3`, without package changes.
The driver defaults to that explicitly authorized interpreter; override it with
`NESTED_PLACE_PYTHON` for another independently provisioned environment.
The subsequent local driver build succeeded, retained its declared archive, and
reported `ACCEPT/ACCEPT`, `SP=F`, and deployment/runtime `MATCH` for the single
`storage_struct_second_field` smoke test. This is **not** full-matrix parity or
behaviour validation. The public build log retains the per-stage statuses.

## Operator recipe

From the repository root, in an existing independently provisioned environment
whose `vyper --version` matches `VYPER_PIN` and whose Python can import and report
metadata for cbor2, immutables, lark, packaging, pycryptodome, wheel (plus py-evm,
eth-abi and eth-utils for behavioural validation):

```sh
python3 lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --corpus nested-places --repo . \
  --fixtures lowering/defs/bytecode/nested-places/oracle
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --corpus nested-places --repo . \
  --fixtures lowering/defs/bytecode/nested-places/oracle \
  --output lowering/defs/bytecode/nested-places/actual
```

The `probe` CLI is for the **external operator only** (it invokes `holbuild run`);
do not invoke it recursively from a build action. Alternatively run the opt-in
validation target with that environment on PATH. Its current single-fixture
probe is only an interface smoke test, not the full matrix.

Retain `oracle/provenance.json`, each oracle `.json` and `.hex`, and
`actual/run.json`, `probe.log`, `status.json`, `summary.txt`, `.hex`, `.term` and
`.residual` outputs where produced. Failed checker/compiler stages must remain
visible. The existing generic `execute` CLI tests unrelated tuple witnesses and
must **not** be used as nested-place behavioural evidence. C7.2 owns the required
nested-place EVM driver and the full supplied witness/control matrix, including
conditional prerequisites and transaction-boundary transient checks.
