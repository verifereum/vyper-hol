# Memory-store witnesses

These sources exercise memory copies, empty initializers, tuple unpacking and
assertion reasons. `parity-fixtures.txt` selects 28 exact bytecode comparisons;
the other sources retain the remaining issue witnesses and cross-area controls
for diagnostic comparison.
The existing 101-fixture corpus is unchanged.

`oracle/` contains independently generated annotated AST/layout JSON and
deployment/runtime bytecode. Its provenance records the pinned compiler,
settings, dependencies and input/output hashes. Use the isolated Python 3.11.11
Vyper installation described in the parent bytecode README, with `VYPER_PIN`
and `python-o1-oracle-constraints.txt`, to reproduce these files. From the
repository root, with that environment first on `PATH`:

```sh
python lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --fixtures /tmp/memory-store-oracle --check
holbuild -j8 build evalCompilerMemoryStoresTheory
```

The HOL theory checks the exported contract in deployment and runtime modes,
then evaluates `compile_vyper (K SOME) (o1_policy all_capabilities)`. The oracle
appears only in the final equality. Standard finite-map and byte-word evaluation
rules are used; no compiler-specific evaluator substitution is installed.
The theory is included in the default lowering rollup.

For a diagnostic report covering every source, run this from the worktree being
tested. The 900-second per-source limit bounds diagnostics; it does not change
the project's proof-step timeout:

```sh
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --fixtures /tmp/memory-store-oracle --output /tmp/memory-store-hol
```

The output directory retains checker outcomes, whitelist membership, compiler
results, bytecode and first runtime-byte differences. `--only NAME` selects a
source and may be repeated. To execute the two tuple-unpacking witnesses in an
independent Prague EVM, using the oracle and HOL bytecode from those directories:

```sh
uv run --with py-evm==0.12.1b1 --with eth-abi==6.0.0 python3 \
  lowering/defs/bytecode/memory_store_witnesses.py execute \
  --fixtures /tmp/memory-store-oracle --output /tmp/memory-store-hol
```

The required results are `"ab"` for `t07_tuple_assign_string_elems` and
`("x", 3)` for `t08_tuple_assign_ret_type_mismatch` on both runtimes.

These checks cover the listed sources. [Issue #549](https://github.com/verifereum/vyper-hol/issues/549)
also documents an untested frontend limitation: empty `HexBytes` and `Bytes`
literals share a representation, although Vyper treats only the latter as an
empty-value fast path.
