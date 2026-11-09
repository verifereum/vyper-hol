# External-call witnesses

These sources exercise the lowering of one external call: the 4-byte selector,
the result buffer, the decode of the returned value, `default_return_value`
and interface constructors used as call arguments
([issue #555](https://github.com/verifereum/vyper-hol/issues/555)), and the
keyword operands `value=`, `gas=`, `default_return_value=` and
`skip_contract_check=` of extcall/staticcall, and `send` with and without
`gas=` ([issue #553](https://github.com/verifereum/vyper-hol/issues/553)).
`parity-fixtures.txt` selects 10 exact bytecode comparisons; the other sources
are controls and related witnesses kept for diagnostic comparison.
The `m10c_iface_storage_main` witness covers first-occurrence DFT dependency
ordering (issue #574); its exact-bytes check is removed until the changed ABI
encoder is ported.
The existing 101-fixture corpus is unchanged.

`oracle/` contains independently generated annotated AST/layout JSON and
deployment/runtime bytecode. Its provenance records the pinned compiler,
settings, dependencies and input/output hashes. Use the isolated Python 3.11.11
Vyper installation described in the parent bytecode README, with `VYPER_PIN`
and `python-o1-oracle-constraints.txt`, to reproduce these files. From the
repository root, with that environment first on `PATH`:

```sh
python bytecode/memory_store_witnesses.py prepare \
  --corpus external-calls --fixtures /tmp/external-call-oracle --check
```

The native runner checks exact deployment and runtime bytecode equality with
the oracle for the witnessed fixtures (`../native/README.md`); from `bytecode/`:

```sh
./native/bytecode_parity_native.exe . external-calls
```

For a diagnostic report covering every source, run this from the worktree being
tested:

```sh
python3 bytecode/memory_store_witnesses.py probe \
  --corpus external-calls --fixtures /tmp/external-call-oracle \
  --output /tmp/external-call-hol
```

`--only NAME` selects a source and may be repeated. The results are recorded
in [`docs/external-call-parity.md`](../../docs/external-call-parity.md).
