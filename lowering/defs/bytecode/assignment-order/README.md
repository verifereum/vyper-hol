# Assignment order validation

`fixtures.txt` lists the 13 witnesses. `sources/` contains their Vyper sources;
`oracle/` contains independent bytecode, annotated AST/layout exports, and
compiler provenance. The frozen 101-fixture corpus has its own provenance.

Run the HOL validation and its proof-dependency audit from the repository root:

```sh
holbuild --tactic-timeout 30 vyperAssignmentOrderAuditTheory
```

`../eval/evalAssignmentOrderScript.sml` checks:

- Runtime and deployment frontend acceptance for all 13 source-derived inputs.
- Supported-program acceptance and exact deployment/runtime bytecode equality
  for c08, c09, g6, x04, s11 and g19.
- Flat tuple assignment support, nested tuple rejection, and exclusion of the
  nested-pop compiler form.
- Nine interpreter regressions: assignment side effects, delayed storage and
  popped reads, nested pops, augmented assignment reads, storage and memory
  shrinking, append after shrinking, and x03's target-bounds error.

Check the expected reference behavior independently in an EVM:

```sh
uv venv /tmp/assignment-order-evm
uv pip install --python /tmp/assignment-order-evm/bin/python py-evm==0.12.1b1
/tmp/assignment-order-evm/bin/python lowering/defs/bytecode/assignment-order/check_evm.py
```

The runner checks genuine `REVERT` for x03, return data, and raw storage slots.
The s11 external-call stub returns 7. Storage augmentation starts with length 1
and element 5, then checks length 0 and the old element slot containing 10.

Regenerate the oracle with the pinned Vyper installed in an isolated environment:

```sh
/path/to/vyper-env/bin/python lowering/defs/bytecode/python_o1_bytecode_oracle.py \
  --expected-commit cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c \
  --expected-python 3.14.4 --generator-uv 0.11.8 \
  --expected-install-root /path/to/vyper-env \
  --sources lowering/defs/bytecode/assignment-order/sources \
  --fixture-manifest lowering/defs/bytecode/assignment-order/fixtures.txt \
  --output lowering/defs/bytecode/assignment-order/oracle --frontend
```

The oracle uses experimental code generation, `OptimizationLevel.NONE`, Prague,
and no bytecode metadata. Exact x03 compiler parity depends on #560; nested-pop
compiler lowering is tracked in #559. Their interpreter regressions remain
checked here.
