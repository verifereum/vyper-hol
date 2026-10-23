# Assignment order witnesses

`sources/` contains the 13 concrete witnesses for issue #550.
`oracle/` contains independent Python Vyper deployment/runtime bytecode,
annotated AST/layout exports, compiler provenance, and reference EVM results.
The expected execution results in `check_evm.py` come from TASK.md.

The compiler is Vyper commit `cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`,
with experimental code generation, `OptimizationLevel.NONE`, Prague, and no
bytecode metadata. The provenance records the actual Python and dependency
versions; this corpus was generated with Python 3.14.4. The existing frozen
101-fixture corpus has its own provenance.

From the repository root, with that Vyper installed in an isolated environment:

```sh
/path/to/vyper-env/bin/python \
  lowering/defs/bytecode/python_o1_bytecode_oracle.py \
  --expected-commit cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c \
  --expected-python 3.14.4 --generator-uv 0.11.8 \
  --expected-install-root /path/to/vyper-env \
  --sources lowering/defs/bytecode/assignment-order/sources \
  --fixture-manifest lowering/defs/bytecode/assignment-order/fixtures.txt \
  --output lowering/defs/bytecode/assignment-order/oracle --frontend
```

Run the reference behavior checks:

```sh
uv venv /tmp/assignment-order-evm
uv pip install --python /tmp/assignment-order-evm/bin/python py-evm==0.12.1b1
/tmp/assignment-order-evm/bin/python \
  lowering/defs/bytecode/assignment-order/check_evm.py \
  --output lowering/defs/bytecode/assignment-order/oracle/evm-results.json
```

The EVM runner selects Prague, checks genuine `REVERT` for x03, and checks
return data and the specified raw storage slots. Its `--bytecode-dir` option
allows the same cases to run against exported HOL compiler output. An external
`g()` stub returns 7 for s11. Storage augmentation starts with length 1 and
element 5, and observes both the resulting length 0 and the old element slot 10.

The three required exact bytecode assertions, with frontend source-translation
and checker checks, are in `../eval/evalCompilerAssignmentOrderScript.sml`:

```sh
holbuild --tactic-timeout 600 evalCompilerAssignmentOrderTheory
```

The nine source-derived interpreter regressions are in
`../eval/evalInterpreterAssignmentOrderScript.sml`. They use the proved
big-step/CPS equivalence and kernel-checked CV evaluation. They cover x04,
g19, delayed storage and popped reads, the nested pop snapshot, all three
shrinking-RHS examples, and x03's exact target-bounds runtime error.

```sh
holbuild --tactic-timeout 600 evalInterpreterAssignmentOrderTheory
```

Evaluate and export actual HOL compiler output, then replay it in the same EVM:

```sh
holbuild --tactic-timeout 600 evalCompilerAssignmentEffectsTheory
python3 lowering/defs/bytecode/assignment-order/export_hol_bytecode.py \
  --output lowering/defs/bytecode/assignment-order/hol-output
/tmp/assignment-order-evm/bin/python \
  lowering/defs/bytecode/assignment-order/check_evm.py \
  --bytecode-dir lowering/defs/bytecode/assignment-order/hol-output \
  --output lowering/defs/bytecode/assignment-order/hol-output/evm-results.json
```

Recorded results:

- Reference Vyper EVM: 13/13 pass.
- HOL interpreter: 9/9 pass.
- Required c08/c09/g6/x04/s11/g19 deploy/runtime comparisons: MATCH.
- Extended HOL compiler EVM replay: 12/13 pass. The nested-pop program reverts:
  `compile_target_base` drops the subscript in `d[0].pop()`, so it pops the outer
  array. The required interpreter regression for this program passes.

`hol-output/comparisons.json` records every bytecode comparison, including the
additional local-array differences. `hol-output/evm-results.json` retains the
nested compiler failure and its original expected result.

Reference EVM success alone does not establish HOL interpreter agreement or
HOL bytecode parity. Those are separate checked obligations. The x03 bytecode
comparison also depends on the list-literal fix in #560.
