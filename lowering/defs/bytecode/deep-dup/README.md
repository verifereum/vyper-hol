# Deep-DUP pending differential fixtures (issue 562)

These are the exact two TASK witness signatures. `cases.json` contains all ten
inputs and independently ABI-derived calldata/return words. Prepend the selector
to the big-endian 32-byte words for calldata; return data is those same words
without the selector. `check_runtime.py` rederives offsets from the nested input,
checks the explicit vectors, and rejects both reverts and incorrect return data.

Status (2026-10-23): externally executed against `a3160f90dd2e`, with the
reconstructed fixture sources in the working tree. Python syntax/self-tests and
independent `eth-abi` vector/selector checks pass. The environment uses Python
3.11.11, pinned Vyper `cd74ce4f`, the repository's oracle dependency constraints,
uv 0.10.11 and py-evm 0.12.1b1 (PragueVM).

Both witnesses pass `check_contract` in deployment and runtime modes; both remain
outside `supported_program`. Actual results before integrating #551 are:

| Witness | Deploy bytes (HOL / Vyper) | Runtime bytes (HOL / Vyper) | Runtime cases (HOL / Vyper) |
| --- | --- | --- | --- |
| `arr_fixed_of_dyn` | 529 / 510 | 508 / 489 | 5/5 / 5/5 pass |
| `arr_dyn_of_dyn` | 636 / 659 | 615 / 638 | 1/5 / 5/5 pass |

HOL reverts on all four nonempty dynamic-array inputs. Both deployment and
runtime byte comparisons report `PARITY_DEFECT`. The #551 branch contains
calldata guard and dynamic-child encode-loop repairs absent from this checkout;
the retained source diff and history identify these changes.

A separate isolated clean merge with committed #551
`6230c620b5208eb1f5e2eb7524e3215dc101c5ef` establishes `MATCH` for both witnesses:
deployment and runtime bytes equal pinned Vyper, and all ten inputs pass on both
runtimes (20 executions). The full current-source parity corpus also passes all
33 HOL targets without CHEAT warnings. These combined witness results depend on
#551; that dependency is not integrated into this checkout. The commented
manifest keeps the fixtures pending; the whitelist is unchanged.

Command receipts, independent oracle inputs/bytes, HOL outputs, every runtime
result and the final corpus/release report are retained under
`.agent-files/deep-dup-validation/`. The runtime checker runs all ten inputs on
both producers even when byte parity or an earlier runtime case fails.

## Reproduction

From the repository root, in a pinned Vyper environment (VYPER_PIN, Python
3.11.11, constraints in the parent directory):

```sh
python3 -m py_compile lowering/defs/bytecode/deep-dup/check_runtime.py
python3 lowering/defs/bytecode/deep-dup/check_runtime.py --self-test
python3 lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --corpus deep-dup --repo "$PWD" --fixtures /tmp/deep-dup-python
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --corpus deep-dup --repo "$PWD" --fixtures /tmp/deep-dup-python \
  --output /tmp/deep-dup-hol
python3 lowering/defs/bytecode/deep-dup/check_runtime.py \
  --python-dir /tmp/deep-dup-python --hol-dir /tmp/deep-dup-hol
lowering/defs/bytecode/python-o1-bytecode-fixtures --compare-hol \
  --vyper-repo /path/to/clean/pinned/vyper
```

The existing prepare command exports annotated AST/layout, sanitizes them, and
compiles Python deployment/runtime using experimental codegen, Prague,
optimization NONE, no metadata. It checks the installed compiler commit against
VYPER_PIN and records provenance. The probe command retains checker/compiler
status and exact bytes; inspect its status/summary/logs as well as the runtime
checker output. Runtime byte equality alone does not prove checker acceptance.
The full corpus command is separate and must not be omitted. The runtime checker
requires py-evm with `eth.vm.forks.prague.PragueVM`; it executes fresh runtime
state for each call. Deployment parity is checked separately, not executed by
this runner. Do not manufacture independent expected bytecode from HOL output.

#551 contains separate decode and encode lowering repairs needed for end-to-end
MATCH. Missing #551 must be recorded explicitly, not implemented here. Promote
fixtures only after independently generated oracle, checker acceptance, byte
parity, all runtime cases and full-corpus results are retained and reviewed.
