# F10 — Invalid EC points must fail, not return infinity

**Intended maintainer:** source semantics EC builtins / builtin type soundness.
**Disposition: FIXED here**, TASK007, landed `1c388afa`; no upstream submission.
[Evidence policy, history, receipts and current audit](README.md).

## Minimal counterexample and exact behavior

Call `ecadd([1,1], [0,0])`, or `ecmul([1,1], 0)` (also scalar1).
`[1,1]` is off the BN254 curve; `[0,0]` is valid infinity.
At PLAN baseline `c587772d`, `evaluate_ecadd`/`evaluate_ecmul` mapped a failed
precompile (`NONE`) to success `INL (mk_ec_result (0,0))`.
Lowered STATICCALL to precompile6/7 fails; its ASSERT reverts, rather than
returning the zero point. The EVM precompile's failure is `OutOfGas` internally;
the enclosing builtin call checks success. Invalid input is not a valid-input
resource escape in the current top theorem.

Current source returns exactly `INR (RuntimeError "ECAdd invalid point")` or
`INR (RuntimeError "ECMul invalid point")`. Argument-shape TypeErrors remain
separate; making validly typed invalid points a TypeError would falsify the
no-TypeError family. Valid `ecmul([1,2],0)` still succeeds with `[0,0]`.

## Current owners and reference evidence

- [Source](../../semantics/vyperContextScript.sml): `evaluate_ecadd_def`,
  `evaluate_ecmul_def`, `evaluate_ec_invalid_point_regression`,
  `evaluate_ec_field_bound_regression`, `evaluate_ec_valid_point_regression`.
- [Type consumers](../../semantics/prop/vyperTypeBuiltinsScript.sml): EC
  success typing and no-TypeError families (retained statements).
- [Lowering](../../lowering/defs/builtinMiscScript.sml): EC precompile
  STATICCALL and ASSERT sequences.
- Affected [ec_builtins source](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/ec_builtins.vy),
  [HOL fixture](../../lowering/defs/bytecode/eval/evalCompilerSubsetBuiltinsScript.sml),
  [byte endpoint](../../lowering/defs/bytecode/eval/evalCompilerBytecodeBuiltinsEcScript.sml).

Pinned reference `vyper/builtins/functions.py:802–843`,
`_ECArith.build_IR`, `ECAdd`, `ECMul`: allocates typed buffers and emits
`assert(staticcall(gas, _precompile, ...))`; precompile IDs6/7 are explicit.
Reference exports `functional/builtins/codegen/test_ec.json` / `test_ecadd`
contain actual `_ecadd` source in deployment trace `source_code` (hash in index).
These were read, not executed by this task.

## Reproduction and evidence distinction

Inspect the two old NONE branches with `git show c587772d:semantics/vyperContextScript.sml`;
substitute `(1,1),(0,0)` and scalar0. Compare the current named literal regression
and the reference `_ECArith` ASSERT. This is a definition-level reproduction;
no new compiled execution is claimed.
Existing TASK007 receipt records actual rebuilt seven EC theorems and eight
unchanged EC traces, with preserved no-TypeError claims. Its tag-only parity
checks are not silently promoted to closed final certificates; TASK060 remains open.

Historical PLAN: §4.2 F10, lines685–692; D12a; §5.3a;
§6.2 EC row. Historical source `vyperContextScript.sml:345–372`,
`builtinMiscScript.sml:105–157`; these are old, not current line numbers.
