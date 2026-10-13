# F14 — unsafe_div by zero returns zero

**Intended maintainer:** source integer arithmetic and binop property consumers.
**Disposition: FIXED here**, TASK014, landed `2855cf04`.
[Evidence, history and current audit](README.md).

## Minimal counterexample and exact behavior

`unsafe_div(1,0)` at uint8 (also signed int8) formerly returned
`INR (RuntimeError "UnsafeDiv0")`. Lowering emits unguarded DIV or SDIV;
EVM/Venom division by zero returns word0. Current source returns
`INL (IntV 0)` via `wrapped_int_op u 0`. **Checked** integer/decimal Div by
zero still fails; the fix is not a blanket division-error exemption.

Nonzero behavior is unchanged, including SDIV toward-zero and unsafe
MIN_INT/−1 wrapping. A success-implies-nonzero theorem that formerly included
UnsafeDiv becomes false under the corrected semantics: the uint8 input1/0
succeeds but its divisor is zero.

## Current owners, fixture and reference evidence

- [Source](../../semantics/vyperValueOperationScript.sml): `evaluate_binop`, UnsafeDiv arm.
- [Property](../../semantics/prop/vyperEvalBinopScript.sml):
  `evaluate_binop_div_mod_success_nonzero` removes only UnsafeDiv from its
  opcode disjunction, with original proof text retained; checked Div/Mod remain.
- [Regression](../../tests/vyperUnsafeDivTestScript.sml):
  `unsafe_div_success_nonzero_counterexample` proves the concrete success AND
  negates the old conclusion; boundary/EVAL/CV and actual builtin checks.
- [Lowering](../../lowering/defs/exprLoweringScript.sml): unsafe arithmetic DIV/SDIV dispatch.
- Unchanged [unsigned fixture](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/scalar_arith_unsafe_uint.vy)
  and [signed fixture](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/scalar_arith_unsafe_int.vy),
  [HOL scalar ASTs](../../lowering/defs/bytecode/eval/evalCompilerSubsetScalarsScript.sml).

Pinned reference `docs/built-in-functions.rst:848–850` specifies division by
zero returns0; `vyper/builtins/functions.py`, `_UnsafeMath.build_IR`1894–1920
and `UnsafeDiv`1938–1940, emit DIV/SDIV plus narrow-width wrapping, no zero guard.
Read-only evidence, not a newly executed reference test.

## Reproduction and actual prior evidence

Substitute `IntV 1`, `IntV 0`, `Unsigned 8` into old/current UnsafeDiv arms;
compare reference instruction generation and the exact retained counterexample.
TASK014 receipt records LOCAL44 targets/44 closed inspected objects,29 literal
EVAL/CV cases and all32 legal width checks, not a full suite/parity run.
Primary016 at `707ec670` later rechecked focused44 objects and completed the
non-parity source checkpoint; its machine summary was parsed here. That later
boundary supersedes014's historical pending016 paragraph, **not** final060 debt.

Historical PLAN: §4.2 F14,729–734; D12h; §5.3h; §6.2 UnsafeDiv row.
Original `vyperValueOperationScript.sml:269–275`, lowering474–476.
