# F15 — Decimal multiplication accepts the negative minimum

**Intended maintainer:** source decimal arithmetic / word-to-source type bridge.
**Disposition: FIXED here**, TASK015, landed `cacf8575`.
[Evidence, history and current audit](README.md).

## Minimal counterexample and exact behavior

Multiply minimum decimal by1.0. Exact **scaled integer** operands are
`DecimalV (-&(2**167))` and `DecimalV 10000000000`; equivalently the first
operand is scaled−187072209578355573530071658587684226515959365500928.
The product's toward-zero scaled quotient is **`−2**167`**, an allowed Signed168
minimum. Old guard checked `within_int_bound (Signed 168) (ABS p / 10000000000)`:
positive2**167 is one past the maximum, so it returned
`RuntimeError "Decimal Mul bound"`. Lowered SDIV+signed range clamp and pinned
reference accept the negative minimum. Current source returns exactly
`INL (DecimalV (-&(2**167)))`.

Current formula is `q = SGN p * (ABS p / 10000000000)`; it tests Signed168 on
**q**, not its absolute value. Exactly+2**167 and−2**167−1 still fail. Signed
fractional products truncate toward zero, not mathematical floor.

## Current owners, fixture and reference evidence

- [Source](../../semantics/vyperValueOperationScript.sml): `evaluate_binop`, decimal Mul.
- [Type bridge](../../semantics/prop/vyperTypeBuiltinsScript.sml): local signed
  guard/word bridge (original body retained); exported success/no-TypeError
  statements unchanged. A local helper is not a separately saved export.
- [Regressions](../../tests/vyperDecimalMulTestScript.sml): `decimal_mul_minimum`,
  `decimal_mul_signed_result`, `decimal_mul_boundaries_eval`,
  `decimal_mul_boundaries_cv`, fixture runtime/deployment checks.
- [Lowering](../../lowering/defs/exprLoweringScript.sml): `compile_safe_mul`.
- Unchanged [scalar_arith_decimal_mul source](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/scalar_arith_decimal_mul.vy),
  [HOL scalar fixtures](../../lowering/defs/bytecode/eval/evalCompilerSubsetScalarsScript.sml).

Pinned `vyper/codegen/arithmetic.py`, `safe_mul`217–279: checks256-bit product
wrap, divides decimal result with SDIV, then `clamp_basetype`. Pinned
`vyper/codegen/core.py:1359–1420`, `clamp_basetype` / `int_clamp`, uses signed
canonical representation for168 bits, so the negative minimum is valid.
These were read, not compiled or executed here.

## Reproduction and prior rebuilt evidence

Inspect old/current decimal Mul and the literal minimum theorem. Compute p's
sign, divide its magnitude by10**10 and compare the two guards; follow the
same SDIV/clamp ordering in lowering/reference. This is definition-level
inspection, not a new end-to-end run. TASK015 receipt records12 independent
EVAL/CV cases and29 closed inspected objects; primary016 later revalidated
those29 and the full non-parity source checkpoint at `707ec670`. Final060 remains
open. Fixture source, hex lists, plain-EVAL endpoints and all original proof
text are unchanged by this report.

Historical PLAN: §4.2 F15,736–742; D12i; §5.3i; §6.2 Mul row.
Old source232–236, `compile_safe_mul`217–232.
