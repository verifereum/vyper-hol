# F12 — Empty-account codehash is zero, not Keccak(empty)

**Intended maintainer:** source account/environment builtin semantics.
**Disposition: FIXED here**, TASK009, landed `3636018d`.
[Evidence, history and current audit](README.md).

## Minimal counterexample and exact behavior

Evaluate `.codehash` for account with balance0, nonce0, code`[]` (storage arbitrary).
Old source returned Keccak of empty bytes:
`c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.
Venom/EVM EXTCODEHASH return the 256-bit word0, represented in source as
**32 zero bytes**, not an empty byte string. Current source matches that.

Control cases matter: balance1/code`[]`/nonce0, or balance0/code`[]`/nonce1,
are nonempty accounts and return the Keccak(empty) vector above. Nonempty code
returns its Keccak. Storage contents do not participate in `account_empty`.

## Current owners and reference evidence

- [Source](../../semantics/vyperContextScript.sml): `evaluate_account_op_def`,
  `evaluate_account_codehash_empty`, `evaluate_account_codehash_nonempty`.
- [Typing](../../semantics/prop/vyperTypeBuiltinsScript.sml):
  `evaluate_account_codehash_length`, retained `account_well_typed_op`.
- [Regressions](../../tests/vyperAccountCodehashTestScript.sml):
  `codehash_empty_account_boundary`, `codehash_empty_account_eval`,
  `codehash_empty_code_balance_nonce_eval`, `codehash_builtin_cv_boundaries`.
- [Venom EXTCODEHASH](../../venom/defs/venomExecSemanticsScript.sml): uses
  empty-account check before hashing code.
- Affected [account_items source](../../lowering/defs/bytecode/python-o1-no-asm-opt-sources/account_items.vy),
  [HOL fixture](../../lowering/defs/bytecode/eval/evalCompilerSubsetBuiltinsScript.sml),
  [byte endpoint](../../lowering/defs/bytecode/eval/evalCompilerBytecodeBuiltinsAccountHashScript.sml).

Pinned reference `vyper/codegen/expr.py:250–254`, `Expr.parse_Attribute`,
codehash branch emits `extcodehash` with bytes32 type (subject to the EVM-version
check). `vyper/venom/builder.py`, `VenomBuilder.extcodehash`, likewise emits the
EVM operation. This is reference instruction evidence, not a Python interpreter
claim or a compiler run performed here.

## Reproduction and evidence distinction

Compare old `git show c587772d:semantics/vyperContextScript.sml` unconditional
Codehash clause with current `account_empty` branch; substitute the two control
accounts above. Follow the literal-vector EVAL/CV regressions and reference
attribute dispatch. TASK009 receipt records eight actually built regressions
and21 closed source/test/CV objects. Its original parity receipt explicitly
contained94 conditional endpoints; later repairs do not retroactively make
that receipt an unconditional certificate. No endpoint/bytes changed here.

Historical PLAN: §4.2 F12, lines704–707; D12c; §5.3c; §6.2 Acc row.
Old source `vyperContextScript.sml:105`; Venom911–917/EVM867–880 in the plan.
