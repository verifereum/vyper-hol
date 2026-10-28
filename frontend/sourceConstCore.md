# Opt-in source constant core

## Status and semantic sources

These theories are **not wired into the existing frontend**. They are a pure,
partial source evaluator, not completion of #543, source typing, reification,
module resolution, or whitelist removal. Only `SC_Value` satisfies a required
constant position; never fall back to compiler-folded metadata after failure.

Semantic reference: `/home/lukasz/vyper`, revision
`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c` (VYPER_PIN).

- `vyper/semantics/analysis/constant_folding.py`: eager child visitation;
  `visit_BinOp`, `visit_Compare`, `visit_Subscript`, literal-kind restrictions,
  shallow folded-node-kind homogeneity and shift counts 0..256.
- `vyper/ast/nodes.py`: literal validation and the individual operator methods,
  especially `Mult`, `Div`, `FloorDiv`, `Mod`, `Pow`, `Invert`. `from_node` does
  not validate every arithmetic result as a new source/runtime literal.
- `vyper/utils.py`: Decimal precision **78**, default ROUND_HALF_EVEN context;
  `quantize` explicitly uses ROUND_DOWN and ten fractional places.
- `vyper/semantics/types/{base,primitives}.py`: source operator/type validation
  is separate from folding. Computing a value does not prove that the original
  expression was legal for its eventual type, signedness or width.

This is not the full witness/consumer inventory required by the overall plan.
Builtin rules now cover the retained witness inventory; see
[sourceConstBuiltin.md](sourceConstBuiltin.md) for their domains, resolved-identity
requirements and Keccak computation proofs. Other builtin groups remain
explicitly unsupported. The core must remain opt-in until its remaining
coverage, original-expression typing and integration obligations are discharged.

## Decoder/resolver interface

`sourceConstASTTheory` is independent of JSON and runtime theories. It contains
no inferred types, widths, compiler-folded replacements or runtime state.

- Expressions preserve literal, name, dynamic, unary, binary, Boolean,
  comparison, list, tuple, subscript, resolved-builtin, ordinary-call and
  unsupported syntax, including children and positional/keyword arguments.
- Decimal tokens are exact coefficient/decimal-place pairs, **not** host floats
  or Decimal source-text replacement fields. Values use coefficients at 10^10.
- Strings are ASCII, Bytes are natural-number octets <256. **Hex retains its
  original string spelling**, with a lowercase `0x` prefix, nonempty even-length
  digits, and hexadecimal character validation. This is essential: normal Hex
  equality ignores letter case, but pinned membership compares raw spelling.
  Hex is never silently converted to Bytes. A decoder must also establish the
  original token's lexical validity.
- Lists, nonempty tuples and nominal structs retain distinct structural kinds.
  Struct expressions/reification are not implemented; structural validity does
  not establish homogeneous/nominal source typing.
- Environments map canonical name paths to `SC_Constant value` or
  `SC_DynamicBinding`. `ALOOKUP` is first-match. A later resolver must establish
  identity, uniqueness, shadowing and dependency correctness. A missing binding
  is `SCS_UnresolvedName`, not a genuinely dynamic expression.
- `SCE_Builtin` contains a resolved identity, never just a spelling. `SCE_Call`
  retains its expression callee. No call is treated as a builtin by its name.

API:

```text
source_const_eval : environment -> source_const_expr
                  -> source_const_value source_const_result
```

Results distinguish `SC_Value`, `SC_NotConstant`, `SC_Invalid error` and
`SC_Unsupported reason`. Dynamic syntax/bindings alone justify NotConstant.
Unimplemented parents remain Unsupported even when some children are dynamic.

## Implemented domain

| Form | Rule |
|---|---|
| Int / Bool literals | Mathematical integer / Boolean |
| Decimal literal | Exact coefficient * 10^(10-places), places <= 10 |
| String / Bytes / Hex | Validated ASCII / octets / original Hex token |
| Unary minus | Mathematical integer; Decimal context rounding before negation result |
| Boolean not | Boolean only |
| Invert | Integer XOR (2^256 - 1), the pinned AST mask |
| Integer +, -, * | Mathematical, unbounded intermediates/results |
| Integer //, % | Zero rejected; quotient toward zero; dividend-signed remainder |
| Integer / | Zero rejected first; otherwise invalid non-Decimal domain |
| Integer power | Negative exponents rejected; zero exponent gives 1, including 0**0; bases 0, 1, -1 have arbitrary-exponent fast paths; see guard boundary below |
| Integer shifts | Count 0..256; unwrapped left shift, arithmetic right shift |
| Integer &, \|, ^ | Mathematical signed bitwise operations |
| Decimal +, - | Round result to the 78-significant-digit context |
| Decimal * | Context-round the scale-20 product, then truncate toward zero to scale 10 |
| Decimal / | Context-round the rational quotient, then truncate toward zero to scale 10; preserve the pinned negative-result recomputation |
| Decimal % | Apply context to absolute operands, reject a quotient needing >78 digits, then dividend-signed Decimal remainder |
| Decimal //, power, bitwise | Invalid domains; // zero is rejected before its domain check; shift-count validation precedes the Decimal shift domain check |
| Numeric comparisons | Same-kind Int or Decimal: ==, !=, <, <=, >, >= |
| Bool / String / Bytes / Hex comparisons | Same literal kind, == / != only; Hex comparison normalizes letter case |
| Membership | Constant scalar left, homogeneous scalar literal List right; Python value equality, not ordinary same-kind comparison |
| Literal-list subscript | Shallow homogeneous folded-node kinds, Int index, 0 <= index < length; return selected element |
| Boolean chains | At least two Boolean operands, eager evaluation |
| Lists / tuples | Eager children, distinct structural kinds; empty tuple invalid |
| Environment constants | Check recursive structural validity before returning |

### Decimal details and boundary

`source_const_context` implements ROUND_HALF_EVEN by integer quotient/remainder
and decimal digit counts. Division locates the rational's significant-digit
exponent using integer comparisons, without floating-point or real-log
approximations. Context rounding is **before** ROUND_DOWN quantization: replacing
both stages by one exact rational truncation gives wrong boundary results.

Pinned `Div._op` recomputes negative results as `-(-left / right)`. Unary Decimal
minus rounds its operand to the context; the evaluator preserves this extra
rounding, including its observable last-place asymmetry for large intermediates.

Multiplication/division quantization rejects results whose scale-10 coefficient
needs more than 78 digits. Addition/subtraction do **not** impose that quantize
check, nor DecimalT's runtime bound. Modulo uses the context's quotient-length
restriction instead. Each operation quantizes where its own pinned method does:
`(1.0 / 3.0) * 3.0` gives `0.9999999999`, not `1.0`.

Host Decimal exponent limits/subnormal behavior are not modeled. Arithmetic
operands (and unary Decimal minus) must have coefficients of at most **1000
decimal digits**; larger inputs return `SCS_DecimalOperation`. This conservative
envelope keeps supported operations far from Emax/Emin; it is not a source
runtime-width restriction. Literal construction and exact comparisons do not
silently inherit this arithmetic envelope.

### Integer-power guard boundary

Pinned `Pow._op` tests a **host binary64 logarithm heuristic**, not an exact
uint256 bound. The evaluator does not pretend those are interchangeable:

- Negative exponents are invalid before any base fast path.
- For |base| <= 1, arbitrarily large nonnegative exponents are supported.
- Otherwise exponent >=258 or |base| >=2^258 is rejected without exponentiation.
- The remaining candidate powers are bounded computations. Results of magnitude
  <=2^256 and exactly 2^257 are supported; magnitude >=2^258 is rejected.
- Other results in the deliberate uncertainty band return **`SCS_Power`**.
  Completing that band requires a pinned host-logarithm guard specification.
  It must not be replaced by either overflow wrapping or an exact 2^256 cutoff.

In particular, both `2**256` and `2**257` fold successfully here, while
`(-2)**258` is rejected. No typed-runtime representability conclusion follows.

### Membership and list-subscript details

Membership deliberately follows Python value equality after the pinned folder's
literal-list checks: `True in [1]`, `1 in [1.0]`, and `"0xAB" in [0xAB]` are true;
`0xAB in [0xab]` is false. Mixed-kind right lists are rejected even if their
first element matches. Empty lists are allowed. Aggregates are not scalar
membership operands. These folding rules are not source type-checking claims.

Subscript homogeneity is **shallow folded node kind**, not recursive element type:
`[[1], [True]][1]` folds to `[True]`, but `[1, True][0]` does not fold. Negative,
out-of-range and empty-list indices are invalid; Bool indices are not Int.
Tuple, String, Bytes and Hex subscripting are not pinned literal-list folding
rules. Nominal struct values are not claimed to identify a folded AST node kind;
subscript lists containing them remain explicitly unsupported.

## Eagerness, proofs and regressions

`source_const_combine`, `source_const_collect` and `source_const_then` implement
an explicit failure algebra: invalid children dominate unsupported/dynamic
children anywhere; within a class the first source-order failure wins.
Unsupported dominates dynamic. Every child must produce a value before an
implemented parent rule runs. Even unsupported calls collect positional and
keyword children eagerly. This algebra does not claim exact reproduction of
all pinned diagnostic messages or their ordering.

`sourceConstEvalPropsTheory` provides:

- Exact collection success/error characterizations and no dynamic success.
- `source_const_eval_value_ok`, including selected-list-element preservation.
- Domain lemmas for Booleans, shifts, divisors, negative powers, membership and
  successful literal-list subscripting; Decimal multiplication's quantization
  equation and same-kind comparison reduction.
- HOL quotient/remainder connection, remainder magnitude/sign and unbounded
  integer addition.
- Executable kernel regressions for signed arithmetic, shift boundaries,
  Boolean eagerness, invalid children under dynamic/unsupported parents, literal
  validation, Hex comparison versus membership, cross-kind Python membership,
  empty/mixed/nested lists, invalid index domains, power fast paths/bounds,
  Decimal signed/truncated operations, per-operation quantization, precision-78
  ties, quantization overflow and negative-division context recomputation.
- An audit of **every export in all three core theories**: no open hypotheses,
  axioms or oracle tags other than DISK_THM bookkeeping.

Local reference checks used the pinned Python operator methods and folder.
Additionally, 3000 deterministic Decimal differential probes (seed 543; +, -, *,
/, %; varied signed coefficients up to 114 digits) agreed with the integer
rounding algorithm. These checks are regression evidence, not a formal theorem
connecting HOL definitions to Python or proof of complete source coverage.

The primitive value-to-runtime reification bridge is now proved separately in
[sourceConstValue.md](sourceConstValue.md). It is not an original-expression
legality or replacement-equivalence theorem. Aggregate reification, full source
typing, program transport and compiler composition remain unproved.

## Build validation boundary

Normal project builds are now supported by **holbuild 0.11.7** at
`.agent-files/.holbuild-toolchain/bin/holbuild`; the previous 0.11.4 manifest
version blocker no longer applies. Neither project nor dependency manifests
need a version bypass. The normal project command is:

```sh
.agent-files/.holbuild-toolchain/bin/holbuild \
  sourceConstASTTheory sourceConstEvalTheory sourceConstEvalPropsTheory \
  --force=theory --skip-checkpoints --no-cache --tactic-timeout 2.5
```

The command above passed after these changes in **24.485 seconds**, with no
CHEAT warnings. The kernel audit reported 192 AST exports, 49 evaluator exports
and 62 property exports, all closed. A separate clean isolated build also
passed in 23.231 seconds with the same 2.5-second tactic timeout.

This checks the opt-in theories in the ordinary dependency context, not frontend
integration or completion of #543. The pinned HOL revision remains
`652d1f0aad5cd537ed1e5d470ba3444e70ba470e`.
