# Source constant builtin rules

Builtin rules for the [source constant core](sourceConstCore.md). Semantic
reference is VYPER_PIN, in particular `builtins/functions.py` and its original
argument/type validation, not merely the folder's permissive `_try_fold`.
See [constant evaluation](constant-evaluation.md) for pipeline and trust boundaries.

## Resolver/decoder API

`SCE_Builtin` must carry a **resolved identity**, not a name lookup by spelling.
Supported identities are `SCB_Abs`, `SCB_PowMod256`, `SCB_Uint256AddMod`,
`SCB_Uint256MulMod`, `SCB_Len`, `SCB_Min`, `SCB_Max`, `SCB_Keccak256`, and
`SCB_MethodId`. Ordinary `SCE_Call` remains an ordinary call.

`SCE_BytesType fixed bound` retains a source-computed type bound. `fixed = T`
means the resolved `bytesM` type constructor, `F` means resolved `Bytes[N]`.
For `bytes4`, use `SCE_BytesType T (SCE_Literal (SCL_Int 4))`. For `Bytes[2+2]`,
retain that addition under `SCE_BytesType F`. These constructors must only be
emitted after resolving the **type constructor**, not by treating a shadowed
identifier spelling as a builtin. Keyword values remain original expressions;
never substitute an inferred/folded output type.

The additional value `SCV_BytesType fixed width` is a **type descriptor**, not a
runtime value or ordinary Vyper constant. Reifiers must reject it as runtime
data; `method_id` consumes it only as the source `output_type` keyword.
Fixed selector output is the existing `SCV_Hex`, dynamic output is the existing
`SCV_Bytes`.

## Domains

* `len`: one String/Bytes operand, actual byte length. Not fixed bytes: although
  `_try_fold` can count Hex, the original builtin signature excludes BytesM.
* `min`/`max`: two Ints with a common signed/unsigned integer type, or two
  Decimal coefficients fitting signed 168 bits. No mixed literal kinds or Bool.
* `abs`: one signed int256 and a representable signed int256 result. Reject
  minimum-signed overflow instead of hiding it behind a positive literal.
* `pow_mod256`: two uint256 operands; logarithmic modular exponentiation.
* `uint256_addmod`/`uint256_mulmod`: three uint256 operands, nonzero modulus;
  unbounded sum/product before modulus, never wrap intermediate arithmetic.
* `keccak256`: String, Bytes or exactly bytes32 Hex; Hex must satisfy the
  original fixed-byte literal syntax/case restriction.
* `method_id`: constant ASCII String with no space; one argument and optional
  unique `output_type` of bytes4 or Bytes[4], default Bytes[4]. Runtime arguments
  are invalid, not a residual runtime builtin. Other keywords/types reject.

Implemented builtins check positional arity and keyword names/duplicates before
producing a value. All child expressions (including type bounds) use the core's
eager failure algebra. Invalid children dominate dynamic/unsupported children.
An original expression's broader numeric/source typing remains the elaborator's
responsibility: structural value validity is not a typing certificate.

## Formal computation

`source_const_keccak` directly uses dependency `keccakTheory.Keccak_256_w64`.
`Keccak_256_w64_thm` proves equality with `Keccak_256_bytes`, the byte wrapper
around bit-level Keccak. The dependency also provides a proved cv translation
and unconditional `Keccak_256_w64_pre`; no external hash oracle is introduced.
Import `sourceConstBuiltinComputeTheory` for the proved cv translations of our
natural-byte wrapper, hex encoder, and modular exponentiation.
`source_const_keccak_specification` records this connection for our natural-byte
interface. Selector order is `TAKE 4` of the hash bytes, with no integer endian
conversion. `source_const_modexp_correct` connects the executable logarithmic
algorithm to mathematical power modulo 2^256.

Proofs and executable regressions live in
[sourceConstBuiltinPropsScript.sml](sourceConstBuiltinPropsScript.sml),
[sourceConstBuiltinTestScript.sml](sourceConstBuiltinTestScript.sml), and
[sourceConstEvalPropsScript.sml](sourceConstEvalPropsScript.sml). These local
computation theorems do not establish source/runtime equivalence.
