# Fixtures pending the vyperlang/vyper#5127 port

Vyper `v0.5.0b1` (`VYPER_PIN`) changed the bytecode of the fixtures below,
mostly through vyperlang/vyper#5127, which rewrote ABI encoding and
allocation. Their oracles are regenerated at the pin, but the HOL compiler
still differs for the reasons below. These fixtures are excluded from the
bytecode-parity checks until their remaining difference is resolved.

P1 (ceil32: `and(add(x, 31), not 31)`), P2 (dynamic external arguments
assert that their calldata offset isn't below 4, `_get_abi_arg_ptr`), P5 (a
slice's output buffer allocated after its bounds check), P3 (escaping
allocations: comparisons don't make an allocation escape, escaping static
allocations stay live everywhere and are allocated first) and P6 (eager call
arguments: internal- and external-call arguments are read as they are
evaluated, also a source-semantics change), P7 (subscript overlap: an
array base derived through a dynamic-array element is copied before an index
that writes a variable the base reads or makes a risky call, also a
source-semantics change) and P9 (constructor argument snapshot: each
constructor argument is read as it is evaluated, a composite one copied
before a later argument that can modify memory or storage, also a
source-semantics change) are ported. P4 encodes directly into the destination
buffer, and P8 sizes the `raw_create` buffers from the bytecode argument's
type. The attribution comes from reverting one change at a time in the
pinned compiler and recompiling.

## P2 (calldata argument guard)

P2 is ported. These still differ from the oracle with it:

- `raw-system/rl_const_topics`: the frontend now expands constant topics
  to a literal array with the reference's bound before checking. The raw
  checker still rejects a top-level name, as `raw_log_rejects_constant_topics`
  records; `raw_log_constant_topics_frontend_accepted` checks the translated
  contract. This bytecode fixture remains pending its parity port.
- `builtin-forms/concat_wide_local`

## Pop receiver copy (vyperlang/vyper#5280), not #5127

- `load_timing/nested_retained_pop`: the pinned compiler's
  `_lower_dynarray_pop` copies a receiver whose index can resize it and pops
  the copy, so the pop is lost; the source semantics pops the array itself.
  Since vyperlang/vyper#5280, after the pin, the compiler rejects such a pop.

## Bounded memory ABI decoding

- `main/abi_dynamic`: the memory `abi_decode` path still emits
  relative-position and head bounds checks before the load in both profiles.
  See [bounded memory ABI decoding](pending-bounded-decode-guards.md).
- `main/abi_static`: the same memory `abi_decode` checks differ in both profiles.

## Constant folding (#543), not #5127

- `raw-system/rl05_3topics_concat`: HOL hashes the literal `b"x"` at runtime
  with `KECCAK256`, while the pinned Python compiler embeds the constant hash.
  The retained `rl07_3topics_concat_nolit` fixture checks the nonliteral path.
  This remains outside exact bytecode parity until
  [#543](https://github.com/verifereum/vyper-hol/issues/543) supplies the same
  compile-time folding.
