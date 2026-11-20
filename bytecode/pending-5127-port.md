# Fixtures pending the vyperlang/vyper#5127 port

Vyper `v0.5.0b1` (`VYPER_PIN`) changed the bytecode of the fixtures below,
mostly through vyperlang/vyper#5127, which rewrote ABI encoding and
allocation. Their oracles are regenerated at the pin, but the HOL compiler
still produces the previous bytes, so they are out of the bytecode-parity
checks (the native runner and the corpora's
`parity-fixtures.txt`) until the change that restores each is ported. Each port
puts its fixtures back and removes them from this list.

The changes, as they appear in the pinned Python compiler:

- P4 direct ABI encoder: values are encoded straight into the destination
  buffer, and an external call sends exactly the encoded length plus 4 bytes.
  It also covers `_revert_with_custom_error`, which lowers each argument as
  a value (`snapshot_value_for_delayed_use`), keeps no declared-type
  argument tuple, and encodes with `abi_encode_values_to_buf`; the
  `custom-errors/` fixtures return to parity with that port.

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
source-semantics change) are ported. The CREATE paths now use P4, and P8
sizes the `raw_create` buffers from the bytecode argument's type. P2 still
heads sections below: two fixtures that differ for other reasons, and
those that also need P4. The attribution comes from reverting one change
at a time in the pinned compiler and recompiling.

## P2 (calldata argument guard)

P2 is ported. These still differ from the oracle with it:

- `raw-system/rl_const_topics`: the frontend now expands constant topics
  to a literal array with the reference's bound before checking. The raw
  checker still rejects a top-level name, as `raw_log_rejects_constant_topics`
  records; `raw_log_constant_topics_frontend_accepted` checks the translated
  contract. This bytecode fixture remains pending its parity port.
- `builtin-forms/concat_wide_local`

## P4 (direct ABI encoder)

- `custom-errors/ce_assert_dynamic`
- `custom-errors/ce_assert_noargs`
- `custom-errors/ce_assert_static`
- `custom-errors/ce_raise_kwargs`
- `custom-errors/ce_raise_noargs`
- `custom-errors/ce_raise_static`
- `external-entries/base_dom1`
- `main/event_log`
- `main/mixed_event_log`

## Pop receiver copy (vyperlang/vyper#5280), not #5127

- `load_timing/nested_retained_pop`: the pinned compiler's
  `_lower_dynarray_pop` copies a receiver whose index can resize it and pops
  the copy, so the pop is lost; the source semantics pops the array itself.
  Since vyperlang/vyper#5280, after the pin, the compiler rejects such a pop.

## P2 (calldata argument guard) + P4 (direct ABI encoder)

- `abi-codegen/enc_ensT_bytes`: after the builtin encoder port, the runtime
  still uses `PUSH2 0x0100` where the oracle uses `PUSH1 0xe0`. The extra byte
  moves the revert destination from `0x013b` to `0x013c`.
- `custom-errors/ce_raise_dynamic`
- `custom-errors/ce_raise_dynarray`
- `main/abi_dynamic`: the memory `abi_decode` path still emits
  relative-position and head bounds checks before the load in both profiles.
  See [bounded memory ABI decoding](pending-bounded-decode-guards.md).
- `main/abi_static`: the same memory `abi_decode` checks differ in both profiles.
- `main/mixed_event_types`

## Not yet attributed

- `memory-stores/w01_return_intcall_dynarray_bytes_widen`

## Constant folding (#543), not #5127

- `raw-system/rl05_3topics_concat`: HOL hashes the literal `b"x"` at runtime
  with `KECCAK256`, while the pinned Python compiler embeds the constant hash.
  The retained `rl07_3topics_concat_nolit` fixture checks the nonliteral path.
  This remains outside exact bytecode parity until
  [#543](https://github.com/verifereum/vyper-hol/issues/543) supplies the same
  compile-time folding.
