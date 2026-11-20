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
- P8 `raw_create` bytecode type: `raw_create` types its bytecode argument
  with the argument's own type rather than `Bytes[49152]`, which sizes its
  initcode buffer (the HOL lowering still snapshots 49152 bytes).

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
source-semantics change) are ported. P2 still heads sections below: two
fixtures that differ for other reasons, and those that also need P4 or P8.
A fixture listed under several changes needs all of them. The attribution
comes from reverting one change at a time in the pinned compiler and
recompiling. The creation fixtures' P4 entries are by elimination: P4 can't
be reverted on its own, and no revert of the other changes restores those
fixtures.

## P2 (calldata argument guard)

P2 is ported. These still differ from the oracle with it:

- `raw-system/rl_const_topics`: the frontend now expands constant topics
  to a literal array with the reference's bound before checking. The raw
  checker still rejects a top-level name, as `raw_log_rejects_constant_topics`
  records; `raw_log_constant_topics_frontend_accepted` checks the translated
  contract. This bytecode fixture remains pending its parity port.
- `builtin-forms/concat_wide_local`

## P4 (direct ABI encoder)

- `abi-codegen/enc_multi`
- `create-builtins/cb02_blueprint_args`
- `create-builtins/cb05_blueprint_rof`
- `create-builtins/cb07_blueprint_args_salt`
- `external-entries/base_dom1`
- `memory-stores/enc_in_assign`
- `raw-system/rr03_abi`

## Pop receiver copy (vyperlang/vyper#5280), not #5127

- `load_timing/nested_retained_pop`: the pinned compiler's
  `_lower_dynarray_pop` copies a receiver whose index can resize it and pops
  the copy, so the pop is lost; the source semantics pops the array itself.
  Since vyperlang/vyper#5280, after the pin, the compiler rejects such a pop.

## P8 (`raw_create` bytecode type)

- `create-builtins/rcr04_rawcreate_storage`

## P2 (calldata argument guard) + P4 (direct ABI encoder)

- `abi-codegen/enc_ensT_bytes`
- `create-builtins/cb06_blueprint_dyn_offset`
- `main/abi_dynamic`
- `main/abi_static`

## P2 (calldata argument guard) + P8 (`raw_create` bytecode type)

- `create-builtins/rcr01_rawcreate`
- `create-builtins/rcr03_rawcreate_rof`
- `create-builtins/rcr06_rawcreate_salt`

## P2 (calldata argument guard) + P4 (direct ABI encoder) + P8 (`raw_create` bytecode type)

- `create-builtins/rcr02_rawcreate_args_salt`
- `create-builtins/rcr05_rawcreate_args`
- `constructor-alias/ctor_alias`

## Not yet attributed

- `memory-stores/w01_return_intcall_dynarray_bytes_widen`

## Constant folding (#543), not #5127

- `raw-system/rl05_3topics_concat`: HOL hashes the literal `b"x"` at runtime
  with `KECCAK256`, while the pinned Python compiler embeds the constant hash.
  The retained `rl07_3topics_concat_nolit` fixture checks the nonliteral path.
  This remains outside exact bytecode parity until
  [#543](https://github.com/verifereum/vyper-hol/issues/543) supplies the same
  compile-time folding.
