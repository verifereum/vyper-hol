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
- P9 constructor argument snapshot: a composite constructor argument is
  copied before a later argument that can modify memory or storage is
  evaluated (also a source-semantics change).

P1 (ceil32: `and(add(x, 31), not 31)`), P2 (dynamic external arguments
assert that their calldata offset isn't below 4, `_get_abi_arg_ptr`), P5 (a
slice's output buffer allocated after its bounds check), P3 (escaping
allocations: comparisons don't make an allocation escape, escaping static
allocations stay live everywhere and are allocated first) and P6 (eager call
arguments: internal- and external-call arguments are read as they are
evaluated, also a source-semantics change) and P7 (subscript overlap: an
array base derived through a dynamic-array element is copied before an index
that writes a variable the base reads or makes a risky call, also a
source-semantics change) are ported. P2 still heads sections below: two
fixtures that differ for other reasons, and those that also need P4 or P8.
A fixture listed under several changes needs all of them. The attribution
comes from reverting one change at a time in the pinned compiler and
recompiling. The creation fixtures' P4 entries are by elimination: P4 can't
be reverted on its own, and no revert of the other changes restores those
fixtures.

## P2 (calldata argument guard)

P2 is ported. These two still differ from the oracle with it:

- `raw-system/rl_const_topics`: the HOL checker rejects a constant
  `DynArray` as `raw_log` topics (only a literal list is accepted), as
  `raw_log_rejects_constant_topics` in `tests/vyperRawSystemTypingTestScript.sml`
  records.
- `raw-system/rr_local`: the HOL lowering sizes the `concat` result by its
  target's bound (40) where Python sums the argument bounds (10 + 10), which
  moves a later buffer from `0x40` to `0x60`. This isn't from #5127: main
  without P1 or P2 shows it too.

## P4 (direct ABI encoder)

- `abi-codegen/enc_multi`
- `create-builtins/cb02_blueprint_args`
- `create-builtins/cb05_blueprint_rof`
- `create-builtins/cb07_blueprint_args_salt`
- `external-calls/e25_arg_strlit_short`
- `external-calls/e36_arg_bytes_literal`
- `external-calls/e40_extcall_gas`
- `external-calls/e41_staticcall_gas`
- `external-calls/e42_extcall_gas_value_order`
- `external-calls/e43_extcall_all_kwargs`
- `external-calls/e44_skip_contract_check`
- `external-calls/e46_arg_storage_str`
- `external-calls/i02_iface_default_param`
- `external-calls/i03_two_ifaces_same_name`
- `external-calls/i09_iface_ret_iface`
- `external-calls/i13_ext_fn_before_iface`
- `external-calls/i15_iface_ret_iface_direct`
- `external-calls/m10c_iface_storage_main`
- `external-entries/base_dom1`
- `internal-frames/p74_int_ext_call`
- `main/event_log`
- `main/interface_calls`
- `main/mixed_event_log`
- `memory-stores/enc_in_assign`
- `raw-system/rr03_abi`

## Internal function order (#546), not #5127

- `load_timing/call_storage_read`: matches once its internal functions are
  emitted in Python's order; the function bodies already match.

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
- `external-calls/e26_arg_str_smaller`
- `external-calls/e27_arg_dyn_smaller`
- `main/abi_dynamic`
- `main/abi_static`
- `main/mixed_event_types`

## P2 (calldata argument guard) + P8 (`raw_create` bytecode type)

- `create-builtins/rcr01_rawcreate`
- `create-builtins/rcr03_rawcreate_rof`
- `create-builtins/rcr06_rawcreate_salt`

## P2 (calldata argument guard) + P4 (direct ABI encoder) + P8 (`raw_create` bytecode type)

- `create-builtins/rcr02_rawcreate_args_salt`
- `create-builtins/rcr05_rawcreate_args`

## P2 (calldata argument guard) + P4 (direct ABI encoder) + P8 (`raw_create` bytecode type) + P9 (constructor argument snapshot)

- `constructor-alias/ctor_alias`
