# Fixtures pending the vyperlang/vyper#5127 port

Vyper `v0.5.0b1` (`VYPER_PIN`) changed the bytecode of the fixtures below,
mostly through vyperlang/vyper#5127, which rewrote ABI encoding and
allocation. Their oracles are regenerated at the pin, but the HOL compiler
still produces the previous bytes, so they are out of the bytecode-parity
checks (the native runner and the corpora's
`parity-fixtures.txt`) until the change that restores each is ported. Each port
puts its fixtures back and removes them from this list.

The changes, as they appear in the pinned Python compiler:

- P2 calldata argument guard: dynamic external arguments assert that their
  calldata offset isn't below 4 (`_get_abi_arg_ptr`).
- P3 escaping allocas: comparisons don't make an allocation escape; escaping
  static allocations stay live everywhere; allocation order sorts escaping ones
  first.
- P4 direct ABI encoder: values are encoded straight into the destination
  buffer, and an external call sends exactly the encoded length plus 4 bytes.
- P5 slice allocation order: a slice's output buffer is allocated after its
  bounds check.
- P6 eager call arguments: internal- and external-call arguments are read as
  they are evaluated (also a source-semantics change).
- P7 subscript overlap: a dynamic array's base is copied when the index
  expression can modify it (also a source-semantics change).
- P8 `raw_create` bytecode type: `raw_create` types its bytecode argument
  with the argument's own type rather than `Bytes[49152]`, which sizes its
  initcode buffer (the HOL lowering still snapshots 49152 bytes).
- P9 constructor argument snapshot: a composite constructor argument is
  copied before a later argument that can modify memory or storage is
  evaluated (also a source-semantics change).

P1 (ceil32: `and(add(x, 31), not 31)`) is ported, so it no longer appears
below. A fixture listed under several changes needs all of them. The
attribution comes from reverting one change at a time in the pinned compiler
and recompiling. The creation fixtures' P4 entries are by elimination: P4 can't
be reverted on its own, and no revert of the other changes restores those
fixtures.

## P2 (calldata argument guard)

- `abi-codegen/arr_dyn_of_fixed`
- `abi-codegen/arr_string_arg`
- `abi-codegen/arr_string_ret`
- `abi-codegen/arr_struct_noclamp`
- `abi-codegen/dec_bytes_unwrapT`
- `abi-codegen/dec_uint_unwrapT`
- `abi-codegen/flag256_array_arg`
- `abi-codegen/st_string_field_arg`
- `abi-codegen/tup_string_arg`
- `builtin-forms/concat_bytes2`
- `builtin-forms/concat_bytesn`
- `builtin-forms/concat_one_bytes_arg`
- `builtin-forms/concat_storage`
- `builtin-forms/concat_string3`
- `builtin-forms/concat_string3args`
- `builtin-forms/extract32_addr`
- `builtin-forms/extract32_bytes4`
- `builtin-forms/extract32_default`
- `builtin-forms/extract32_int128`
- `builtin-forms/extract32_uint`
- `builtin-forms/len_bytes_arg`
- `builtin-forms/len_concat`
- `builtin-forms/p103_rbuf_control_word_ret_concat_arg`
- `builtin-forms/p97_rbuf_stack_tuple_ret_concat_arg`
- `builtin-forms/struct_code_slice`
- `builtin-forms/struct_data_slice`
- `conversions/bys16_to_dec`
- `conversions/bys1_to_u8`
- `conversions/bys20_to_addr`
- `conversions/bys32_to_i8`
- `conversions/bys32_to_u8`
- `conversions/bys4_to_b4`
- `conversions/str_to_bys`
- `create-builtins/cb03_blueprint_rawargs`
- `deep-dup/arr_dyn_of_dyn`
- `deep-dup/arr_fixed_of_dyn`
- `external-entries/dflt_bytes`
- `main/external_arrays`
- `main/external_dynamic`
- `main/scalar_convert_bytes_dynamic`
- `memory-stores/a02_bytes_local_from_arg`
- `memory-stores/a12_local_dynarray_from_arg`
- `memory-stores/c07_annassign_str_same_len`
- `memory-stores/dec_from_memory2`
- `memory-stores/e70_noData_live_mem2`
- `memory-stores/p15_local_append_bytes`
- `memory-stores/t03_tuple_assign_abi_decode`
- `memory-stores/t11_tuple_onew_decode_mem`
- `phi-pointers/ctl_ret_string_phi`
- `phi-pointers/ifexp_bytes`
- `phi-pointers/ifexp_dynarray`
- `phi-pointers/ifexp_string`
- `raw-calls/rc19_dyn_data`
- `raw-calls/rc25_stmt_argdata`
- `raw-calls/rc29_delegate`
- `raw-system/rl03_4topics`
- `raw-system/rl_const_topics`
- `raw-system/rr02_dynamic`
- `raw-system/rr04_terminus_ret`
- `raw-system/rr_arg`
- `raw-system/rr_local`
- `raw-system/rr_nr`
- `slice-buffers/slice_bytes_var`
- `slice-buffers/slice_string_lit`

## P3 (escaping allocas)

- `memory-stores/a11_local_string_from_intcall`

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

## P5 (slice allocation order)

- `builtin-forms/ext_code_slice`
- `builtin-forms/self_code_slice`
- `slice-buffers/slice_msg_data_var`
- `slice-buffers/slice_msg_data`

## P6 (eager call arguments)

- `load_timing/call_memory_pop`
- `load_timing/call_storage_read`

## P7 (subscript overlap)

- `load_timing/nested_retained_pop`

## P8 (`raw_create` bytecode type)

- `create-builtins/rcr04_rawcreate_storage`

## P2 (calldata argument guard) + P3 (escaping allocas)

- `builtin-forms/p58_int_bytes_local`
- `builtin-forms/p94_rbuf_bytes_ret_concat_arg`
- `builtin-forms/p98_rbuf_mem_tuple_ret_concat_arg`
- `builtin-forms/p99_rbuf_string_ret_concat_arg`
- `internal-frames/p02_int_local_string`
- `internal-frames/p47_len_of_string_call`
- `main/internal_bytes_call`
- `memory-stores/p64_string_annassign_call`

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

## Not yet attributed

- `memory-stores/w01_return_intcall_dynarray_bytes_widen`
