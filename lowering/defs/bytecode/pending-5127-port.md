# Fixtures pending the vyperlang/vyper#5127 port

Vyper `v0.5.0b1` (`VYPER_PIN`) changed the bytecode of the fixtures below,
mostly through vyperlang/vyper#5127, which rewrote ABI encoding and
allocation. Their oracles are regenerated at the pin, but the HOL compiler
still produces the previous bytes, so they are out of the bytecode-parity
checks (the `*_matches_python_oracle` theorems and the corpora's
`parity-fixtures.txt`) until the change that restores each is ported. Each port
puts its fixtures back and removes them from this list.

The changes, as they appear in the pinned Python compiler:

- P1 ceil32: `ceil32` rounds with `and(add(x, 31), not 31)`, used by bytestring
  copies and the encoder's `Bytes`/`String` length.
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

A fixture listed under several changes needs all of them. The attribution comes
from reverting one change at a time in the pinned compiler and recompiling.

## P1 (ceil32)

- `builtin-forms/p102_rbuf_bytes_ret_word_arg`
- `builtin-forms/slice_bytes32`
- `builtin-forms/uint2str_local`
- `external-calls/e04_ret_string`
- `external-calls/e05_ret_bytes`
- `external-calls/e37_default_ret_string`
- `internal-frames/p76_int_assert_raise`
- `main/assert_reason`
- `main/raise_reason`
- `memory-stores/a01_str_local_reassign`
- `memory-stores/c01_ctrl_str_local_decl`
- `memory-stores/c05_assign_empty_builtin_string`
- `memory-stores/c12_annassign_empty_bytes_ret`
- `memory-stores/empty_string_ret`
- `memory-stores/long_bytes_literal`
- `memory-stores/long_string_literal`
- `memory-stores/method_id_lit`
- `memory-stores/p16_return_tuple_bytes_widen`
- `memory-stores/r07_assert_storage_string_reason`
- `memory-stores/st_empty_ret`
- `memory-stores/t07_tuple_assign_string_elems`
- `memory-stores/t08_tuple_assign_ret_type_mismatch`
- `name-collisions/nm_redeclared_local`
- `phi-pointers/uint2str_arg`
- `raw-calls/rc02_outsize_ret`
- `raw-calls/rc04_static`
- `raw-calls/rc07_rof_false_tuple`
- `slice-buffers/slice_storage_bytes`

## P2 (calldata argument guard)

- `abi-codegen/arr_dyn_of_fixed`
- `abi-codegen/arr_string_arg`
- `abi-codegen/arr_struct_noclamp`
- `abi-codegen/dec_uint_unwrapT`
- `abi-codegen/flag256_array_arg`
- `abi-codegen/st_string_field_arg`
- `abi-codegen/tup_string_arg`
- `builtin-forms/extract32_addr`
- `builtin-forms/extract32_bytes4`
- `builtin-forms/extract32_default`
- `builtin-forms/extract32_int128`
- `builtin-forms/extract32_uint`
- `builtin-forms/len_bytes_arg`
- `builtin-forms/len_concat`
- `conversions/bys16_to_dec`
- `conversions/bys1_to_u8`
- `conversions/bys20_to_addr`
- `conversions/bys32_to_i8`
- `conversions/bys32_to_u8`
- `conversions/bys4_to_b4`
- `deep-dup/arr_dyn_of_dyn`
- `deep-dup/arr_fixed_of_dyn`
- `main/external_arrays`
- `main/scalar_convert_bytes_dynamic`
- `memory-stores/a12_local_dynarray_from_arg`
- `memory-stores/t03_tuple_assign_abi_decode`
- `memory-stores/t11_tuple_onew_decode_mem`
- `phi-pointers/ifexp_dynarray`
- `raw-calls/rc25_stmt_argdata`

## P1 (ceil32) + P2 (calldata argument guard)

- `abi-codegen/arr_string_ret`
- `abi-codegen/dec_bytes_unwrapT`
- `builtin-forms/concat_bytes2`
- `builtin-forms/concat_bytesn`
- `builtin-forms/concat_one_bytes_arg`
- `builtin-forms/concat_storage`
- `builtin-forms/concat_string3`
- `builtin-forms/concat_string3args`
- `builtin-forms/p103_rbuf_control_word_ret_concat_arg`
- `builtin-forms/p97_rbuf_stack_tuple_ret_concat_arg`
- `builtin-forms/struct_code_slice`
- `builtin-forms/struct_data_slice`
- `conversions/str_to_bys`
- `external-entries/dflt_bytes`
- `main/external_dynamic`
- `memory-stores/a02_bytes_local_from_arg`
- `memory-stores/c07_annassign_str_same_len`
- `memory-stores/dec_from_memory2`
- `memory-stores/e70_noData_live_mem2`
- `memory-stores/p15_local_append_bytes`
- `phi-pointers/ctl_ret_string_phi`
- `phi-pointers/ifexp_bytes`
- `phi-pointers/ifexp_string`
- `raw-calls/rc19_dyn_data`
- `raw-calls/rc29_delegate`
- `slice-buffers/slice_bytes_var`
- `slice-buffers/slice_string_lit`

## P1 (ceil32) + P3 (escaping allocas)

- `memory-stores/a11_local_string_from_intcall`

## P1 (ceil32) + P2 (calldata argument guard) + P3 (escaping allocas)

- `builtin-forms/p58_int_bytes_local`
- `builtin-forms/p94_rbuf_bytes_ret_concat_arg`
- `builtin-forms/p98_rbuf_mem_tuple_ret_concat_arg`
- `builtin-forms/p99_rbuf_string_ret_concat_arg`
- `internal-frames/p02_int_local_string`
- `internal-frames/p47_len_of_string_call`
- `main/internal_bytes_call`
- `memory-stores/p64_string_annassign_call`

## P1 (ceil32) + P5 (slice allocation order)

- `builtin-forms/ext_code_slice`
- `builtin-forms/self_code_slice`
- `slice-buffers/slice_msg_data`
- `slice-buffers/slice_msg_data_var`

## P4 (direct ABI encoder)

- `external-calls/e40_extcall_gas`
- `external-calls/e41_staticcall_gas`
- `external-calls/e42_extcall_gas_value_order`
- `external-calls/e43_extcall_all_kwargs`
- `external-calls/e44_skip_contract_check`
- `external-calls/i02_iface_default_param`
- `external-calls/i03_two_ifaces_same_name`
- `external-calls/i09_iface_ret_iface`
- `external-calls/i13_ext_fn_before_iface`
- `external-calls/i15_iface_ret_iface_direct`
- `external-calls/m10c_iface_storage_main`
- `internal-frames/p74_int_ext_call`
- `main/event_log`
- `main/interface_calls`
- `main/mixed_event_log`

## P1 (ceil32) + P4 (direct ABI encoder)

- `abi-codegen/enc_multi`
- `external-calls/e25_arg_strlit_short`
- `external-calls/e36_arg_bytes_literal`
- `external-calls/e46_arg_storage_str`
- `external-entries/base_dom1`
- `memory-stores/enc_in_assign`

## P2 (calldata argument guard) + P4 (direct ABI encoder)

- `external-calls/e27_arg_dyn_smaller`

## P1 (ceil32) + P2 (calldata argument guard) + P4 (direct ABI encoder)

- `abi-codegen/enc_ensT_bytes`
- `external-calls/e26_arg_str_smaller`
- `main/abi_dynamic`
- `main/abi_static`
- `main/mixed_event_types`

## P6 (eager call arguments)

- `load_timing/call_memory_pop`
- `load_timing/call_storage_read`

## P7 (subscript overlap)

- `load_timing/nested_retained_pop`
