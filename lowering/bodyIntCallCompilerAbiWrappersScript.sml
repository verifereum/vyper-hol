Theory bodyIntCallCompilerAbiWrappers
Ancestors
  bodyIntCallCompilerEncoder bodyIntCallCompilerDecoder
  bodyIntCallCompilerAggregate bodyIntCallCompilerTypedMemory
  bodyIntCallCompilerUnwrap bodyIntCallCompilerContext
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit builtinAbi exprLowering compileEnv

Theorem intcall_interval_lower_abi_encode:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (lower_abi_encode tup mid src info maxlen a))
Proof
  strip_tac >> Cases_on `mid` >>
  simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_op, intcall_interval_emit_void,
            cj 2 intcall_interval_encode_family])
QED

Theorem intcall_interval_lower_abi_decode:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (lower_abi_decode data info lo hi sz a))
Proof
  strip_tac >> Cases_on `lo = hi` >>
  simp[lower_abi_decode_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_return,
            intcall_interval_emit_op, intcall_interval_emit_void,
            cj 1 intcall_interval_decode_family])
QED

Theorem intcall_interval_store_abi_tuple:
  !vs cenv buf off k a. k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_store_abi_tuple cenv buf off vs a))
Proof
  Induct >> simp[compile_store_abi_tuple_def, intcall_interval_return] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  Cases_on `is_word_type h1` >>
  simp[compile_store_abi_tuple_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_copy_memory])
QED

Theorem intcall_interval_materialize_vv:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_materialize_vv cenv ty vv a))
Proof
  strip_tac >> simp[compile_materialize_vv_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_unwrap_value,
            intcall_interval_store_memory, intcall_interval_return])
QED

Theorem intcall_interval_pure_abi_encode_args:
  (!ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es a. EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_abi_encode_args cfn cenv es a))
Proof
  strip_tac >> Induct >>
  simp[compile_abi_encode_args_def, intcall_interval_return] >>
  rpt strip_tac >> Cases_on `~is_word_type (expr_type h) /\ exprs_can_mutate cenv es` >>
  simp[] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_materialize_vv, intcall_interval_unwrap_value,
            intcall_interval_return])
QED
