(* Statement operations with equal inputs under shadow compilation. *)
Theory gasShadowCompileStmtOps
Ancestors
  gasShadowCompileStmtBase gasShadowCompileContext gasShadowCompileBase
  gasShadowState gasShadowCompileConvert gasShadowCompileAbi stmtLowering compileEnv context list

Theorem gas_shadow_compiles_log_topic_ops:
  !ops. gas_shadow_compiles (compile_log_topic_ops ops) (compile_log_topic_ops ops)
Proof
  Induct >> simp[compile_log_topic_ops_def, gas_shadow_compiles_bind,
    gas_shadow_compiles_return, gas_shadow_compiles_encode_log_topic]
QED

Theorem gas_shadow_compiles_log_store_data:
  !ops tys buf off. gas_shadow_compiles (compile_log_store_data cenv ops tys buf off)
    (compile_log_store_data cenv ops tys buf off)
Proof
  Induct >> Cases_on `tys` >> rpt gen_tac >>
  simp[compile_log_store_data_def, comp_ignore_bind_def,
       gas_shadow_compiles_return, gas_shadow_compiles_emit_void] >>
  irule gas_shadow_compiles_bind >> simp[gas_shadow_compiles_emit_op] >> gen_tac >>
  irule gas_shadow_compiles_bind >> simp[gas_shadow_compiles_store_memory]
QED

Theorem gas_shadow_compiles_revert_with_reason:
  gas_shadow_compiles (compile_revert_with_reason cenv vv ty nbytes)
    (compile_revert_with_reason cenv vv ty nbytes)
Proof
  simp[compile_revert_with_reason_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_emit_void,
               gas_shadow_compiles_unwrap_value] >> gen_tac) >>
  simp[gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_compiles_load_tuple_elements:
  !tys base off.
  gas_shadow_compiles (compile_load_tuple_elements cenv base tys off)
    (compile_load_tuple_elements cenv base tys off)
Proof
  Induct >> simp[compile_load_tuple_elements_def, gas_shadow_compiles_bind,
    gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_internal_return:
  gas_shadow_compiles (compile_internal_return cenv rv pc n ty sty etys rb)
    (compile_internal_return cenv rv pc n ty sty etys rb)
Proof
  Cases_on `rv` >> Cases_on `rb` >>
  simp[compile_internal_return_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
       gas_shadow_compiles_load_tuple_elements, gas_shadow_compiles_store_memory]
QED

Theorem gas_shadow_compiles_nonreentrant_unlock:
  gas_shadow_compiles (compile_nonreentrant_unlock nkey use_transient is_view)
    (compile_nonreentrant_unlock nkey use_transient is_view)
Proof
  Cases_on `is_view` >> Cases_on `use_transient` >>
  simp[compile_nonreentrant_unlock_def, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_return_unlock:
  gas_shadow_compiles (compile_return_unlock cenv) (compile_return_unlock cenv)
Proof
  simp[compile_return_unlock_def] >> pairarg_tac >>
  rw[gas_shadow_compiles_nonreentrant_unlock, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_external_return:
  gas_shadow_compiles (compile_external_return rv prim raw info max_size nr key transient view)
    (compile_external_return rv prim raw info max_size nr key transient view)
Proof
  Cases_on `rv` >> Cases_on `nr` >> Cases_on `raw` >> Cases_on `prim` >>
  simp[compile_external_return_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_nonreentrant_unlock, gas_shadow_compiles_emit_inst,
       gas_shadow_compiles_emit_void, gas_shadow_compiles_alloc_buffer,
       gas_shadow_compiles_abi_encode_to_buf]
QED

Theorem gas_shadow_compiles_tuple_load_all:
  !tys base off. gas_shadow_compiles (compile_tuple_load_all cenv base tys off)
    (compile_tuple_load_all cenv base tys off)
Proof
  Induct >> simp[compile_tuple_load_all_def, gas_shadow_compiles_bind,
    gas_shadow_compiles_return, gas_shadow_compiles_load_memory]
QED

Theorem gas_shadow_compiles_store_at_loc:
  gas_shadow_compiles (compile_store_at_loc imm dst v loc)
    (compile_store_at_loc imm dst v loc)
Proof
  Cases_on `loc` >> simp[compile_store_at_loc_def, gas_shadow_compiles_emit_void] >>
  rename1 `SOME l` >> Cases_on `l` >>
  simp[compile_store_at_loc_def, gas_shadow_compiles_emit_void,
       gas_shadow_compiles_imm_store_word]
QED

Theorem gas_shadow_compiles_range_bound_checks:
  gas_shadow_compiles (compile_range_bound_checks start end_op rounds bound signed)
    (compile_range_bound_checks start end_op rounds bound signed)
Proof
  Cases_on `signed` >>
  simp[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac) >>
  simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_iter_elem_copy:
  gas_shadow_compiles (compile_iter_elem_copy cenv elem item n loc slot ty ety)
    (compile_iter_elem_copy cenv elem item n loc slot ty ety)
Proof
  Cases_on `slot` >> Cases_on `loc` >>
  simp[compile_iter_elem_copy_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_slot_to_memory, gas_shadow_compiles_ptr_load,
       gas_shadow_compiles_emit_void, gas_shadow_compiles_copy_memory,
       gas_shadow_compiles_imm_copy_to_memory, gas_shadow_compiles_store_memory]
QED

Theorem gas_shadow_compiles_assign_value:
  gas_shadow_compiles (compile_assign_value cenv dst loc v prim src_loc ty sty da n)
    (compile_assign_value cenv dst loc v prim src_loc ty sty da n)
Proof
  Cases_on `loc`
  >- suspend "memory"
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code" >>
  simp[compile_assign_value_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst,
       gas_shadow_compiles_return]
QED

Resume gas_shadow_compiles_assign_value[memory]:
  Cases_on `prim` >> Cases_on `src_loc = SOME LocMemory` >>
  simp[compile_assign_value_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_void, gas_shadow_compiles_alloc_buffer,
       gas_shadow_compiles_copy_memory, gas_shadow_compiles_store_memory]
QED

Resume gas_shadow_compiles_assign_value[storage]:
  simp[compile_assign_value_def, comp_ignore_bind_def] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (IF_CASES_TAC >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
           gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_store_memory_typed]) >>
  gen_tac >> Cases_on `prim` >>
  simp[gas_shadow_compiles_emit_void] >>
  Cases_on `da`
  >- (Cases_on `(if is_bytestring_type ty then type_memory_bytes cenv sty else n) <= 32` >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
           gas_shadow_compiles_emit_void, gas_shadow_compiles_memory_to_storage]) >>
  rename1 `SOME p` >> PairCases_on `p` >>
  simp[gas_shadow_compiles_dynarray_to_storage]
QED

Resume gas_shadow_compiles_assign_value[transient]:
  simp[compile_assign_value_def, comp_ignore_bind_def] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (IF_CASES_TAC >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
           gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_store_memory_typed]) >>
  gen_tac >> Cases_on `prim` >>
  simp[gas_shadow_compiles_emit_void] >>
  Cases_on `da`
  >- (Cases_on `(if is_bytestring_type ty then type_memory_bytes cenv sty else n) <= 32` >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
           gas_shadow_compiles_emit_void, gas_shadow_compiles_memory_to_transient]) >>
  rename1 `SOME p` >> PairCases_on `p` >>
  simp[gas_shadow_compiles_dynarray_to_storage]
QED

Resume gas_shadow_compiles_assign_value[code]:
  simp[compile_assign_value_def, comp_ignore_bind_def] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (IF_CASES_TAC >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
           gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_store_memory_typed]) >>
  gen_tac >> Cases_on `prim` >>
  Cases_on `(if is_bytestring_type ty then type_memory_bytes cenv sty else n) <= 32` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_imm_store_word,
       gas_shadow_compiles_imm_store_words]
QED

Finalise gas_shadow_compiles_assign_value

Theorem gas_shadow_compiles_internal_return_from_env:
  gas_shadow_compiles (compile_internal_return_from_env cenv ty sty v rpc)
    (compile_internal_return_from_env cenv ty sty v rpc)
Proof
  simp[compile_internal_return_from_env_def, comp_ignore_bind_def] >>
  ho_match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_return_unlock] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `cenv.ce_return_buf` >>
      simp[gas_shadow_compiles_return] >>
      rename1 `SOME loc` >> Cases_on `loc` >>
      simp[gas_shadow_compiles_bind, gas_shadow_compiles_return]) >>
  gen_tac >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_internal_return]
QED
