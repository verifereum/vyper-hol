(* Allocation windows are preserved by statement lowering and typed stores. *)
Theory runtimePeakMemoryStmtOps
Ancestors
  runtimePeakMemoryControl runtimePeakMemoryExpr
  runtimePeakMemoryBuiltins runtimePeakMemoryArity runtimePeakMemoryCode runtimePeakMemoryAbi
  stmtLowering exprLowering supportedStmtTraverse supportedExprTraverse
  compileEnv context emitHelper venomInst vyperAST list finite_map

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer, dalloca_windows_ptr_access,
      dalloca_windows_lower_value, dalloca_windows_unwrap_value])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

Theorem dalloca_windows_store_slots[local]:
  (!cenv src slot ty tr.
     preserves_dalloca_windows window (compile_store_slots cenv src slot ty tr)) /\
  (!cenv src slot members mo so tr.
     preserves_dalloca_windows window
       (compile_store_slots_members cenv src slot members mo so tr)) /\
  (!cenv src slot elem n tr.
     preserves_dalloca_windows window
       (compile_copy_elements_to_slots cenv src slot elem n tr))
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  simp[Once compile_store_slots_def, compile_memory_to_storage_def,
       compile_memory_to_transient_def, compile_word_copy_loop_def,
       compile_word_copy_loop_op_def, compile_bytestring_word_count_def,
       compile_lit_byte_offset_def] >>
  windows_tac [dalloca_windows_word_copy, compile_memory_to_storage_def,
       compile_memory_to_transient_def, compile_word_copy_loop_def,
       compile_word_copy_loop_op_def] >> gvs[] >>
  metis_tac[]
QED

Theorem dalloca_windows_imm_store_words[local]:
  !n off. preserves_dalloca_windows window (compile_imm_store_words imm src dst n off)
Proof
  Induct >> simp[compile_imm_store_words_def, dalloca_windows_return] >>
  windows_tac [compile_lit_byte_offset_def, dalloca_windows_imm_store]
QED

Theorem dalloca_windows_assign_value:
  preserves_dalloca_windows window
    (compile_assign_value cenv dst loc v prim src_loc dst_ty src_ty sz)
Proof
  Cases_on `loc` >> simp[compile_assign_value_def] >>
  windows_tac [dalloca_windows_store_memory, dalloca_windows_store_memory_typed,
    dalloca_windows_copy_memory, dalloca_windows_store_slots,
    dalloca_windows_imm_store, dalloca_windows_imm_store_words,
    compile_store_immutable_bytestring_def, compile_bytestring_word_count_def,
    dalloca_windows_word_copy]
QED

Theorem dalloca_windows_store_at_loc:
  preserves_dalloca_windows window (compile_store_at_loc imm dst v loc_opt)
Proof
  Cases_on `loc_opt` >> TRY (rename1 `SOME loc` >> Cases_on `loc`) >>
  simp[compile_store_at_loc_def, dalloca_windows_imm_store, dalloca_windows_emit_helpers]
QED

Theorem dalloca_windows_nonreentrant:
  preserves_dalloca_windows window (compile_nonreentrant_lock key tr view) /\
  preserves_dalloca_windows window (compile_nonreentrant_unlock key tr view)
Proof
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def] >>
  conj_tac >> windows_tac []
QED

Theorem dalloca_windows_return_unlock:
  preserves_dalloca_windows window (compile_return_unlock cenv)
Proof
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  fs[markerTheory.Abbrev_def, GSYM markerTheory.Abbrev_def] >>
  simp[compile_return_unlock_def] >>
  pairarg_tac >> fs[] >> windows_tac [dalloca_windows_nonreentrant]
QED

Theorem dalloca_windows_load_tuple_elements[local]:
  !tys off. preserves_dalloca_windows window (compile_load_tuple_elements cenv src_op tys off)
Proof
  Induct >> simp[compile_load_tuple_elements_def, dalloca_windows_return] >>
  windows_tac []
QED

Theorem dalloca_windows_internal_return[local]:
  preserves_dalloca_windows window
    (compile_internal_return cenv rv pc n ty src_ty tys buf)
Proof
  simp[compile_internal_return_def] >>
  windows_tac [dalloca_windows_store_memory, dalloca_windows_load_tuple_elements]
QED

Theorem dalloca_windows_internal_return_from_env:
  preserves_dalloca_windows window (compile_internal_return_from_env cenv ty src_ty v pc)
Proof
  simp[compile_internal_return_from_env_def] >>
  windows_tac [dalloca_windows_return_unlock, dalloca_windows_internal_return]
QED

Theorem dalloca_windows_external_return:
  preserves_dalloca_windows window
    (compile_external_return rv prim raw enc_info sz nr key tr view)
Proof
  simp[compile_external_return_def] >>
  windows_tac [dalloca_windows_nonreentrant, dalloca_windows_abi_encode]
QED

Theorem dalloca_windows_dynarray_append:
  preserves_dalloca_windows window
    (compile_dynarray_append cenv base_op v stride sz dst_ty src_ty cap prim loc)
Proof
  simp[compile_dynarray_append_def] >>
  windows_tac [dalloca_windows_store_memory, dalloca_windows_store_slots,
               dalloca_windows_imm_store_words]
QED

Theorem dalloca_windows_tuple_load_all[local]:
  !tys off. preserves_dalloca_windows window (compile_tuple_load_all cenv src tys off)
Proof
  Induct >> simp[compile_tuple_load_all_def, dalloca_windows_return] >>
  windows_tac [compile_load_memory_def]
QED

Theorem dalloca_windows_tuple_store_all[local]:
  !tys targets vals.
    (!bt. MEM (BaseTarget bt) targets ==>
      preserves_dalloca_windows window (compile_get_target_ptr compile_expr cenv bt)) ==>
    preserves_dalloca_windows window (compile_tuple_store_all cenv tys targets vals)
Proof
  Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, dalloca_windows_return] >>
  rename1 `target::targets` >> Cases_on `target` >>
  simp[compile_tuple_store_all_def] >> rpt strip_tac >>
  windows_tac [dalloca_windows_store_at_loc, dalloca_windows_assign_value] >>
  metis_tac[]
QED

Theorem dalloca_windows_tuple_unpack:
  (!bt. MEM (BaseTarget bt) targets ==>
    preserves_dalloca_windows window (compile_get_target_ptr compile_expr cenv bt)) ==>
  preserves_dalloca_windows window (compile_tuple_unpack cenv ty stage targets src)
Proof
  strip_tac >> simp[compile_tuple_unpack_def] >>
  windows_tac [dalloca_windows_tuple_load_all, dalloca_windows_tuple_store_all] >>
  metis_tac[dalloca_windows_tuple_store_all]
QED

Theorem dalloca_windows_revert_with_reason:
  preserves_dalloca_windows window (compile_revert_with_reason cenv msg ty sz)
Proof
  simp[compile_revert_with_reason_def] >> windows_tac []
QED

Theorem dalloca_windows_reason_message:
  preserves_dalloca_windows window (compile_expr cenv (expr_type e) e) ==>
  preserves_dalloca_windows window (compile_reason_message cenv e)
Proof
  Cases_on `e` >>
  TRY (rename1 `Literal ty l` >> Cases_on `ty` >>
       TRY (rename1 `BaseT b` >> Cases_on `b` >> Cases_on `l`)) >>
  simp[compile_reason_message_def] >> rpt strip_tac >> windows_tac [dalloca_windows_bytelike_literal]
QED

Theorem dalloca_windows_revert_with_custom_error:
  (!e. MEM e (custom_error_exprs err) ==>
       preserves_dalloca_windows window (compile_expr cenv (expr_type e) e)) ==>
  preserves_dalloca_windows window (compile_revert_with_custom_error cenv err)
Proof
  Cases_on `err` >>
  simp[compile_revert_with_custom_error_def] >> rpt strip_tac >>
  windows_tac [dalloca_windows_abi_encode_values] >>
  irule dalloca_windows_ext_call_args >> simp[]
QED

Theorem dalloca_windows_log_saved_topics:
  !vs. preserves_dalloca_windows window (compile_log_saved_topics cenv vs)
Proof
  Induct >> rpt gen_tac >> TRY (PairCases_on `h`) >>
  simp[compile_log_saved_topics_def, dalloca_windows_return] >>
  windows_tac [compile_encode_log_topic_def, dalloca_windows_hash_ops]
QED
