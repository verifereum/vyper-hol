(*
 * Fuel bounds (fuel_ok) for the statement-level compile helpers that sit
 * above compile_stmt in stmtLowering: logs, reverts, returns, assignment
 * and tuple unpacking.  None of them writes a variable it did not allocate.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_log_save_arg, fuel_ok_compile_log_eval_all,
 *   fuel_ok_compile_log_topic_ops, fuel_ok_compile_log_store_data,
 *   fuel_ok_compile_revert_with_reason, fuel_ok_compile_reason_message,
 *   fuel_ok_compile_load_tuple_elements, fuel_ok_compile_mcopy_guard,
 *   fuel_ok_compile_internal_return, fuel_ok_compile_external_return,
 *   fuel_ok_compile_assign_value, fuel_ok_compile_tuple_load_all,
 *   fuel_ok_compile_store_at_loc, fuel_ok_compile_tuple_store_all,
 *   fuel_ok_compile_tuple_unpack, fuel_ok_compile_return_unlock,
 *   fuel_ok_compile_internal_return_from_env
 *)

Theory fragFuelStmtHelpers
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelLoopDynStorage
  fragFuelStmtBase stmtLowering fragFuelExpr fragFuelExprCfn
  fragFuelExprHelpers fragFuelBuiltins fragFuelAbi
  compileEnv emitHelper context venomInst
Libs
  fragFuelLib

(* compile_expr as a callback, in the shape the callback lemmas take *)
Theorem fuel_ok_compile_expr_cb[local]:
  !cenv ty e Wv E. fuel_ok Wv {} E (compile_expr cenv ty e)
Proof
  rpt gen_tac >> mp_tac fuel_ok_compile_expr >> simp[]
QED

Theorem fuel_ok_compile_get_target_ptr_ce[local]:
  !cenv bt Wv E.
    fuel_ok Wv {} E (compile_get_target_ptr compile_expr cenv bt)
Proof
  rpt gen_tac >> irule fuel_ok_compile_get_target_ptr >>
  simp[fuel_ok_compile_expr_cb]
QED

(* ===== Logs ===== *)

Theorem fuel_ok_compile_log_save_arg:
  !cenv src_ty op es Wv E.
    fuel_ok Wv {} E (compile_log_save_arg cenv src_ty op es)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_log_save_arg_def] >>
  fuel_auto [fuel_ok_compile_materialize_vv]
QED

Theorem fuel_ok_compile_log_eval_all:
  !cenv es Wv E. fuel_ok Wv {} E (compile_log_eval_all cenv es)
Proof
  Induct_on `es` >> rpt gen_tac
  >- simp[compile_log_eval_all_def, fuel_ok_return] >>
  simp_tac std_ss [compile_log_eval_all_def] >>
  first_x_assum (fn ih =>
    fuel_auto [ih, fuel_ok_lower_value_compile_expr,
               fuel_ok_compile_log_save_arg])
QED

Theorem fuel_ok_compile_log_topic_ops:
  !ops Wv E. fuel_ok Wv {} E (compile_log_topic_ops ops)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_log_topic_ops_def, fuel_ok_return] >>
  simp_tac std_ss [compile_log_topic_ops_def] >>
  first_x_assum (fn ih =>
    fuel_auto [ih, fuel_ok_context_misc])
QED

Theorem fuel_ok_compile_log_store_data:
  !cenv ops tys buf off Wv E.
    fuel_ok Wv {} E (compile_log_store_data cenv ops tys buf off)
Proof
  Induct_on `ops` >> rpt gen_tac >> Cases_on `tys`
  >- simp[compile_log_store_data_def, fuel_ok_return]
  >- (simp[compile_log_store_data_def] >>
      irule fuel_ok_emit_void_any >> simp[])
  >- (simp[compile_log_store_data_def] >>
      irule fuel_ok_emit_void_any >> simp[]) >>
  simp_tac std_ss [compile_log_store_data_def] >>
  first_x_assum (fn ih =>
    fuel_auto [ih, fuel_ok_emit_op, fuel_ok_compile_store_memory]) >>
  simp[is_terminator_def]
QED

(* ===== Reverts ===== *)

Theorem fuel_ok_compile_revert_with_reason:
  !cenv msg_vv msg_type msg_mem_size Wv E.
    fuel_ok Wv {} E
      (compile_revert_with_reason cenv msg_vv msg_type msg_mem_size)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_revert_with_reason_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_emit_inst_any,
             fuel_ok_compile_alloc_buffer, fuel_ok_unwrap_value] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_reason_message:
  !cenv e Wv E. fuel_ok Wv {} E (compile_reason_message cenv e)
Proof
  rpt gen_tac >> Cases_on `e` >>
  simp[compile_reason_message_def, fuel_ok_compile_expr_cb] >>
  rename1 `Literal t l` >> Cases_on `t` >>
  simp[compile_reason_message_def, fuel_ok_compile_expr_cb] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  simp[compile_reason_message_def, fuel_ok_compile_expr_cb] >>
  Cases_on `l` >>
  simp[compile_reason_message_def, fuel_ok_compile_expr_cb] >>
  fuel_auto [fuel_ok_compile_bytelike_literal]
QED

(* ===== Returns ===== *)

Theorem fuel_ok_compile_load_tuple_elements:
  !tys cenv base off Wv E.
    fuel_ok Wv {} E (compile_load_tuple_elements cenv base tys off)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_load_tuple_elements_def, fuel_ok_return] >>
  simp_tac std_ss [compile_load_tuple_elements_def] >>
  first_x_assum (fn ih => fuel_auto [ih, fuel_ok_emit_op]) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_mcopy_guard:
  !cenv supported Wv E.
    fuel_ok Wv {} E supported ==>
    fuel_ok Wv {} E (compile_mcopy_guard cenv supported)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_mcopy_guard_def] >>
  match_mp_tac fuel_ok_if >> conj_tac >> strip_tac
  >- first_assum ACCEPT_TAC >>
  irule fuel_ok_emit_inst_any >> simp[]
QED

Theorem fuel_ok_compile_internal_return:
  !cenv rv rpc cnt rty sty ets rbuf Wv E.
    fuel_ok Wv {} E
      (compile_internal_return cenv rv rpc cnt rty sty ets rbuf)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_internal_return_def] >>
  match_mp_tac fuel_ok_if >> conj_tac >> strip_tac
  >- (Cases_on `rv` >> simp_tac (srw_ss()) []
      >- (irule fuel_ok_emit_inst_any >> simp[]) >>
      match_mp_tac fuel_ok_if >> conj_tac >> strip_tac
      >- (irule fuel_ok_emit_inst_any >> simp[]) >>
      fuel_auto [fuel_ok_compile_load_tuple_elements] >>
      irule fuel_ok_emit_inst_any >> simp[]) >>
  Cases_on `rbuf` >> simp_tac (srw_ss()) []
  >- (irule fuel_ok_emit_inst_any >> simp[]) >>
  Cases_on `rv` >> simp_tac (srw_ss()) []
  >- (irule fuel_ok_emit_inst_any >> simp[]) >>
  fuel_auto [fuel_ok_compile_store_memory] >>
  irule fuel_ok_emit_inst_any >> simp[]
QED

Theorem fuel_ok_compile_return_unlock:
  !cenv Wv E. fuel_ok Wv {} E (compile_return_unlock cenv)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_return_unlock_def] >>
  Cases_on `cenv.ce_nonreentrant` >> rename1 `(a, rest)` >>
  PairCases_on `rest` >> PURE_REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  fuel_auto [fuel_ok_context_storage]
QED

Theorem fuel_ok_compile_external_return:
  !rv pw raw enc mx nr nkey tr view Wv E.
    fuel_ok Wv {} E
      (compile_external_return rv pw raw enc mx nr nkey tr view)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_external_return_def] >>
  Cases_on `rv` >> simp_tac (srw_ss()) [] >>
  fuel_auto [fuel_ok_context_storage, fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_emit_inst_any, fuel_ok_compile_alloc_buffer,
             fuel_ok_compile_abi_encode_to_buf] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_internal_return_from_env:
  !cenv ty sty val_op rpc Wv E.
    fuel_ok Wv {} E
      (compile_internal_return_from_env cenv ty sty val_op rpc)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_internal_return_from_env_def] >>
  Cases_on `cenv.ce_return_buf` >> TRY (rename1 `SOME x` >> Cases_on `x`) >>
  simp_tac (srw_ss()) [] >>
  fuel_auto [fuel_ok_compile_return_unlock, fuel_ok_compile_internal_return,
             fuel_ok_emit_op] >>
  simp[is_terminator_def]
QED

(* ===== Assignment ===== *)

Theorem fuel_ok_compile_store_at_loc:
  !imm dst v loc Wv E.
    fuel_ok Wv {} E (compile_store_at_loc imm dst v loc)
Proof
  rpt gen_tac >> Cases_on `loc` >>
  TRY (rename1 `SOME l` >> Cases_on `l`) >>
  simp[compile_store_at_loc_def, fuel_ok_compile_imm_store_word] >>
  irule fuel_ok_emit_void_any >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_assign_value:
  !cenv dst dloc v pw sloc dty sty dinfo msz Wv E.
    fuel_ok Wv {} E
      (compile_assign_value cenv dst dloc v pw sloc dty sty dinfo msz)
Proof
  rpt gen_tac >> Cases_on `dinfo` >>
  TRY (rename1 `SOME p` >> PairCases_on `p`) >>
  Cases_on `dloc` >> simp_tac (srw_ss()) [compile_assign_value_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_emit_inst_any,
             fuel_ok_compile_alloc_buffer, fuel_ok_compile_copy_memory,
             fuel_ok_compile_store_memory, fuel_ok_typed_memory_family,
             CONJUNCT1 fuel_ok_typed_memory_family,
             fuel_ok_compile_dynarray_to_storage,
             fuel_ok_compile_imm_store_word,
             fuel_ok_compile_store_immutable_bytestring,
             fuel_ok_compile_imm_store_words,
             fuel_ok_context_copies] >>
  simp[is_terminator_def]
QED

(* ===== Tuple unpacking ===== *)

Theorem fuel_ok_compile_tuple_load_all:
  !tys cenv src off Wv E.
    fuel_ok Wv {} E (compile_tuple_load_all cenv src tys off)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_tuple_load_all_def, fuel_ok_return] >>
  simp_tac std_ss [compile_tuple_load_all_def] >>
  first_x_assum (fn ih => fuel_auto [ih, fuel_ok_emit_op, fuel_ok_context_misc]) >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_tuple_store_all:
  !cenv tys ts vs Wv E.
    fuel_ok Wv {} E (compile_tuple_store_all cenv tys ts vs)
Proof
  recInduct compile_tuple_store_all_ind >> rpt conj_tac >> rpt gen_tac
  >- simp[compile_tuple_store_all_def, fuel_ok_return]
  >- (strip_tac >> simp_tac std_ss [compile_tuple_store_all_def] >>
      first_x_assum (fn ih =>
        fuel_auto [ih, fuel_ok_compile_get_target_ptr_ce,
                   fuel_ok_compile_store_at_loc,
                   fuel_ok_compile_assign_value, fuel_ok_emit_void_any]) >>
      simp[is_terminator_def])
  >- (strip_tac >> simp[compile_tuple_store_all_def] >>
      first_x_assum (fn ih => fuel_auto [ih, fuel_ok_emit_void_any]) >>
      simp[is_terminator_def]) >>
  simp[compile_tuple_store_all_def, fuel_ok_return]
QED

Theorem fuel_ok_compile_tuple_unpack:
  !cenv ty stage ts src Wv E.
    fuel_ok Wv {} E (compile_tuple_unpack cenv ty stage ts src)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_tuple_unpack_def] >>
  fuel_auto [fuel_ok_emit_inst_any, fuel_ok_emit_void_any,
             fuel_ok_compile_alloc_buffer, fuel_ok_compile_tuple_load_all,
             fuel_ok_compile_tuple_store_all] >>
  simp[is_terminator_def]
QED
