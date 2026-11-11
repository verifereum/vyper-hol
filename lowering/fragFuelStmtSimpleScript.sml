(*
 * Fuel bounds for the statements that contain no other statement: every
 * compile_stmt case except If and For.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_stmt_simple
 *)

Theory fragFuelStmtSimple
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelStmtBase
  fragFuelStmtHelpers fragFuelExpr fragFuelExprCfn fragFuelExprHelpers
  fragFuelAbi stmtLowering exprLowering compileEnv emitHelper context
  venomInst
Libs
  fragFuelLib

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

Theorem fuel_ok_ld_st_opc[local]:
  !loc. ~is_terminator (load_opc_for loc) /\ load_opc_for loc <> PHI /\
        ~is_terminator (store_opc_for loc) /\ store_opc_for loc <> PHI
Proof
  Cases >> simp[load_opc_for_def, store_opc_for_def, is_terminator_def]
QED

Theorem fuel_ok_stmt_annassign[local]:
  !cenv lctx ty id vtyp e Wv E.
    cenv_ptrs_in Wv cenv ==>
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (AnnAssign id vtyp e))
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [compile_stmt_def] >>
  Cases_on `FLOOKUP cenv.ce_vars id` >>
  TRY (rename1 `SOME x` >> Cases_on `x`) >>
  simp_tac (srw_ss()) [] >>
  fuel_auto [fuel_ok_emit_local_alloca, fuel_ok_compile_expr_cb,
             fuel_ok_unwrap_value, fuel_ok_emit_void_any,
             fuel_ok_compile_assign_value] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_stmt_assign_base[local]:
  !cenv lctx ty bt e Wv E.
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (Assign (BaseTarget bt) e))
Proof
  rpt gen_tac >> simp_tac std_ss [compile_stmt_def] >>
  match_mp_tac fuel_ok_if >> conj_tac >> strip_tac
  >- fuel_auto [fuel_ok_compile_get_target_ptr_ce,
                fuel_ok_compile_store_at_loc] >>
  Cases_on `dst_loc_opt` >> simp_tac (srw_ss()) [] >>
  fuel_auto [fuel_ok_compile_expr_cb, fuel_ok_compile_snapshot_vv,
             fuel_ok_compile_get_target_ptr_ce, fuel_ok_unwrap_value,
             fuel_ok_compile_assign_value, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_stmt_assign_tuple[local]:
  !cenv lctx ty ts e Wv E.
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (Assign (TupleTarget ts) e))
Proof
  rpt gen_tac >> simp_tac std_ss [compile_stmt_def] >>
  fuel_auto [fuel_ok_compile_expr_cb, fuel_ok_unwrap_value,
             fuel_ok_compile_tuple_unpack]
QED

Theorem fuel_ok_stmt_augassign[local]:
  !cenv lctx ty tty bt bop e Wv E.
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (AugAssign tty bt bop e))
Proof
  rpt gen_tac >> simp_tac std_ss [compile_stmt_def] >>
  fuel_auto [fuel_ok_compile_get_target_ptr_ce] >>
  Cases_on `FST (SND tgt_result)` >> simp_tac (srw_ss()) [] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_lower_value_compile_expr, fuel_ok_compile_binop] >>
  simp[is_terminator_def] >> Cases_on `x` >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_stmt_assert[local]:
  !cenv lctx ty c r Wv E.
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (Assert c r))
Proof
  rpt gen_tac >> Cases_on `r` >> simp_tac std_ss [compile_stmt_def] >>
  fuel_auto [fuel_ok_lower_value_compile_expr, fuel_ok_emit_inst_any,
             fuel_ok_emit_inst_jnz, fuel_ok_compile_reason_message,
             fuel_ok_compile_revert_with_reason] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_stmt_raise[local]:
  !cenv lctx ty r Wv E.
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (Raise r))
Proof
  rpt gen_tac >> Cases_on `r` >> simp_tac std_ss [compile_stmt_def] >>
  fuel_auto [fuel_ok_emit_inst_any, fuel_ok_compile_reason_message,
             fuel_ok_compile_revert_with_reason] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_stmt_log[local]:
  !cenv lctx ty ev args Wv E.
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (Log ev args))
Proof
  rpt gen_tac >> simp_tac std_ss [compile_stmt_def] >>
  Cases_on `cenv.ce_event_info (nsid_to_string ev)` >>
  TRY (rename1 `SOME x` >> PairCases_on `x`) >>
  simp_tac (srw_ss()) [] >>
  fuel_auto [fuel_ok_emit_inst_any, fuel_ok_emit_op,
             fuel_ok_compile_log_eval_all, fuel_ok_compile_log_topic_ops,
             fuel_ok_compile_log_store_data, fuel_ok_compile_alloc_buffer,
             fuel_ok_compile_abi_encode_to_buf] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_stmt_return_none[local]:
  !cenv lctx ty Wv E.
    stmt_exits_in E cenv lctx ==>
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (Return NONE))
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [compile_stmt_def] >>
  Cases_on `cenv.ce_return_pc` >>
  TRY (rename1 `SOME x` >> Cases_on `x`) >>
  simp_tac (srw_ss()) []
  >- (Cases_on `cenv.ce_ctor_exit_label` >> simp_tac (srw_ss()) []
      >- (Cases_on `cenv.ce_nonreentrant` >> rename1 `(a, rest)` >>
          PairCases_on `rest` >> simp_tac (srw_ss()) [] >>
          fuel_auto [fuel_ok_context_storage, fuel_ok_emit_inst_any] >>
          simp[])
      >- (irule fuel_ok_emit_inst_jmp >> fs[stmt_exits_in_def]))
  >- (fuel_auto [fuel_ok_compile_return_unlock, fuel_ok_emit_op,
                 fuel_ok_emit_inst_any] >> simp[])
  >- (Cases_on `cenv.ce_ctor_exit_label` >> simp_tac (srw_ss()) []
      >- (Cases_on `cenv.ce_nonreentrant` >> rename1 `(a, rest)` >>
          PairCases_on `rest` >> simp_tac (srw_ss()) [] >>
          fuel_auto [fuel_ok_context_storage, fuel_ok_emit_inst_any] >>
          simp[])
      >- (irule fuel_ok_emit_inst_jmp >> fs[stmt_exits_in_def])) >>
  fuel_auto [fuel_ok_compile_return_unlock, fuel_ok_emit_inst_any] >> simp[]
QED

Theorem fuel_ok_stmt_return_some[local]:
  !cenv lctx ty e Wv E.
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (Return (SOME e)))
Proof
  rpt gen_tac >> simp_tac std_ss [compile_stmt_def] >>
  match_mp_tac fuel_ok_bind0 >> conj_tac
  >- simp[fuel_ok_lower_value_compile_expr] >>
  gen_tac >> BETA_TAC >>
  Cases_on `cenv.ce_return_pc` >>
  TRY (rename1 `SOME x` >> Cases_on `x`) >>
  simp_tac (srw_ss()) []
  >- (fuel_auto [fuel_ok_compile_alloc_buffer,
                 fuel_ok_compile_store_memory_typed,
                 fuel_ok_compile_store_memory,
                 fuel_ok_context_storage, fuel_ok_compile_external_return] >>
      simp[is_terminator_def])
  >- (fuel_auto [fuel_ok_emit_op, fuel_ok_compile_internal_return_from_env] >>
      simp[is_terminator_def])
  >- (fuel_auto [fuel_ok_compile_internal_return_from_env])
  >- (fuel_auto [fuel_ok_compile_alloc_buffer,
                 fuel_ok_compile_store_memory_typed,
                 fuel_ok_compile_store_memory,
                 fuel_ok_context_storage, fuel_ok_compile_external_return] >>
      simp[is_terminator_def]) >>
  fuel_auto [fuel_ok_compile_alloc_buffer,
             fuel_ok_compile_store_memory_typed,
             fuel_ok_context_storage, fuel_ok_compile_external_return] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_stmt_append[local]:
  !cenv lctx ty tgt e Wv E.
    fuel_ok Wv {} E (compile_stmt cenv lctx ty (Append tgt e))
Proof
  rpt gen_tac >> simp_tac std_ss [compile_stmt_def] >>
  fuel_auto [fuel_ok_lower_value_compile_expr, fuel_ok_compile_alloc_buffer,
             fuel_ok_compile_store_memory, fuel_ok_compile_dynarray_append] >>
  simp[fuel_ok_ld_st_opc]
QED

Theorem fuel_ok_compile_stmt_simple:
  !cenv lctx ty s Wv E.
    (!c tb eb. s <> If c tb eb) /\
    (!id fty it bound body. s <> For id fty it bound body) /\
    cenv_ptrs_in Wv cenv /\ stmt_exits_in E cenv lctx ==>
    fuel_ok Wv {} E (compile_stmt cenv lctx ty s)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `s`
  >- simp[compile_stmt_def, fuel_ok_return]
  >- (Cases_on `lctx` >> fs[stmt_exits_in_def] >>
      simp[compile_stmt_def, fuel_ok_emit_inst_any, is_terminator_def] >>
      (* Continue: a jump to the loop's continue label, in E *)
      irule fuel_ok_emit_inst_jmp >> simp[])
  >- (Cases_on `lctx` >> fs[stmt_exits_in_def] >>
      simp[compile_stmt_def, fuel_ok_emit_inst_any, is_terminator_def] >>
      irule fuel_ok_emit_inst_jmp >> simp[])
  >- (simp[compile_stmt_def] >> fuel_auto [fuel_ok_compile_expr_cb])
  >- fs[]
  >- fs[]
  >- simp[fuel_ok_stmt_assert]
  >- simp[fuel_ok_stmt_log]
  >- simp[fuel_ok_stmt_raise]
  >- (Cases_on `o'` >> simp[fuel_ok_stmt_return_none, fuel_ok_stmt_return_some])
  >- (Cases_on `a` >> simp[fuel_ok_stmt_assign_base, fuel_ok_stmt_assign_tuple])
  >- simp[fuel_ok_stmt_augassign]
  >- simp[fuel_ok_stmt_append] >>
  simp[fuel_ok_stmt_annassign]
QED
