(* The explicit read preserves the complete expression frame. *)
Theory msgGasPost
Ancestors
  msgGasSim gasSummary exprSim exprSimHyps exprLoweringProps
  exprLowering emitHelperProps compileEnv loweringSlice
  vyperInterpreter vyperState venomState

Theorem msg_gas_typed[local]:
  expr_sim_pre cenv cx env (Builtin ann (Env MsgGas) args) es ==>
  ann = env_item_type MsgGas /\ args = []
Proof
  simp[expr_sim_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[]
QED

Theorem msg_gas_source[local]:
  bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
       (read_result cx) (es with gas_obs := w::tail) =
    (INL (IntV (&w2n w)), es with gas_obs := tail)
Proof
  once_rewrite_tac[evaluate_def] >>
  simp[vyperContextTheory.builtin_args_length_ok_def, bind_def, ignore_bind_def,
       type_check_def, check_def, assert_def, return_def,
       next_gas_reading_def, read_result_def]
QED

Theorem msg_gas_state_frame[local]:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with gas_obs := gs)
    (s with <|vs_gas_readings := readings; vs_inst_idx := k|>)
Proof
  strip_tac >>
  gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def, accounts_rel_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem msg_gas_post_frame[local]:
  compile_env_var MsgGas sa = (Var out,sb) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 ==>
  expr_post ctx func cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    es sa sb s0 (es with gas_obs := []) (IntV (&w2n w)) (Var out)
    (update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>))
Proof
  strip_tac >>
  `out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[compile_env_var_def, emitHelperTheory.emit_op_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
        emit_def] >>
  `not_local_ptr cenv (es with gas_obs := []).scopes out` by
    (gvs[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
    (update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>))` by
    (irule stmt_state_rel_update_var >> simp[] >>
     drule msg_gas_state_frame >>
     disch_then (qspecl_then [`DROP 1 s0.vs_gas_readings`,
                            `LENGTH sb.cs_current_insts`, `[]`] mp_tac) >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, vyperTypeSystemTheory.env_item_type_def,
       is_word_type_def, eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, typed_val_to_w256_word_value,
       word_value_def, locals_kept_mem] >>
  conj_tac
  >- simp[valueEncodingTheory.val_to_w256_def] >>
  rpt strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <> x` by
    (strip_tac >> gvs[not_fresh_at_def]) >> simp[]
QED

Theorem compile_msg_gas_post:
  !ctx func cenv cx env ty ann args es sa sb op s0.
    expr_sim_pre cenv cx env (Builtin ann (Env MsgGas) args) es /\
    lower_value compile_expr cenv ty (Builtin ann (Env MsgGas) args) sa =
      (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_summary_at (ctx, func) [T]
      (bind (eval_expr cx (Builtin ann (Env MsgGas) args)) (read_result cx))
      (es, s0)
      (\res ee t.
         (?v. res = INL v /\
              expr_post ctx func cenv cx (Builtin ann (Env MsgGas) args)
                es sa sb s0 ee v op t) /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. F)
Proof
  rpt strip_tac >> drule msg_gas_typed >> strip_tac >> gvs[] >>
  drule lower_value_env >> strip_tac >>
  drule_all compile_msg_gas_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `expr_post ctx func cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    es sa sb s0 (es with gas_obs := []) (IntV (&w2n w)) (Var out)
    (update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>))` by
    (irule msg_gas_post_frame >> simp[]) >>
  `gas_explicit [T] s0.vs_gas_readings = [w]`
    by simp[gas_explicit_def] >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (IntV (&w2n w))`, `es`] >>
  conj_tac >- simp[msg_gas_source] >>
  qexists_tac `OK (update_var out w
    (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
               vs_inst_idx := LENGTH sb.cs_current_insts|>))` >>
  gvs[update_var_def]
QED
