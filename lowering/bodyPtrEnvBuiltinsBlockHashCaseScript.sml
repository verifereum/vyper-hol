(* Guarded BlockHash consumer: source semantics and checked runs stay separate. *)
Theory bodyPtrEnvBuiltinsBlockHashCase
Ancestors bodyPtrEnvBuiltinsEntryFrame bodyPtrEnvBuiltinsBlockHashSource
  bodyPtrEnvBuiltinsBlockHashOperand bodyPtrEnvBuiltinsBlockHashRun
  bodyPtrEnvBuiltinsGuardedCompose bodyPtrEnvBuiltinsBoundary bodyPtrEnvBuiltinsMethodTyping
  exprSimBuiltins exprSimUnopProps exprSimUnopComposeProps
  exprSimDefs exprSimWordArgs exprSimSource exprSimHypsDefs exprSimProps
  exprLowering exprLoweringProps exprOperandVar freshWrites
  bodyPtrDefs bodyPtrPreds gasSummaryComposePtr fragGasPathPtr gasSummary gasExemptCert
  vyperTypeBuiltins vyperTypeSystem vyperInterpreter vyperValue vyperState
  builtinSimple vyperTypeInvariants vyperContext vyperTyping vyperAST
  builtinProps compileEnv loweringStateRelDefs context loweringPosts venomState venomInst finite_map list fragExec exprSimHyps

Theorem blockhash_body_pre_args:
  expr_body_pre cenv cx env (Builtin ann BlockHash args) es ==>
  ?e. args = [e] /\ ann = BaseT (BytesT (Fixed 32)) /\
      expr_type e = BaseT (UintT 256)
Proof
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]
QED

Theorem blockhash_operand_pre:
  expr_body_pre cenv cx env (Builtin ann BlockHash [e]) es ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >> drule blockhash_body_pre_args >> strip_tac >> gvs[] >>
  irule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >> simp[] >>
  conj_tac >- gvs[expr_body_pre_def] >>
  qexistsl_tac [`BaseT (BytesT (Fixed 32))`, `[e]`, `BlockHash`, `es`] >> simp[]
QED

Theorem blockhash_singleton_sim_ptr:
  expr_body_pre cenv cx env (Builtin ann BlockHash [e]) es /\
  expr_sim_ptr d ctx PG fn cenv cx ty e es ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (Builtin ann BlockHash [e]) es
Proof
  strip_tac >> drule blockhash_body_pre_args >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by metis_tac[blockhash_operand_pre] >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_blockhash >> strip_tac >>
  drule compile_blockhash_shape >> strip_tac >>
  `cs_extends s1 sb` by (simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> goal_assum (drule_at Any) >>
     simp[builtin_args_length_ok_def, precompile_builtin_def]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `bind (eval_expr cx (Builtin (BaseT (BytesT (Fixed 32))) BlockHash [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v ee. (unop_result cx (BaseT (BytesT (Fixed 32))) BlockHash [expr_type e] v ee,ee))` by
    (irule eval_expr_unop_action_general >>
     simp[builtin_args_length_ok_def, precompile_builtin_def]) >>
  pop_assum SUBST1_TAC >> irule guarded_suffix_outcome_compose >>
  conj_tac
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def] >>
      once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]) >>
  goal_assum (drule_at Any) >> suspend "suffix"
QED

Resume blockhash_singleton_sim_ptr[suffix]:
  rpt strip_tac >> gvs[] >>
  drule_all method_id_marked_operand_facts >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,ee with gas_obs := [])` by
    (gvs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  `i < 2 ** 256` by
    (`?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >> gvs[]) >>
  `eval_operand x t = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i))` by
    (gvs[expr_post_def, expr_val_rel_def, is_word_type_def, evaluate_type_def] >> metis_tac[]) >>
  `op_taint tn x = {} /\ op_prov G x = NONE` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  `local_ptrs_rel fn cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `stmt_state_rel ctx fn cenv cx ee t` by gvs[expr_post_def] >>
  fs[] >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    (qpat_assum `lower_value _ _ _ e _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[is_word_type_def] >> metis_tac[]) >>
  drule_at (Pat `eval_operand _ _ = _`) blockhash_source_raw_outcome >>
  simp[] >> disch_then drule_all >> strip_tac
  >- suspend "normal" >> suspend "abort"
QED
Resume blockhash_singleton_sim_ptr[normal]:
  drule_at (Pat `bind _ _ _ = _`) operand_blockhash_suffix_run >>
  simp[expr_post_entry_gas_obs, ghost_kept_entry_gas_obs] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  qexistsl_tac [`INL v`, `ee`, `G''`, `tn''`, `OK t'`] >>
  simp[unop_result_gas_obs, expr_type_def, is_word_type_def] >>
  conj_tac >- suspend "post" >>
  simp[ptr_val_ok_def, is_word_type_def]
QED
Resume blockhash_singleton_sim_ptr[abort]:
  drule_all blockhash_counted_abort >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  qexistsl_tac [`unop_result cx (BaseT (BytesT (Fixed 32))) BlockHash
    [BaseT (UintT 256)] (IntV i) ee`, `ee`, `G'`, `tn'`,
    `Abort Revert_abort (u with vs_inst_idx := j)`] >>
  simp[unop_result_gas_obs, exit_result_def] >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  simp[oneline expr_exit_def]
QED
Resume blockhash_singleton_sim_ptr[post]:
  rpt strip_tac >> irule expr_post_unop >>
  simp[is_word_type_def] >> conj_tac
  >- (simp[expr_val_rel_def, is_word_type_def, evaluate_type_def] >>
      goal_assum (drule_at Any) >> simp[]) >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise blockhash_singleton_sim_ptr

Theorem body_blockhash_ptr_case:
  (!s'' x t.
     type_check (builtin_args_length_ok BlockHash (LENGTH args)) "Builtin args" s'' =
       (INL x,t) ==> body_exprs_ptr_ok cx args) ==>
  body_expr_ptr_ok cx (Builtin ann BlockHash args)
Proof
  strip_tac >> irule body_expr_ptr_stack >>
  conj_tac >- simp[compile_blockhash_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  drule blockhash_body_pre_args >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [e]` by
    (first_x_assum (qspecl_then [`es`, `es`] mp_tac) >>
     simp[builtin_args_length_ok_def, type_check_def, assert_def, return_def]) >>
  irule blockhash_singleton_sim_ptr >> conj_tac
  >- (qexists_tac `env` >> simp[]) >>
  irule body_expr_ptr_sim >> simp[] >>
  conj_tac >- metis_tac[body_exprs_ptr_head] >>
  conj_tac >- (qexists_tac `tops` >> simp[]) >>
  qexists_tac `env` >> simp[] >> metis_tac[blockhash_operand_pre]
QED
