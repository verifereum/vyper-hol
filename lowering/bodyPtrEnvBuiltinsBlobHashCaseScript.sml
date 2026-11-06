(* Pointer simulation for the scalar BLOBHASH builtin. *)
Theory bodyPtrEnvBuiltinsBlobHashCase
Ancestors
  bodyPtrEnvBuiltinsEntryFrame
  bodyPtrEnvBuiltinsBlobHashRun bodyPtrEnvBuiltinsBlobHashFacts
  bodyPtrEnvBuiltinsOperandCompose bodyPtrEnvBuiltinsBoundary bodyPtrEnvBuiltinsMethodTyping
  exprSimBuiltins exprSimUnopProps exprSimUnopComposeProps
  exprSimWordArgs exprSimSource exprSimHypsDefs exprSimProps
  exprLowering exprLoweringProps exprOperandVar freshWrites
  bodyPtrDefs bodyPtrPreds gasSummaryComposePtr fragGasPathPtr gasSummary gasExemptCert
  vyperTypeBuiltins vyperTypeSystem vyperInterpreter vyperValue vyperState
  builtinSimple vyperTypeInvariants vyperContext vyperTyping vyperAST
  compileEnv context loweringPosts venomState venomInst finite_map list fragExec exprSimHyps
  emitHelperProps exprSimAccounts

Theorem blobhash_singleton_sim_ptr:
  expr_body_pre cenv cx env (Builtin ann BlobHash [e]) es /\
  expr_sim_ptr d ctx PG fn cenv cx ty e es ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (Builtin ann BlobHash [e]) es
Proof
  strip_tac >> drule blobhash_body_pre_args >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by metis_tac[blobhash_operand_pre] >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_blobhash >> strip_tac >>
  drule emit_op_extends_next_var >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> goal_assum (drule_at Any) >>
     simp[builtin_args_length_ok_def, precompile_builtin_def]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `bind (eval_expr cx (Builtin (BaseT (BytesT (Fixed 32))) BlobHash [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v ee. (unop_result cx (BaseT (BytesT (Fixed 32))) BlobHash [expr_type e] v ee,ee))` by
    (irule eval_expr_unop_action_general >>
     simp[builtin_args_length_ok_def, precompile_builtin_def]) >>
  pop_assum SUBST1_TAC >> irule scalar_suffix_outcome_compose >>
  conj_tac
  >- (rpt strip_tac >> rewrite_tac[ignore_bind_def] >>
      once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]) >>
  goal_assum (drule_at Any) >> suspend "normal"
QED

Resume blobhash_singleton_sim_ptr[normal]:
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
  `op_taint tn x = {}` by gvs[ptr_val_ok_def, is_word_type_def] >>
  `local_ptrs_rel fn cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `stmt_state_rel ctx fn cenv cx ee t` by gvs[expr_post_def] >>
  fs[] >>
  drule_at (Pat `bind _ _ _ = _`) operand_blobhash_suffix_run >>
  simp[expr_post_entry_gas_obs, ghost_kept_entry_gas_obs] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  qexistsl_tac [`INL (evaluate_blob_hash cx.txn (Num i))`, `ee`, `G''`, `tn''`, `t'`] >>
  simp[unop_result_gas_obs, expr_type_def, blobhash_source_result] >>
  conj_tac >- suspend "post" >>
  simp[ptr_val_ok_def, is_word_type_def]
QED
Resume blobhash_singleton_sim_ptr[post]:
  rpt strip_tac >> irule expr_post_unop >>
  simp[is_word_type_def, blobhash_source_result] >>
  conj_tac
  >- (simp[expr_val_rel_def, is_word_type_def, evaluate_type_def] >>
      goal_assum (drule_at Any) >> simp[]) >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise blobhash_singleton_sim_ptr

Theorem body_blobhash_ptr_case:
  (!s'' x t.
     type_check (builtin_args_length_ok BlobHash (LENGTH args)) "Builtin args" s'' =
       (INL x,t) ==> body_exprs_ptr_ok cx args) ==>
  body_expr_ptr_ok cx (Builtin ann BlobHash args)
Proof
  strip_tac >> irule body_expr_ptr_stack >>
  conj_tac >- simp[compile_blobhash_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  rpt gen_tac >> strip_tac >>
  drule blobhash_body_pre_args >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [e]` by
    (first_x_assum (qspecl_then [`es`, `es`] mp_tac) >>
     simp[builtin_args_length_ok_def, type_check_def, assert_def, return_def]) >>
  irule blobhash_singleton_sim_ptr >> conj_tac
  >- (qexists_tac `env` >> simp[]) >>
  irule body_expr_ptr_sim >> simp[] >>
  conj_tac >- metis_tac[body_exprs_ptr_head] >>
  conj_tac >- (qexists_tac `tops` >> simp[]) >>
  qexists_tac `env` >> simp[] >> metis_tac[blobhash_operand_pre]
QED
