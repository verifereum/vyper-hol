(* The positional capture and the real LOG suffix share the same saved rows. *)
Theory bodyLogCompilerCutsMods
Ancestors
  loweringPosts stmtLowering stmtLoweringMono exprLowering exprLoweringProps
  eventLoweringStructure fragExec compileEnv emitHelper vyperAST
  gasShadow gasShadowState gasShadowCompileBase gasShadowCompileStmtCases
  venomInst pair list

Theorem stmt_env_log_compile[local]:
  stmt_env ce lctx ret (Log id args) sa = (ce',sb) ==>
  ce' = ce /\ compile_stmt ce lctx ret (Log id args) sa = ((),sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem log_saved_capture_shadow[local]:
  compile_ext_call_args compile_expr ce [] (MAP (lowered_value_type ce) args)
    args sa = (saved,sm) /\ gas_shadow_state sa ta ==>
  ?tm. compile_ext_call_args compile_expr (gas_shadow_env T ce) []
         (MAP (lowered_value_type (gas_shadow_env T ce)) (MAP gas_shadow_expr args))
         (MAP gas_shadow_expr args) ta = (saved,tm) /\ gas_shadow_state sm tm
Proof
  simp[lowered_value_type_gas_shadow_env] >> strip_tac >>
  Cases_on `compile_ext_call_args compile_expr (gas_shadow_env T ce) []
    (MAP (lowered_value_type ce) (MAP gas_shadow_expr args))
    (MAP gas_shadow_expr args) ta` >>
  mp_tac (Q.INST [`sd` |-> `T`, `cenv` |-> `ce`]
    gas_shadow_log_snapshots_env) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`ta`] mp_tac) >> simp[EQ_SYM_EQ]
QED

(* Project the reached endpoint from a compiler monotonicity theorem. *)
fun log_mono cut mono =
  qpat_assum cut (fn eq =>
    SUBST1_TAC (SYM (REWRITE_RULE [SND] (Q.AP_TERM `SND` eq)))) >>
  (MATCH_ACCEPT_TAC mono ORELSE (irule mono >> simp[cj 1 compile_expr_ci_mono]));

Theorem log_compiler_cuts_mods:
  ce.ce_event_info (nsid_to_string id) = SOME (hash,declared,flags) /\
  stmt_env ce lctx ret (Log id args) sa = (ce',sf) /\
  stmt_env (gas_shadow_env T ce) lctx ret (gas_shadow_stmt (Log id args)) ta = (te',tf) /\
  gas_shadow_state sa ta /\ fn_has_code sa sf func /\ fn_has_code ta tf tfunc ==>
  ?saved sm tm topics st.
    ce' = ce /\ te' = gas_shadow_env T ce /\
    compile_ext_call_args compile_expr ce [] (MAP (lowered_value_type ce) args)
      args sa = (saved,sm) /\
    compile_ext_call_args compile_expr (gas_shadow_env T ce) []
      (MAP (lowered_value_type (gas_shadow_env T ce)) (MAP gas_shadow_expr args))
      (MAP gas_shadow_expr args) ta = (saved,tm) /\
    gas_shadow_state sm tm /\ ci_mono sa sm /\ ci_mono ta tm /\
    fn_has_code sa sm func /\ fn_has_code ta tm tfunc /\ fn_has_code sm sf func /\
    let (topic_rows,data_rows) = split_log_ops (ZIP (saved,MAP (lowered_value_type ce) args)) flags;
        topic_ops = Lit (n2w (SUC (LENGTH topics))) :: REVERSE topics ++ [Lit (n2w hash)]
    in
      compile_log_saved_topics ce topic_rows sm = (topics,st) /\
      ci_mono sm st /\ fn_has_code sm st func /\ fn_has_code st sf func /\
      ((data_rows = [] /\
        emit_inst LOG (topic_ops ++ [Lit 0w; Lit 0w]) [] st = ((),sf) /\
        ci_mono st sf) \/
       (data_rows <> [] /\
        ?buf sb len se.
          compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
            (TupleT (MAP SND data_rows))) st = (buf,sb) /\
          compile_abi_encode_values_to_buf ce buf.buf_operand data_rows sb = (len,se) /\
          emit_inst LOG (topic_ops ++ [len;buf.buf_operand]) [] se = ((),sf) /\
          ci_mono st sb /\ ci_mono sb se /\ ci_mono se sf /\
          fn_has_code st sb func /\ fn_has_code sb se func /\ fn_has_code se sf func))
Proof
  simp[gas_shadow_stmt_def] >> strip_tac >>
  qpat_x_assum `stmt_env ce _ _ (Log id args) _ = _`
    (strip_assume_tac o MATCH_MP stmt_env_log_compile) >>
  qpat_x_assum `stmt_env (gas_shadow_env T ce) _ _ (Log id _) _ = _`
    (strip_assume_tac o MATCH_MP stmt_env_log_compile) >>
  drule_all_then (qx_choosel_then [`saved`,`sm`,`topics`,`st`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))
    compile_log_stmt_trace >>
  drule_all_then (qx_choose_then `tm` strip_assume_tac) log_saved_capture_shadow >>
  drule_all_then strip_assume_tac compile_log_stmt_snapshot_code >>
  `(gas_shadow_env T ce).ce_event_info (nsid_to_string id) = SOME (hash,declared,flags)` by simp[] >>
  drule_all_then strip_assume_tac (Q.INST [`cenv` |-> `gas_shadow_env T ce`]
    (SPEC_ALL compile_log_stmt_snapshot_code)) >>
  `ci_mono sa sm` by log_mono `compile_ext_call_args _ _ _ _ _ sa = _` ci_mono_compile_ext_call_args >>
  `ci_mono ta tm` by log_mono `compile_ext_call_args _ _ _ _ _ ta = _` ci_mono_compile_ext_call_args >>
  `ci_mono sm st` by log_mono `compile_log_saved_topics _ _ sm = _` compile_log_saved_topics_ci_mono >>
  qexistsl_tac [`saved`,`sm`,`tm`,`topics`,`st`] >>
  simp[LET_THM, pairTheory.ELIM_UNCURRY] >>
  qpat_x_assum `(_ /\ emit_inst LOG _ _ st = _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac
      (CONJUNCTS_THEN2 assume_tac (qx_choosel_then [`buf`,`sb`,`len`,`se`] strip_assume_tac)))
  >- (`ci_mono st sf` by log_mono `emit_inst LOG _ _ st = _` ci_mono_emit_inst >>
      `fn_has_code sm st func /\ fn_has_code st sf func` by
        (irule fn_has_code_split >> fs[ci_mono_def]) >>
      gs[]) >>
  `ci_mono st sb` by log_mono `compile_alloc_buffer _ st = _` ci_mono_compile_alloc_buffer >>
  `ci_mono sb se` by log_mono `compile_abi_encode_values_to_buf _ _ _ sb = _`
    ci_mono_compile_abi_encode_values_to_buf >>
  `ci_mono se sf` by log_mono `emit_inst LOG _ _ se = _` ci_mono_emit_inst >>
  `ci_mono st sf` by (irule ci_mono_trans >> qexists `se` >> simp[] >>
    irule ci_mono_trans >> qexists `sb` >> simp[]) >>
  `fn_has_code sm st func /\ fn_has_code st sf func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code st sb func /\ fn_has_code sb sf func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sb se func /\ fn_has_code se sf func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  gs[]
QED
