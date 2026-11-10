(* Counted valued returns in the selected external frame. *)
Theory externalReturnValuedFrag
Ancestors externalReturnSelectedDispatch externalReturnSelectedResources
  externalReturnSelectedPrefix
  externalReturnCountedBoundary externalReturnConsumerFit
  stmtLoweringMono stmtSimDefs loweringPosts bodySim exprSimHypsDefs
  exprLoweringProps fragExec compileEnv stmtLowering
  bodySimFull gasOutcomeFullCompose entryHaltPtr
  gasShadowState emitHelper abiBuiltinAllocation
  externalReturnSelectedSuffix bodyPtrDefs loweringHalt vyperLoweringCorrect e2eDefs
  stmtSimReturn gasOutcomeFull exprOperandVar fragGasOriginPtr exprSimDefs
  vyperState stmtSimProps

Theorem return_selected_valued_frag:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (!ty. expr_sim ctx func ce cx ty e es /\ expr_vv_sim ctx func ce cx ty e es) /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target ==>
  stmt_frag ctx func cx lctx
    (\v ee r. ?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
    ce (stmt_env ce lctx ret (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  `ce.ce_return_pc = NONE` by
    (drule_all return_selected_consumer_resources >> simp[]) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all return_consumer_compile_split >> strip_tac >>
  `ci_mono sa sb` by
    (qspecl_then [`ce`,`ret`,`e`,`sa`] mp_tac (cj 2 ci_mono_compile_expr_sa) >>
     simp[]) >>
  `!sx. ci_mono sx
    (SND (return_consumer_suffix ce ret (lowered_value_type ce e) op sx))` by
    (gen_tac >> pure_rewrite_tac[return_consumer_suffix_def] >>
     irule ci_mono_bind >> conj_tac
     >- simp[ci_mono_return_helpers] >>
     rpt gen_tac >> IF_CASES_TAC >> simp[ci_mono_comp_return] >>
     irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
     rpt gen_tac >> irule ci_mono_bind >> simp[ci_mono_comp_return] >>
     rpt gen_tac >> irule ci_mono_ignore_bind >>
     simp[ci_mono_typed_memory_family, ci_mono_comp_return]) >>
  `cs_extends sa sb /\ cs_extends sb cs'` by
    (qpat_x_assum `!sx. ci_mono _ _` (qspec_then `sb` mp_tac) >>
     simp[ci_mono_def] >> fs[ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all return_prefix_code_resources >> strip_tac >>
  `expr_sim ctx func ce
      (initial_evaluation_context am.sources am.layouts tx NONE) ret e es /\
   expr_vv_sim ctx func ce
      (initial_evaluation_context am.sources am.layouts tx NONE) ret e es` by simp[] >>
  drule_all return_selected_forced_prefix >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ H _` >> strip_tac >>
  `(\res ee t. ?v. res = INL v /\ H (INL v) ee t) = H` by
    (simp[FUN_EQ_THM] >> rpt gen_tac >> Cases_on `res` >> simp[Abbr `H`]) >>
  irule return_counted_continuation >>
  qexists_tac `\v ee t. H (INL v) ee t` >>
  conj_tac
  >- (rpt gen_tac >> simp[Abbr `H`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      `expr_post ctx func ce
        (initial_evaluation_context am.sources am.layouts tx NONE) e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
        sa sb s0 ee v op t` by simp[return_expr_post_start_gas_obs] >>
      qmatch_goalsub_abbrev_tac `stmt_exit RetQ` >>
      qsuff_tac `?n r. gas_path ctx func t n r /\ exit_result r /\ RetQ v ee r`
      >- (strip_tac >> qexistsl_tac [`n`,`r`] >> simp[] >>
          fs[stmt_exit_def, Abbr `RetQ`, return_result_gas_obs,
            return_result_scopes]) >>
      simp[Abbr `RetQ`] >> irule return_selected_success_suffix >> simp[] >>
      qpat_assum `expr_post _ _ _ _ _ (_ with gas_obs := _) _ _ _ _ _ _ _`
        (irule_at Any) >>
      qpat_assum `IS_SOME (type_stmt _ _ _)` (irule_at Any) >>
      qpat_assum `set_external_package_target _ _ = _` (irule_at Any) >>
      simp[] >>
      qpat_assum `lower_vyper_runtime_unit _ _ = _` (irule_at Any) >>
      qpat_assum `compile_register_positional_args _ _ _ _ = _` (irule_at Any) >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  BETA_TAC >> asm_rewrite_tac[]
QED

Theorem return_word_shadow_cancel[local]:
  compile_external_return (SOME op) T F ei msz F nkey ut iv s = (u,sf) /\
  compile_external_return (SOME op') T F ei' msz' F nkey' ut' iv' t = (u',tf) /\
  gas_shadow_state sf tf ==>
  op = op' /\ gas_shadow_state s t
Proof
  simp[compile_external_return_def, contextTheory.compile_alloc_buffer_def,
    emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
    emit_def] >>
  rpt strip_tac >> gvs[gas_shadow_state_def] >>
  gvs[gas_shadow_inst_def, venomInstTheory.mk_inst_def]
QED

Theorem return_word_paired_prefix[local]:
  ce.ce_return_pc = NONE /\ is_word_type ret /\ ~ce.ce_raw_return /\
  ce.ce_nonreentrant = (F,nkey,ut,iv) /\
  stmt_env ce lc ret (Return (SOME e)) sa = (ce',sf) /\
  stmt_env ce lc ret (Return (SOME (gas_shadow_expr e))) ta = (ce',tf) /\
  gas_shadow_state sf tf /\ fn_has_code sa sf func /\
  fn_has_code ta tf shadow_func ==>
  ?op sb tb.
    lower_value compile_expr ce ret e sa = (op,sb) /\
    lower_value compile_expr ce ret (gas_shadow_expr e) ta = (op,tb) /\
    gas_shadow_state sb tb /\
    compile_external_return (SOME op) T F ce.ce_ret_enc_info
      ce.ce_max_return_size F nkey ut iv sb = ((),sf) /\
    compile_external_return (SOME op) T F ce.ce_ret_enc_info
      ce.ce_max_return_size F nkey ut iv tb = ((),tf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\
    fn_has_code ta tb shadow_func /\ fn_has_code tb tf shadow_func
Proof
  strip_tac >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def,
    comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_all return_consumer_compile_split >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ (Return (SOME e)) _ = _` kall_tac >>
  drule_all return_consumer_compile_split >> strip_tac >>
  gvs[return_consumer_no_normalize] >>
  drule_all return_word_shadow_cancel >> strip_tac >> gvs[] >>
  `cs_extends sa sb` by
    (mp_tac (cj 2 ci_mono_compile_expr_sa) >>
     disch_then (qspecl_then [`ce`,`ret`,`e`,`sa`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends ta sb'` by
    (mp_tac (cj 2 ci_mono_compile_expr_sa) >>
     disch_then (qspecl_then [`ce`,`ret`,`gas_shadow_expr e`,`ta`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends sb cs'' /\ cs_extends sb' cs'` by
    (mp_tac (cj 3 ci_mono_return_helpers) >>
     simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
  metis_tac[fn_has_code_split]
QED

Theorem return_word_full_suffix[local]:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  is_word_type ret /\ ~lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops /\
  compile_external_return (SOME op) T F ei msz F nkey ut iv sb = ((),sf) /\
  fn_has_code sb sf func /\
  (!y. op = Var y ==> not_fresh_at sb y) /\
  ghost_inv_at D lo d ce cx ee G tn s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?ss G' tn'.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Halt ss,G',tn') /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) (Halt ss))
Proof
  strip_tac >> drule_all return_site_word_operand >> strip_tac >>
  `op_taint tn op = {} /\ stor_taint_ok_at D tn s /\
   allocas_from lo s /\ lo <= s.vs_alloca_next` by
    gvs[ptr_val_ok_def, ghost_inv_at_def] >>
  drule_all external_return_word_suffix_full >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  `cx.sources = am.sources /\ cx.layouts = am.layouts /\
   cx.txn.target = tx.target` by
    simp[vyperInterpreterTheory.initial_evaluation_context_def] >>
  `state_rel func ce cx ee s` by fs[stmt_state_rel_def] >>
  drule_all external_halt_success >>
  pure_rewrite_tac[FORALL_SIMP] >>
  disch_then (qspec_then `am.exports` mp_tac) >>
  strip_tac >>
  drule_all return_bytes_prim_value >> strip_tac >>
  qexistsl_tac [`ss`,`G'`,`tn'`] >> simp[] >>
  qexistsl_tac [`tv`,`v`] >>
  gvs[external_call_result_rel_def, tx_return_bytes_def,
      vyperInterpreterTheory.abstract_machine_from_state_def]
QED

(* The source evaluation equation belongs to the full witness; retain it
   alongside the normal post when composing the primitive return suffix. *)
Theorem compile_return_word_external_frag_full:
 !D lo d ctx shadow_ctx PG func shadow_func cx cenv lctx ret e env es tops am tx nkey ut iv.
  cenv.ce_return_pc = NONE /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  cenv.ce_raw_return = lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
  ~cenv.ce_raw_return /\ is_word_type ret /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops /\
  expr_sim_inv cenv cx env es /\
  stmt_exprs_ok cenv (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  (!ety. expr_sim_full (D,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ety e es /\
         expr_vv_sim_full (D,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ety e es)
  ==>
  stmt_frag_full (D,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx
   (\v ee gt r. ?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
     safe_cast tv v = SOME v' /\
     external_call_result_rel tops ret tx
       (INL v', finalize_pending_deletions
         (abstract_machine_from_state am.sources am.exports am.layouts ee),ee.requests) r)
   cenv (stmt_env cenv lctx ret (Return (SOME e)))
   (stmt_env cenv lctx ret (Return (SOME (gas_shadow_expr e))))
   (eval_stmt cx (Return (SOME e))) es
Proof
  rpt strip_tac >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all return_word_paired_prefix >> strip_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `!ety. _` (qspec_then `ret` strip_assume_tac) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_full_def] >>
  disch_then drule_all >> simp[] >>
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- suspend "normal"
  >- suspend "exit"
  >> suspend "exempt"
QED

Resume compile_return_word_external_frag_full[exempt]:
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
  disj2_tac >> metis_tac[return_forced_exempt]
QED

Resume compile_return_word_external_frag_full[exit]:
  gvs[] >>
  `?exc. res = INR exc` by (Cases_on `res` >> gvs[expr_exit_def]) >>
  gvs[] >> rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >>
  conj_tac
  >- (gen_tac >> pure_rewrite_tac[eval_return_forced] >>
      qpat_x_assum `!tail. _ = _` (qspec_then `tail` assume_tac) >>
      gvs[bind_def]) >>
  simp[] >> disj2_tac >> simp[stmt_exit_ptr_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_return_word_external_frag_full[normal]:
  gvs[] >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[exit_result_def] >> metis_tac[]) >>
  `!y. op = Var y ==> not_fresh_at sb' y` by
    metis_tac[compile_lower_value_var] >>
  qpat_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
  `expr_post ctx func cenv
    (initial_evaluation_context am.sources am.layouts tx NONE) e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
    sa sb' s0 (ee with gas_obs := []) v op t` by
      simp[return_expr_post_start_gas_obs] >>
  `expr_sim_inv cenv
    (initial_evaluation_context am.sources am.layouts tx NONE) env
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  fs[vyperTypeCallGraphTheory.int_calls_stmt_def,
     vyperTypeCallGraphTheory.int_calls_expr_def] >>
  qpat_x_assum `monad_bind _ _ _ = _` mp_tac >> simp[] >> strip_tac >>
  `?ss H u.
    gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G',tn') [] (Halt ss,H,u) /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts
            (ee with gas_obs := [])),
          (ee with gas_obs := []).requests) (Halt ss))` by
    (irule return_word_full_suffix >> simp[] >>
     qpat_assum `expr_post _ _ _ _ _ (_ with gas_obs := _) _ _ _ _ _ _ _`
       (irule_at Any) >> simp[] >>
     metis_tac[expr_sim_inv_gas_obs]) >>
  `gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) marks (Halt ss,H,u)` by
    (qpat_assum `gas_origin_ptr_path _ _ _ (OK _,_,_)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     simp[] >> disch_then drule >> simp[]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR (ReturnException v)`,`ee`,`Halt ss`,`H`,`u`] >>
  conj_tac
  >- (gen_tac >> pure_rewrite_tac[eval_return_forced] >>
      qpat_x_assum `!tail. _ = _` (qspec_then `tail` assume_tac) >>
      gvs[bind_def, raise_def]) >>
  simp[exit_result_def] >>
  simp[stmt_exit_ptr_def, return_result_gas_obs, return_result_scopes] >>
  metis_tac[return_result_gas_obs]
QED

Finalise compile_return_word_external_frag_full
