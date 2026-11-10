(* Seam 2 joint induction, For family: iteration over an array. *)
Theory bodyIntCallFamStmtForArray
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtForArraySetup
  bodyIntCallFamStmtForArrayProducer bodyIntCallFamStmtForArrayIterations
  stmtSimProps stmtSimDefs bodySim exprSimHypsDefs vyperTyping
  compileEnv stmtSimForArrayLoop exprLoweringProps loweringPosts
  vyperInterpreter vyperState finite_map list bodyIntCallJointStmtSeq
  supportedStmts vyperTypeSystem bodySimDeclCases valueEncodingProps
  stmtLoweringMono fragExec stmtLowering compileVyper vyperTypeInvariants
  stmtSimForArrayFrag stmtForArrayMemorySupport stmtSimDeclCompose
  exprSimSubscriptMap bodyIntCallJointStmtBoundary

Theorem intcall_stmts_producer_for_array:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  intcall_stmts_producer fp stmts ==>
  intcall_stmts_producer fp [For id fty (Array arr) bound stmts]
Proof
  strip_tac >> simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es /\ ce_locals_declared ce env` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `supported_stmt fp.jc_tops bindings (For id fty (Array arr) bound stmts) /\
   type_stmt env fp.jc_ret_ty (For id fty (Array arr) bound stmts) = SOME env'` by
    (fs[supported_stmts_list, type_stmt_def, AllCaseEqs()]) >>
  drule_all intcall_array_source_inputs >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ip) arrsz)` >>
  qmatch_asmsub_abbrev_tac `LENGTH vs = bound` >>
  drule_all array_for_layout_ready >> strip_tac >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `32 <= type_memory_bytes ce fty` by
    (`assignable_type (get_tenv fp.jc_cx) fty` by metis_tac[] >>
     drule_all assignable_type_slot_size_pos >>
     simp[type_memory_size_slots]) >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  `!c lc sa sb. compile_stmts c lc
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[compile_stmt_cs_mono, cs_mono_def] >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `vs = array_elements (ArrayTV tv (Fixed (LENGTH vs))) (SArrayV al)` by
    (qpat_x_assum `Abbrev _` mp_tac >> simp[markerTheory.Abbrev_def]) >>
  `32 <= type_memory_bytes ce fty /\
   type_memory_bytes ce fty + 64 < dimword (:256)` by simp[] >>
  drule_all intcall_array_compiler_entry >> strip_tac >>
  suspend "iterate"
QED

Resume intcall_stmts_producer_for_array[iterate]:
  `?ce_b. stmts_env bc (InLoop exit incr)
      (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0 = (ce_b,sb1)` by
    (qmatch_goalsub_abbrev_tac `stmts_env bc lc rt stmts sb0` >>
     Cases_on `stmts_env bc lc rt stmts sb0` >>
     fs[array_for_code_def] >> metis_tac[compile_stmts_env, pairTheory.SND]) >>
  `same_frame ce bc` by
    (irule declare_local_same_frame >>
     qhdtm_assum `declare_local` (irule_at Any) >> simp[]) >>
  `body_inv fp.jc_tops fp.jc_ctx bc fp.jc_cx` by
    metis_tac[bodyExprPreFactsTheory.body_inv_same_frame] >>
  `local_ptrs_reserved ce sb1` by
    (`local_ptrs_reserved ce sa` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
     `sb0.cs_next_var <= sb1.cs_next_var` by
       (fs[array_for_code_def] >> metis_tac[]) >>
     irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops` by
    fs[body_inv_def] >>
  `call_evaluation_safe fp.jc_cx (int_calls_stmts stmts)` by
    (fs[intcall_frame_ok_def, vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
     metis_tac[]) >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
    occurs_abi_decode_target target fp.jc_tops` by
    (fs[supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >> metis_tac[]) >>
  `EVERY (stmt_exprs_ok bc) stmts` by
    (drule bodyExprPreFactsTheory.stmt_exprs_ok_same_frame >>
     disch_then SUBST1_TAC >> drule body_for_exprs_ok >> simp[]) >>
  `IS_SOME (type_stmts ((extend_local env id fty F) with bare_global_assignable := FEMPTY)
    fp.jc_ret_ty stmts)` by
    (qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
     simp[type_stmt_def, extend_local_def] >>
     IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> simp[]) >>
  `FLOOKUP env.var_types name = SOME (ArrayT fty (Fixed (LENGTH vs))) /\ name <> id` by
    (fs[well_typed_expr_def] >> strip_tac >> gvs[FLOOKUP_DEF]) >>
  `type_memory_bytes ce fty < 2 ** 64` by
    fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def] >>
  `gas_admissible (eval_for fp.jc_cx tv id stmts vs) (stmt_res_ok lctx) es` by
    (irule intcall_array_for_admissible >>
     qhdtm_assum `gas_admissible` (irule_at Any) >> simp[]) >>
  `!gs. eval_stmt fp.jc_cx
    (For id fty (Array (Name (ArrayT fty (Fixed (LENGTH vs))) name)) (LENGTH vs) stmts)
    (es with gas_obs := gs) = eval_for fp.jc_cx tv id stmts vs (es with gas_obs := gs)` by
    (irule intcall_array_eval_for_source >> simp[]) >>
  suspend "apply"
QED
Resume intcall_stmts_producer_for_array[apply]:
  drule array_for_code_condition >> strip_tac >>
  `!scs. not_local_ptr ce scs dv` by (fs[array_for_code_def] >> metis_tac[]) >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_for fp.jc_cx tv id stmts (DROP 0 vs)) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ intcall_joint_res fp ce env ee sa t /\
      (!x z. not_fresh_at sa x /\ lookup_var x cc = SOME z ==> lookup_var x t = SOME z) /\
      (!aid b. FLOOKUP cc.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      cc.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. ?ex. res = INR ex /\ intcall_stmt_exit fp (INR ex) ee r)` by
    (irule (SRULE [LET_THM] intcall_array_iterations) >>
     qpat_assum `array_loop_inv _ _ _ _ _ vs id idx _ _ _ _ _ _ cond sa 0 es cc`
       (irule_at Any) >> simp[] >>
     qexists_tac `stmt_res_ok lctx` >> simp[] >>
     qexistsl_tac [`sa.cs_next_id + 5`, `sa.cs_next_id + 4`, `dv`, `bod`] >> simp[] >>
     reverse conj_tac >- metis_tac[] >>
     rpt gen_tac >> strip_tac >>
     irule intcall_array_producer_round >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     qhdtm_x_assum `array_for_code` mp_tac >> simp[] >> strip_tac >>
     qhdtm_assum `array_for_code` (irule_at Any) >> simp[] >>
     qhdtm_assum `declare_local` (irule_at Any) >> simp[] >>
     conj_tac >- (qx_gen_tac `u` >> strip_tac >>
       qpat_assum `!k ee s lbl. _` (qspecl_then [`k`, `es'`, `u`, `bod`] mp_tac) >> simp[]) >>
     conj_tac >- (qpat_assum `!k ee s lbl. _` (qspecl_then [`k`, `es'`, `s''`, `cond`] mp_tac) >> simp[]) >>
     conj_tac >- (qpat_x_assum `type_memory_bytes ce fty < _` mp_tac >> simp[]) >>
     fs[array_loop_inv_def]) >>
  irule gas_outcome_zero_prefix >> qexists_tac `cc` >> simp[] >>
  irule array_for_source_prefix >> simp[] >>
  conj_tac >- fs[array_loop_inv_def] >>
  irule gas_outcome_start_gas_obs >>
  irule gas_outcome_conseq >>
  qhdtm_x_assum `gas_outcome` mp_tac >> simp[] >> strip_tac >>
  qhdtm_assum `gas_outcome` (irule_at Any) >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[stmt_lands_def, block_is_terminated_def, cenv_top_ext_refl] >>
  irule intcall_joint_res_next_var >> qexists_tac `sa` >> simp[] >>
  metis_tac[compile_stmt_cs_mono, cs_mono_def]
QED
Finalise intcall_stmts_producer_for_array
