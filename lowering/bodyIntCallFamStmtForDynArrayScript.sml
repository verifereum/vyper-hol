(* Seam 2 joint induction, For family: iteration over a local DynArray. *)
Theory bodyIntCallFamStmtForDynArray
Ancestors
  bodyIntCallFamStmtForDynArraySetup bodyIntCallFamStmtForDynArrayEntry
  bodyIntCallFamStmtForArrayGen bodyDynArraySource
  whitelistForIterDynFrag whitelistForIterDynLoop
  bodyIntCallJointContract stmtSimProps stmtSimDefs bodySim exprSimHypsDefs
  vyperTyping compileEnv stmtSimForArrayLoop exprLoweringProps loweringPosts
  vyperInterpreter vyperState finite_map list bodyIntCallJointStmtSeq
  supportedStmts vyperTypeSystem bodySimDeclCases valueEncodingProps
  stmtLoweringMono fragExec stmtLowering compileVyper vyperTypeInvariants
  stmtSimForArrayFrag stmtForArrayMemorySupport stmtSimDeclCompose
  exprSimSubscriptMap bodyIntCallJointStmtBoundary vyperAST

Theorem intcall_stmts_producer_for_dynarray_name:
  intcall_stmts_producer fp stmts /\
  (?c name. arr = Name (ArrayT fty (Dynamic c)) name) ==>
  intcall_stmts_producer fp [For id fty (Array arr) bound stmts]
Proof
  strip_tac >> gvs[] >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es /\ ce_locals_declared ce env` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `supported_stmt fp.jc_tops bindings
     (For id fty (Array (Name (ArrayT fty (Dynamic c)) name)) bound stmts) /\
   type_stmt env fp.jc_ret_ty
     (For id fty (Array (Name (ArrayT fty (Dynamic c)) name)) bound stmts) =
     SOME env'` by
    (gvs[supported_stmts_list, type_stmt_def, AllCaseEqs()]) >>
  `c = bound` by
    (drule type_stmt_for_array_bound >> simp[expr_type_def]) >>
  gvs[] >>
  drule supported_loop_body_contract >> strip_tac >>
  `bound <= bound` by simp[] >>
  drule_all dynarray_name_source_ready >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ip) arrsz)` >>
  rename1 `lookup_scopes name es.scopes = SOME snapshot` >>
  `!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)` by
    (gen_tac >> strip_tac >> irule dynarray_elements_typed >>
     simp[] >> qexists_tac `bound` >> gvs[]) >>
  drule_all array_for_layout_ready >> strip_tac >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  `!c lc sa sb. compile_stmts c lc
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[compile_stmt_cs_mono, cs_mono_def] >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `type_memory_bytes ce fty + 64 < dimword (:256) /\
   value_has_type snapshot.type snapshot.value` by simp[] >>
  drule_all intcall_dynarray_compiler_entry >> strip_tac >>
  suspend "iterate"
QED

Resume intcall_stmts_producer_for_dynarray_name[iterate]:
  qhdtm_assum `dynarray_for_code`
    (strip_assume_tac o REWRITE_RULE [dynarray_for_code_def]) >>
  `?ce_b. stmts_env bc (InLoop exit incr)
      (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0 = (ce_b,sb1)` by
    (qmatch_goalsub_abbrev_tac `stmts_env bc lc rt stmts sb0` >>
     Cases_on `stmts_env bc lc rt stmts sb0` >>
     metis_tac[compile_stmts_env, pairTheory.SND]) >>
  `same_frame ce bc` by
    (irule declare_local_same_frame >>
     qhdtm_assum `declare_local` (irule_at Any) >> simp[]) >>
  `body_inv fp.jc_tops fp.jc_ctx bc fp.jc_cx` by
    metis_tac[bodyExprPreFactsTheory.body_inv_same_frame] >>
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `local_ptrs_reserved ce sb1` by
    (`local_ptrs_reserved ce sa` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops` by
    fs[body_inv_def] >>
  `call_evaluation_safe fp.jc_cx (int_calls_stmts stmts)` by
    (fs[intcall_frame_ok_def, vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
     metis_tac[]) >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
    occurs_abi_decode_target target fp.jc_tops` by
    (fs[supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >> metis_tac[]) >>
  `stmts_exprs_ok bc stmts` by
    (irule bodyExprPreFactsTheory.for_declare_stmts_exprs_ok >>
     qhdtm_assum `declare_local` (irule_at Any) >>
     metis_tac[bodySimDeclCasesTheory.body_for_exprs_ok]) >>
  `IS_SOME (type_stmts ((extend_local env id fty F) with bare_global_assignable := FEMPTY)
    fp.jc_ret_ty stmts)` by
    (qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
     simp[type_stmt_def, extend_local_def] >>
     IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> simp[]) >>
  `name <> id` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
  `type_memory_bytes ce fty < 2 ** 64` by
    fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def] >>
  `gas_admissible (eval_for fp.jc_cx tv id stmts (MAP Value vs)) (stmt_res_ok lctx) es` by
    (irule intcall_dynarray_for_admissible >>
     qhdtm_assum `gas_admissible` (irule_at Any) >> simp[]) >>
  suspend "apply"
QED

Resume intcall_stmts_producer_for_dynarray_name[apply]:
  drule intcall_dynarray_copy_entry >> rpt (disch_then drule) >> strip_tac >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] (Q.INST
    [`P` |-> `\ee. lookup_scopes name ee.scopes = SOME snapshot`,
     `sc` |-> `sa`, `origin` |-> `cc`, `lvo` |-> `Var lv`,
     `saved` |-> `Var ip`, `tyv` |-> `tv`, `sz` |-> `type_memory_bytes ce fty`,
     `j1` |-> `sa.cs_next_id + 8`, `j2` |-> `sa.cs_next_id + 9`,
     `i1` |-> `sj.cs_next_id`, `i2` |-> `sj.cs_next_id + 1`,
     `i3` |-> `sj.cs_next_id + 2`, `sd` |-> `st1`, `sd'` |-> `sd`]
    intcall_array_gen_loop))) >>
  qpat_assum `ALL_DISTINCT [idx; _; _; _; _; _; _; _]`
    (strip_assume_tac o SRULE []) >>
  `LENGTH vs < dimword (:256)` by simp[] >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`eval_stmts _ _ _ = _`]
      >- (qx_genl_tac [`k1`, `es1`, `gs`, `res`, `ee`] >> strip_tac >>
          Cases_on `ee.scopes` >- gvs[] >> simp[] >>
          irule array_body_direct_snapshot >>
          qpat_x_assum `eval_stmts _ _ _ = _` (assume_tac o SRULE []) >>
          qexistsl_tac [`ArrayT fty (Dynamic bound)`, `bindings`, `Dynamic bound`,
            `fp.jc_cx`, `ee`, `es1 with gas_obs := gs`, `fty`, `env`, `env_b`,
            `id`, `res`, `fp.jc_ret_ty`, `h`, `stmts`, `fp.jc_tops`, `tv`, `fty`,
            `EL k1 vs`] >>
          simp[]) >>
      simp[]) >>
  disch_then (qspecl_then [`0`, `es`, `cc`] mp_tac) >>
  impl_tac
  >- (qpat_x_assum `type_memory_bytes ce fty = _` kall_tac >>
      simp[venomStateTheory.eval_operand_def]) >>
  strip_tac >>
  irule gas_outcome_zero_prefix >> qexists_tac `cc` >> simp[] >>
  qpat_assum `!gs. eval_iterator _ _ _ = _` (fn th => irule (MATCH_MP
    (REWRITE_RULE [GSYM AND_IMP_INTRO] for_source_prefix_bounded) th)) >>
  qpat_assum `evaluate_type _ fty = SOME _` (irule_at Any) >> simp[] >>
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
Finalise intcall_stmts_producer_for_dynarray_name
