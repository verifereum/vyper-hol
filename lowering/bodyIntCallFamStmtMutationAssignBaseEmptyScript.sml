(* Empty RHS BaseTarget path: source evaluation precedes counted target code. *)
Theory bodyIntCallFamStmtMutationAssignBaseEmpty
Ancestors
  bodyIntCallFamStmtMutationAssignBaseEntry
  bodyIntCallFamStmtMutationAssignEmptyStore
  bodyIntCallFamStmtMutationAugTargetCounted
  bodyIntCallJointStmtSeq bodyIntCallJointContract
  supportedStmtTraverse vyperTypeCallGraph exprSimHypsDefs
  compileEnv stmtLoweringMono exprLoweringProps supportedStmts
  vyperTypeSystem bodyExprPreFacts bodySim vyperTypeCallStackSoundness
  immutableAssignEmpty memoryLocalRhsProps targetPlaceSimDefs stmtLowering stmtSimAssignMem loweringPosts
  targetPlaceSim tuplePlaceTargetGas bodyPtrPopTargetFragTransport
  vyperTypeInvariants emitHelper fragExec exprSimHyps vyperTypeArgFits vyperTypeValues
  stmtReasonVvMemory exprSimSubscriptMap gasSummary gasOutcome fragGasMode
  stmtForArrayMemorySupport tuplePlaceWriteOutcome tuplePlaceSourceGas

Theorem intcall_assign_base_empty_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size (Assign (BaseTarget bt) rhs) ==>
        intcall_stmts_producer fp ss) /\
  has_length_word (expr_type rhs) /\ is_empty_value_expr rhs ==>
  intcall_stmts_producer fp [Assign (BaseTarget bt) rhs]
Proof
  strip_tac >>
  simp[intcall_stmts_producer_def,eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe fp.jc_cx
      (int_calls_stmts [Assign (BaseTarget bt) rhs])` by
    (fs[intcall_frame_ok_def,call_evaluation_safe_def] >> metis_tac[]) >>
  `expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  drule_at (Pat `body_inv`) intcall_assign_base_entry >>
  disch_then (drule_at (Pat `type_stmts _ _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv`)) >>
  disch_then (qspec_then `bindings` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  `stmt_env ce lctx (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
     (Assign (BaseTarget bt) rhs) sa = (ce',sb)` by
    metis_tac[stmts_env_singleton] >>
  drule stmt_env_assign >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def,comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  suspend "target"
QED

Resume intcall_assign_base_empty_stmt_step[target]:
  markerLib.RESUME_TAC >>
  `target_pre ce fp.jc_cx env bt es` by simp[target_pre_def] >>
  `call_evaluation_safe fp.jc_cx (int_calls_target bt)` by
    (fs[intcall_frame_ok_def,call_evaluation_safe_def] >> metis_tac[]) >>
  `gas_admissible (eval_target_place fp.jc_cx bt) target_place_res_ok es` by
    (irule tuple_place_target_gas_admissible >>
     simp[] >> qexistsl_tac [`ce`,`env`,`dty`] >> simp[well_typed_target_def]) >>
  `gas_admissible (eval_base_place fp.jc_cx bt) target_res_ok es` by
    (irule get_place_base_admissible >>
     fs[eval_target_place_as_bind]) >>
  `cs_extends sa cs'` by
    (qspecl_then [`bt`,`ce`,`sa`] mp_tac ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `cs_extends cs' sb` by
    (mp_tac (cj 2 ci_mono_stmt_helpers) >>
     disch_then (qspecl_then
       [`ce.ce_imm_alloca`,`FST tgt_result`,`Lit 0w`,`FST (SND tgt_result)`,`cs'`] mp_tac) >>
     gvs[ci_mono_def]) >>
  `fn_has_code sa cs' fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  drule_at (Pat `compile_get_target_ptr`) intcall_target_counted >>
  disch_then (drule_at (Pat `type_place_target`)) >>
  disch_then (drule_at (Pat `intcall_expr_res`)) >>
  disch_then (qspec_then `bindings` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `expr_body_pre ce fp.jc_cx env rhs es` by simp[] >>
  `?tv. evaluate_type (get_tenv fp.jc_cx) dty = SOME tv` by
    (drule expr_body_pre_type_evaluates >>
     Cases_on `evaluate_type (get_tenv fp.jc_cx) (expr_type rhs)` >> simp[] >>
     rename1 `evaluate_type _ (expr_type rhs) = SOME etv` >>
     drule_at (Pat `type_widens_to`) type_widens_to_value_has_type >>
     disch_then (qspec_then `default_value etv` mp_tac) >>
     fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
     metis_tac[vyperTypingTheory.default_value_well_typed]) >>
  drule_all immutable_assign_empty_read >> strip_tac >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (vyperState$bind (eval_expr fp.jc_cx rhs) (read_result fp.jc_cx)) (es,s)
    (\res ee u. res = INL (default_value tv) /\
       ee = es with gas_obs := [] /\ u = s) (\res ee r. F)` by
    (simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
     simp[gas_summary_at_def,gas_marked_exec_def] >>
     qexists_tac `es` >>
     simp[gas_marked_path_def] >> metis_tac[fragGasPathTheory.gas_path_rules]) >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at (Pat `gas_outcome`)) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  irule gas_outcome_start_gas_obs >>
  rewrite_tac[eval_target_place_as_bind,vyperStateTheory.bind_assoc] >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome`)) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res` >> fs[intcall_stmt_exit_def] >>
      disj1_tac >> Cases_on `y` >> Cases_on `r` >>
      fs[exprSimDefsTheory.expr_exit_def] >>
      rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >>
      fs[exprSimDefsTheory.expr_exit_def]) >>
  rpt strip_tac >> gvs[] >>
  gvs[target_post_def] >>
  Cases_on `v` >> fs[place_ptr_rel_def] >>
  simp[vyperStateTheory.get_place_def,vyperStateTheory.bind_return] >>
  `!tail. eval_target_place fp.jc_cx bt
     (es with gas_obs := gas_explicit marks' s.vs_gas_readings ++ tail) =
     (INL p,mid' with gas_obs := tail)` by
    (fs[gas_marked_exec_def,eval_target_place_as_bind,
        vyperStateTheory.bind_def,vyperStateTheory.get_place_def,
        vyperStateTheory.return_def] >> metis_tac[]) >>
  `well_typed_target env bt dty` by simp[well_typed_target_def] >>
  `target_pre ce fp.jc_cx env bt
     (es with gas_obs := gas_explicit marks' s.vs_gas_readings)` by simp[] >>
  `eval_target_place fp.jc_cx bt
     (es with gas_obs := gas_explicit marks' s.vs_gas_readings) =
     (INL p,mid' with gas_obs := [])` by metis_tac[listTheory.APPEND_NIL] >>
  drule_all tuplePlaceSourceHeadTheory.tuple_place_source_target_endpoint >>
  strip_tac >>
  Cases_on `write_place fp.jc_cx p (default_value tv) (mid' with gas_obs := [])` >>
  rename1 `write_place _ _ _ _ = (wr,ff)` >>
  `wr = INL ()` by
    (irule tuple_place_source_write_success >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `eval_target_place _ _ _ = (INL _,_)` (irule_at Any) >>
     qpat_assum `target_pre _ _ _ _ (_ with gas_obs := _)` (irule_at Any) >>
     qexistsl_tac [`dty`,`tv`,`t`,`fp.jc_func`,`fp.jc_ctx`] >>
     simp[vyperTypingTheory.default_value_well_typed]) >> gvs[] >>
  `value_has_type tv (default_value tv)` by
    simp[vyperTypingTheory.default_value_well_typed] >>
  `expr_sim_inv ce fp.jc_cx env ff` by
    (irule tuplePlaceSourceHeadTheory.tuple_place_source_write_endpoint >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `eval_target_place _ _ _ = (INL _,_)` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `intcall_joint_res fp ce env (mid' with gas_obs := []) cs' t` by
    fs[intcall_joint_res_def,intcall_expr_cont_def] >>
  `has_length_word dty` by metis_tac[type_widens_to_has_length_word] >>
  `?loc. FST (SND tgt_result) = SOME loc` by
    (Cases_on `p` >> fs[place_ptr_rel_def]) >>
  gvs[] >>
  `loc <> LocCode /\ loc <> LocCalldata` by
    (Cases_on `p` >> fs[place_ptr_rel_def,slot_loc_def] >> gvs[AllCaseEqs()]) >>
  `acyclic_struct_metadata ce.ce_struct_fields` by fs[body_inv_def] >>
  `!id path entry t0.
    p = MemoryPlace id path /\ lookup_scopes id (mid' with gas_obs := []).scopes = SOME entry /\
    ce.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv fp.jc_cx) t0 = SOME entry.type` by
    (rpt strip_tac >> fs[] >>
     drule_all abiEncodeArgsSimTheory.abi_args_local_type_coherent >> strip_tac >> gvs[]) >>
  `fn_has_code cs' sb fp.jc_func` by metis_tac[fn_has_code_split] >>
  drule_at (Pat `compile_store_at_loc`) intcall_assign_empty_store_path >>
  disch_then (drule_at (Pat `write_place`)) >>
  disch_then (qspecl_then [`w`,`t`,`env`,`dty`,`ce`] mp_tac) >>
  (impl_tac >- fs[intcall_expr_cont_def]) >> strip_tac >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`,`ff`,`OK t'`] >>
  conj_tac
  >- (simp[gas_marked_exec_def] >>
      gen_tac >> drule tuple_place_write_gas_obs >> simp[]) >>
  simp[] >> disj1_tac >>
  simp[stmt_lands_def,cenv_top_ext_def] >>
  rpt conj_tac
  >- (`~block_is_terminated cs'` by
        metis_tac[tuplePlaceOpenTheory.tuple_place_target_ptr_open] >>
      qpat_x_assum `compile_store_at_loc _ _ _ _ _ = _` mp_tac >>
      Cases_on `loc` >>
      simp[compile_store_at_loc_def,comp_return_def] >> strip_tac >> gvs[] >>
      drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
      simp[venomInstTheory.is_terminator_def])
  >- (qpat_x_assum `intcall_joint_res _ _ _ ff _ _` mp_tac >>
      simp[intcall_joint_res_def,intcall_expr_res_def,
           exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
      strip_tac >> metis_tac[])
  >- (rpt strip_tac >>
      `not_fresh_at cs' x` by
        (irule stmtFragPtrTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[] >>
         qspecl_then [`bt`,`ce`,`sa`] mp_tac ci_mono_compile_get_target_ptr >>
         gvs[ci_mono_def]) >> simp[])
  >- fs[intcall_expr_cont_def]
QED

Finalise intcall_assign_base_empty_stmt_step
