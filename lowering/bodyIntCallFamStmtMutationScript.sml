(* Seam 2 joint induction, a family leaf of the stmt step: declarations and mutations. *)
Theory bodyIntCallFamStmtMutation
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtMutationEntry bodyIntCallFamStmtMutationResource
  bodyIntCallFamStmtMutationEffectful bodyIntCallFamStmtMutationAssign bodyIntCallFamStmtMutationBinop
  bodyIntCallFamStmtMutationLoad bodyIntCallFamStmtMutationAnn
  bodyIntCallFamStmtMutationBinopCont bodyIntCallFamStmtMutationAugLocalStore
  bodyIntCallFamStmtMutationAugLocalEntry bodyIntCallFamStmtMutationAugMemoryStore
  bodyIntCallFamStmtMutationAugStorageStore bodyIntCallFamStmtMutationAugTargetArray
  bodyIntCallFamStmtMutationAugTargetMappingFinish
  bodyIntCallFamStmtMutationAugTargetPrehash bodyIntCallFamStmtMutationAugTargetAttr
  bodyIntCallFamStmtMutationAugTargetAttrCounted
  bodyIntCallFamStmtMutationAugTargetCounted
  bodyIntCallFamStmtMutationAugPlaceProducer bodyIntCallFamStmtMutationAugLocal
  bodyIntCallFamStmtMutationFlatCopy bodyIntCallFamStmtMutationBytesFootprint
  bodyIntCallFamStmtMutationInactiveStore bodyIntCallFamStmtMutationWordInit
  bodyIntCallFamStmtMutationEmptyInit bodyIntCallFamStmtMutationEmptyProducer
  bodyIntCallFamStmtMutationStaging bodyIntCallFamStmtMutationInactiveCopy
  bodyIntCallFamStmtMutationCopyInit bodyIntCallFamStmtMutationAssignInit
  bodyIntCallFamStmtMutationAssignRun bodyIntCallFamStmtMutationSourceActivation
  bodyIntCallFamStmtMutationForcedInit bodyIntCallFamStmtMutationAggregateInit
  bodyIntCallFamStmtMutationBytesInit bodyIntCallFamStmtMutationBytesAssign
  bodyIntCallFamStmtMutationBytesContinuation bodyIntCallFamStmtMutationAnnProducer
  bodyIntCallFamStmtMutationActivate bodyIntCallFamStmtMutationActivateTyping
  bodyIntCallFamStmtMutationLocalStore bodyIntCallFamStmtMutationResourceLanding
  bodyIntCallFamStmtMutationAppendSuffix bodyIntCallFamStmtMutationAppendExec
  bodyIntCallFamStmtMutationAppendAggregateCompile
  bodyIntCallFamStmtMutationAppendAggregateStage
  bodyIntCallFamStmtMutationAppendAggregateCopy
  bodyIntCallFamStmtMutationAppendAggregatePrefix
  bodyIntCallFamStmtMutationAppendAggregatePost
  bodyIntCallFamStmtMutationAppendAggregateUnfresh
  bodyIntCallFamStmtMutationDeclEntry bodyIntCallFamStmtMutationDeclAlloc
  bodyAppendStorageAdapter bodyIntCallJointStmtSeq bodyIntCallPureLayout
  stmtReasonVvMemory exprSimSubscriptMap appendStorageComposeFactsPtr bodyMemAppendFacts

(* A pending declaration cannot use the current expression-producer entry.
   The new compile binding is present before the source local is introduced. *)
Theorem intcall_joint_res_requires_declared_binding:
  intcall_joint_res fp ce env es sa s /\
  FLOOKUP ce.ce_vars id = SOME loc ==>
  id IN FDOM env.var_types
Proof
  simp[intcall_joint_res_def, intcall_expr_res_def, bodySimTheory.ce_locals_declared_def] >>
  metis_tac[]
QED

Theorem intcall_append_rhs_pre:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sa s /\
  type_stmt env ret (Append tg rhs) = SOME env' /\
  supported_stmt fp.jc_tops bindings (Append tg rhs) /\
  stmt_exprs_ok ce (Append tg rhs) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Append tg rhs) ==> occurs_abi_decode_target target fp.jc_tops) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr rhs) ==>
  expr_body_pre ce fp.jc_cx env rhs es
Proof
  strip_tac >>
  `well_typed_expr env rhs` by
    (fs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs()] >>
     metis_tac[]) >>
  `supported_expr fp.jc_tops rhs` by
    fs[supportedStmtsTheory.supported_stmt_def,
       supportedExprsTheory.supported_expr_def] >>
  drule bodyExprPreFactsTheory.supported_expr_body_calls >> strip_tac >>
  irule (Q.INST [`calls` |-> `[]`]
    (SPEC_ALL bodyExprPreFactsTheory.stmt_expr_body_pre_alloc)) >>
  simp[] >>
  fs[intcall_joint_res_def,intcall_expr_res_def,
     bodySimTheory.stmt_exprs_ok_def,
     supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
     intcall_frame_ok_def,bodySimTheory.body_inv_def,
     gasContextTheory.cx_tops_def,
     vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def,
     allocLimitsTheory.alloc_limits_stmt_def] >>
  metis_tac[]
QED

Theorem intcall_append_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) ==>
  intcall_stmts_producer fp [Append tg rhs]
Proof
  strip_tac >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `type_stmt env fp.jc_ret_ty (Append tg rhs) = SOME env'` by
    gvs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs()] >>
  `supported_stmt fp.jc_tops bindings (Append tg rhs)` by
    fs[supportedStmtsTheory.supported_stmts_list] >>
  `expr_body_pre ce fp.jc_cx env rhs es` by
    (irule intcall_append_rhs_pre >>
     goal_assum (drule_at Any) >>
     fs[supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
        vyperTypeCallGraphTheory.int_calls_stmt_def] >>
     metis_tac[]) >>
  qpat_x_assum `supported_stmt _ _ _` mp_tac >>
  simp[Once supportedStmtsTheory.supported_stmt_def] >>
  Cases_on `tg` >> simp[] >>
  PairCases_on `p` >> rename1 `TopLevelNameTarget (src,id)` >>
  strip_tac
  >- (drule_all bodyAppendStorageFactsTheory.body_append_target_bounds >>
      strip_tac >> suspend "code") >>
  Cases_on `supported_storage_dynamic_array fp.jc_tops (src,id)`
  >- (drule_all bodyAppendStorageFactsTheory.body_append_target_bounds >>
      strip_tac >> suspend "code") >>
  suspend "aggregate_visible"
QED

Resume intcall_append_stmt_step[code]:
  markerLib.RESUME_TAC >>
  `is_word_type elem` by
    metis_tac[bodyAppendStorageFactsTheory.supported_append_element_layout] >>
  `type_memory_bytes ce elem = 32` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
  `get_module_code fp.jc_cx src = SOME fp.jc_tops` by
    (drule_all bodyAppendStorageFactsTheory.supported_append_storage_decl >>
     strip_tac >>
     drule bodyAppendStorageFactsTheory.supported_append_capacity_lookup >>
     strip_tac >> gvs[] >> fs[bodySimTheory.body_inv_def]) >>
  `storage_vars_rel ce fp.jc_cx /\ transient_vars_rel ce fp.jc_cx` by
    fs[intcall_joint_res_def, intcall_expr_res_def,
       exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  drule_all bodyAppendStorageFactsTheory.append_storage_compiler_location >>
  strip_tac >>
  `ce.ce_hashmap_info (src,id) = NONE` by
    (drule_all bodyAppendStorageFactsTheory.supported_append_storage_decl >>
     strip_tac >>
     drule_all bodyAppendStorageFactsTheory.body_append_root_metadata >>
     strip_tac >> simp[]) >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton] >> strip_tac >>
  drule_all stmtSimAppendStorageComposeTheory.append_storage_word_code_parts >>
  strip_tac >> gvs[] >>
  drule_all stmtSimAppendStorageComposeTheory.append_storage_word_code_frame >>
  strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx rhs) (read_result fp.jc_cx))
      expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  `supported_expr fp.jc_tops rhs` by
    fs[supportedExprsTheory.supported_expr_def] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr rhs)` by
    fs[vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  qpat_x_assum `!e. intcall_expr_producer _ _ /\ _`
    (qspec_then `rhs` strip_assume_tac) >>
  qpat_x_assum `intcall_forced_producer _ _` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then drule_all >> strip_tac >>
  suspend "compose"
QED

Resume intcall_append_stmt_step[compose]:
  markerLib.RESUME_TAC >> (
  rpt (qpat_x_assum `supported_variable_decl _ _ = _` kall_tac) >>
  rename1 `eval_target_place _ _ _ = (INL (StoragePlace tr (n2w slot) tv),_)` >>
  `eval_stmt fp.jc_cx (Append (TopLevelNameTarget (src,id)) rhs) =
     bind (bind (eval_expr fp.jc_cx rhs) (read_result fp.jc_cx))
       (append_place fp.jc_cx (StoragePlace tr (n2w slot) tv))` by
    metis_tac[stmtSimAppendStorageComposeTheory.append_toplevel_place_any,
              stmtSimAppendStorageComposeTheory.eval_append_storage_bind] >>
  asm_rewrite_tac[] >>
  drule (INST_TYPE [alpha |-> ``:unit``] gas_outcome_bind_value) >>
  disch_then irule >> reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      simp[intcall_stmt_exit_def] >> disj1_tac >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule bodyAppendStorageFactsTheory.append_typing_target >> strip_tac >>
  `env_consistent env fp.jc_cx es` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all bodyAppendStorageFactsTheory.body_append_runtime_metadata >>
  strip_tac >> gvs[] >>
  drule bodyAppendStorageFactsTheory.supported_append_element_layout >>
  disch_then (qspec_then `get_tenv fp.jc_cx` strip_assume_tac) >>
  `expr_type rhs = elem` by
    metis_tac[bodyAppendStorageFactsTheory.type_widens_to_word] >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  suspend "suffix")
QED

Resume intcall_append_stmt_step[suffix]:
  markerLib.RESUME_TAC >> (
  rename1 `type_slot_size etv = 1` >>
  `declared_storage_region fp.jc_cx src id [] =
    SOME (tr,n2w slot,ArrayTV etv (Dynamic (ce.ce_module_dynarray_capacity (src,id))))` by
    simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def,
         vyperValueTheory.evaluate_type_def] >>
  `encode_value etv v = SOME [(0,typed_val_to_w256 etv v)]` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     `expr_body_pre ce fp.jc_cx env rhs
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
     metis_tac[bodyAppendStorageAdapterTheory.body_append_word_encoding]) >>
  `eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_val_rel_def]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) t /\
   local_ptrs_reserved ce sb' /\ ~t.vs_halted /\
   t.vs_current_bb = sb'.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb'.cs_current_insts` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `~t.vs_call_ctx.cc_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `0 < type_slot_size (ArrayTV etv
      (Dynamic (ce.ce_module_dynarray_capacity (src,id))))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all appendStorageComposeFactsPtrTheory.declared_storage_head_agree >>
  strip_tac >>
  `ce.ce_module_dynarray_capacity (src,id) < dimword (:256)` by decide_tac >>
  drule_all intcall_append_storage_suffix_exec >>
  disch_then (mp_then Any mp_tac gas_outcome_conseq) >>
  disch_then irule >> conj_tac
  >- (rpt strip_tac >> simp[intcall_stmt_exit_def] >> disj1_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "landing")
QED

Resume intcall_append_stmt_step[landing]:
  markerLib.RESUME_TAC >> (
  `src = NONE` by metis_tac[bodySimTheory.body_inv_def] >> gvs[] >>
  drule_all gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
  qpat_x_assum `eval_stmt _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `supported_stmt fp.jc_tops []
      (Append (TopLevelNameTarget (NONE,id)) rhs)` by
    simp[supportedStmtsTheory.supported_stmt_def,
         supportedStmtsTheory.supported_append_target_def] >>
  `expr_sim_inv ce fp.jc_cx env
      (es with gas_obs := gas_explicit (marks ++ marks') s.vs_gas_readings ++ [])` by
    simp[] >>
  `expr_sim_inv ce fp.jc_cx env' (raw with gas_obs := [])` by
    (drule_at (Pos (el 8)) bodyExprPreFactsTheory.expr_sim_inv_stmt >>
     disch_then irule >>
     fs[bodySimTheory.body_inv_def] >>
     conj_tac
     >- (fs[intcall_frame_ok_def,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def,
            vyperTypeCallGraphTheory.int_calls_stmt_def] >>
         metis_tac[]) >>
     conj_tac >- (qexists `[]` >> simp[]) >>
     qexistsl [`ce`, `env`, `lctx`, `fp.jc_ret_ty`, `sa`, `sb`] >>
     simp[] >>
     qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[loweringPostsTheory.stmt_env_def,
          stmtLoweringTheory.declare_stmt_local_def,
          stmtLoweringTheory.compile_stmt_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def]) >>
  `env' = env` by
    (qpat_x_assum `type_stmt _ _ _ = SOME _` mp_tac >>
     simp[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
     metis_tac[]) >> gvs[] >>
  `~block_is_terminated sb` by
    (irule appendStorageComposeFactsPtrTheory.primitive_append_nonterminator_open >>
     goal_assum (drule_at Any) >>
     Cases_on `tr` >> simp[venomInstTheory.is_terminator_def]) >>
  simp[loweringPostsTheory.stmt_lands_def, loweringPostsTheory.cenv_top_ext_def] >>
  suspend "resources")
QED

Resume intcall_append_stmt_step[resources]:
  markerLib.RESUME_TAC >> (
  `intcall_joint_res fp ce env (mid with gas_obs := []) sb' t` by
    fs[intcall_joint_res_def, intcall_expr_cont_def] >>
  `sb'.cs_next_var <= sb.cs_next_var` by
    metis_tac[bodyMemAppendFactsTheory.append_storage_word_suffix_grows_mem] >>
  conj_tac
  >- (irule intcall_joint_res_storage_landing >>
      fs[intcall_joint_res_def, intcall_expr_res_def,
         compileEnvTheory.cs_extends_def] >>
      conj_tac
      >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
          qexists `sb'` >> simp[]) >>
      qexistsl [`env`, `mid with gas_obs := []`, `t`, `sb'`] >>
      simp[intcall_joint_res_def, intcall_expr_res_def] >>
      metis_tac[]) >>
  drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
  strip_tac >>
  fs[intcall_expr_cont_def] >>
  rpt strip_tac >>
  `not_fresh_at sb' x` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  `lookup_var x t = SOME w` by metis_tac[] >>
  metis_tac[])
QED

Resume intcall_append_stmt_step[aggregate_visible]:
  `~supported_full_word_type (expr_type rhs)` by
    (fs[supportedStmtsTheory.supported_append_target_def] >> gvs[]) >>
  `supported_stmt fp.jc_tops bindings
      (Append (TopLevelNameTarget (src,id)) rhs)` by
    fs[supportedStmtsTheory.supported_stmts_list] >>
  `mut = Storage \/ mut = Transient` by
    (fs[supportedStmtsTheory.supported_append_target_def] >> gvs[]) >>
  drule_at (Pos (el 3)) bodyAppendStorageFactsTheory.body_append_aggregate_metadata >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `storage_vars_rel ce fp.jc_cx /\ transient_vars_rel ce fp.jc_cx` by
    fs[intcall_joint_res_def,intcall_expr_res_def,
       exprLoweringPropsTheory.stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  `lowered_value_type ce rhs = expr_type rhs` by
    (`well_typed_expr env rhs /\
      sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
       fs[exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >>
     `!id ty. FLOOKUP env.var_types id = SOME ty ==>
        well_formed_type env.type_defs ty` by
       (rpt strip_tac >>
        `env_consistent env fp.jc_cx es` by
          fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
        drule_all exprSimSourceTheory.env_consistent_var_type_evaluates >>
        fs[vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_context_consistent_def,
           vyperTypeSystemTheory.well_formed_type_def]) >>
     drule_all pure_expr_lowered_type_compatible >> simp[]) >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton] >> strip_tac >>
  drule_all intcall_append_aggregate_compile >> strip_tac >>
  drule_all intcall_append_aggregate_code_frame >> strip_tac >> gvs[] >>
  suspend "aggregate_rhs"
QED

Resume intcall_append_stmt_step[aggregate_rhs]:
  markerLib.RESUME_TAC >> (
  `gas_admissible (bind (eval_expr fp.jc_cx rhs) (read_result fp.jc_cx))
      expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  `supported_expr fp.jc_tops rhs` by
    fs[supportedExprsTheory.supported_expr_def] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr rhs)` by
    fs[vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  qpat_x_assum `!e. intcall_expr_producer _ _ /\ _`
    (qspec_then `rhs` strip_assume_tac) >>
  qpat_x_assum `intcall_forced_producer _ _` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then drule_all >> strip_tac >>
  `eval_stmt fp.jc_cx (Append (TopLevelNameTarget (NONE,id)) rhs) =
     bind (bind (eval_expr fp.jc_cx rhs) (read_result fp.jc_cx))
       (append_place fp.jc_cx (StoragePlace tr (n2w off)
         (ArrayTV tv (Dynamic (ce.ce_module_dynarray_capacity (NONE,id))))))` by
    metis_tac[stmtSimAppendStorageComposeTheory.append_toplevel_place_any,
              stmtSimAppendStorageComposeTheory.eval_append_storage_bind] >>
  asm_rewrite_tac[] >>
  drule (INST_TYPE [alpha |-> ``:unit``] gas_outcome_bind_value) >>
  disch_then irule >> reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      simp[intcall_stmt_exit_def] >> disj1_tac >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `post_value_type ce rhs = expr_type rhs` by
    metis_tac[bodyExprPreFactsTheory.supported_pure_int_calls,
              exprSimHypsTheory.post_value_type_no_calls] >>
  gvs[] >>
  `type_memory_bytes ce (expr_type rhs) = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_body_pre_copy_ok] >>
  `?sw. eval_operand raw t = SOME sw /\
        val_in_memory tv v (w2n sw) t.vs_memory` by
    (qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
  `value_has_type tv v /\ val_wf tv v` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     `expr_body_pre ce fp.jc_cx env rhs
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
     drule (SRULE [SF ETA_ss] abiEncodeArgsCaseTheory.abi_args_success_ready) >>
     simp[] >> disch_then drule_all >> strip_tac >> gvs[]) >>
  `intcall_joint_res fp ce env (mid with gas_obs := []) sm t /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def,intcall_joint_res_def] >>
  `!lbl. raw <> Label lbl` by
    metis_tac[exprSimSliceCaptureTheory.slice_source_operand_not_label] >>
  `type_memory_bytes ce (expr_type rhs) < dimword (:256)` by
    (drule bodyAppendStorageFactsTheory.body_append_element_alloc_bound >>
     simp[wordsTheory.dimword_def]) >>
  `compile_alloc_buffer (type_memory_bytes ce (expr_type rhs)) sm = (buf,sn)` by
    metis_tac[] >>
  drule_at (Pos (el 6)) intcall_append_aggregate_stage >>
  disch_then drule_all >> strip_tac >>
  suspend "aggregate_suffix")
QED

Resume intcall_append_stmt_step[aggregate_suffix]:
  markerLib.RESUME_TAC >> (
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx (mid with gas_obs := []) t' /\
   local_ptrs_reserved ce sp /\
   expr_sim_inv ce fp.jc_cx env (mid with gas_obs := []) /\
   ~t'.vs_halted /\ t'.vs_current_bb = sp.cs_current_bb /\
   t'.vs_inst_idx = LENGTH sp.cs_current_insts` by
    (fs[intcall_joint_res_def,intcall_expr_res_def,intcall_expr_cont_def,
       exprLoweringPropsTheory.stmt_state_rel_def] >> metis_tac[]) >>
  `~t'.vs_call_ctx.cc_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    (qpat_assum `body_inv _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rewrite_tac[bodySimTheory.body_inv_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `value_has_type tv v /\ ?writes. encode_value tv v = SOME writes` by
    metis_tac[vyperTypingTheory.value_has_type_equiv, optionTheory.IS_SOME_EXISTS] >>
  `0 < type_slot_size (ArrayTV tv
      (Dynamic (ce.ce_module_dynarray_capacity (NONE,id))))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all appendStorageComposeFactsPtrTheory.declared_storage_head_agree >>
  strip_tac >>
  `(!x. buf.buf_operand = Var x ==> not_fresh_at sp x) /\
   w2n (n2w off : 256 word) + type_slot_size (ArrayTV tv
     (Dynamic (ce.ce_module_dynarray_capacity (NONE,id)))) <= dimword (:256) /\
   w2n w + type_memory_size tv < dimword (:256)` by
    (simp[wordsTheory.w2n_n2w] >>
     `off < dimword (:256)` by decide_tac >>
     simp[arithmeticTheory.LESS_MOD]) >>
  drule_all intcall_append_aggregate_suffix_exec_unfresh >>
  disch_tac >>
  irule stmtReasonVvMemoryTheory.gas_outcome_zero_prefix_any >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `gas_outcome _ _ _ _ (_,t') _ _`
    (mp_then Any mp_tac gas_outcome_conseq) >>
  disch_then irule >> conj_tac
  >- (rpt strip_tac >> simp[intcall_stmt_exit_def] >> disj1_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "aggregate_landing")
QED

Resume intcall_append_stmt_step[aggregate_landing]:
  markerLib.RESUME_TAC >> (
  drule_all stmtSimDeclGasTheory.gas_marked_exec_zero_prefix >> strip_tac >>
  drule_all gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
  qpat_x_assum `eval_stmt _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `supported_stmt fp.jc_tops []
      (Append (TopLevelNameTarget (NONE,id)) rhs)` by
    simp[supportedStmtsTheory.supported_stmt_def,
         supportedStmtsTheory.supported_append_target_def] >>
  `expr_sim_inv ce fp.jc_cx env
      (es with gas_obs := gas_explicit (marks ++ marks') s.vs_gas_readings ++ [])` by
    simp[] >>
  `expr_sim_inv ce fp.jc_cx env' (raw' with gas_obs := [])` by
    (drule_at (Pos (el 8)) bodyExprPreFactsTheory.expr_sim_inv_stmt >>
     disch_then irule >> fs[bodySimTheory.body_inv_def] >>
     conj_tac
     >- (fs[intcall_frame_ok_def,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def,
            vyperTypeCallGraphTheory.int_calls_stmt_def] >> metis_tac[]) >>
     conj_tac >- (qexists `[]` >> simp[]) >>
     qexistsl [`ce`, `env`, `lctx`, `fp.jc_ret_ty`, `sa`, `sb`] >> simp[] >>
     qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[loweringPostsTheory.stmt_env_def,stmtLoweringTheory.declare_stmt_local_def,
          stmtLoweringTheory.compile_stmt_def,compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_return_def]) >>
  `env' = env` by
    (qpat_x_assum `type_stmt _ _ _ = SOME _` mp_tac >>
     simp[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >> metis_tac[]) >> gvs[] >>
  `~block_is_terminated sb` by
    (drule intcall_append_aggregate_suffix_parts >> strip_tac >>
     drule_at (Pos hd) exprOpenPrimitivesTheory.emit_void_terminated >>
     Cases_on `tr` >> simp[venomInstTheory.is_terminator_def]) >>
  simp[loweringPostsTheory.stmt_lands_def, loweringPostsTheory.cenv_top_ext_def] >>
  suspend "aggregate_resources")
QED

Resume intcall_append_stmt_step[aggregate_resources]:
  markerLib.RESUME_TAC >> (
  conj_tac
  >- (irule intcall_joint_res_storage_landing >>
      fs[intcall_joint_res_def,intcall_expr_res_def] >>
      conj_tac
      >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
          qexists `sp` >> simp[]) >>
      qexistsl [`env`, `mid with gas_obs := []`, `t'`, `sp`] >>
      simp[intcall_joint_res_def,intcall_expr_res_def] >> metis_tac[]) >>
  fs[intcall_expr_cont_def] >>
  rpt strip_tac >>
  `not_fresh_at sm x /\ not_fresh_at sp x` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  metis_tac[])
QED

Finalise intcall_append_stmt_step

Theorem intcall_mutation_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  ((?x ty e. st = AnnAssign x ty e) \/ (?tg e. st = Assign tg e) \/
   (?ty tg op e. st = AugAssign ty tg op e) \/ (?tg e. st = Append tg e)) ==>
  intcall_stmts_producer fp [st]
Proof
  rpt strip_tac >> gvs[]
  >- (irule intcall_annassign_stmt_step >> simp[])
  >- (irule intcall_assign_stmt_step >> simp[])
  >- (Cases_on `?id. tg = NameTarget id`
      >- (gvs[] >> irule intcall_augassign_local_stmt_step >> simp[]) >>
      irule intcall_augassign_place_stmt_step >>
      conj_tac >- (MATCH_ACCEPT_TAC intcall_target_counted) >>
      fs[]) >>
  irule intcall_append_stmt_step >> simp[]
QED
