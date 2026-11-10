(* Seam 2 joint induction, a family leaf of the stmt step: declarations and mutations. *)
Theory bodyIntCallFamStmtMutation
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtMutationEntry bodyIntCallFamStmtMutationResource
  bodyIntCallFamStmtMutationEffectful bodyIntCallFamStmtMutationBinop
  bodyIntCallFamStmtMutationLoad bodyIntCallFamStmtMutationAnn
  bodyIntCallFamStmtMutationFlatCopy bodyIntCallFamStmtMutationBytesFootprint
  bodyIntCallFamStmtMutationInactiveStore bodyIntCallFamStmtMutationWordInit
  bodyIntCallFamStmtMutationEmptyInit bodyIntCallFamStmtMutationStaging
  bodyIntCallFamStmtMutationCopyInit bodyIntCallFamStmtMutationAssignInit
  bodyIntCallFamStmtMutationAssignRun bodyIntCallFamStmtMutationSourceActivation
  bodyIntCallFamStmtMutationActivate bodyIntCallFamStmtMutationActivateTyping
  bodyIntCallFamStmtMutationLocalStore bodyIntCallFamStmtMutationResourceLanding
  bodyIntCallFamStmtMutationAppendSuffix bodyIntCallFamStmtMutationAppendExec
  bodyIntCallFamStmtMutationDeclEntry bodyIntCallFamStmtMutationDeclAlloc
  bodyAppendStorageAdapter bodyIntCallJointStmtSeq
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

Theorem intcall_append_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) ==>
  intcall_stmts_producer fp [Append tg rhs]
Proof
  strip_tac >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  gvs[supportedStmtsTheory.supported_stmt_def,
      vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  Cases_on `tg` >> gvs[supportedStmtsTheory.supported_append_target_def] >>
  rename1 `TopLevelNameTarget nid` >> Cases_on `nid` >>
  rename1 `TopLevelNameTarget (src,id)` >>
  `expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `type_stmt env fp.jc_ret_ty
     (Append (TopLevelNameTarget (src,id)) rhs) = SOME env'` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  drule_all bodyAppendStorageFactsTheory.body_append_target_bounds >> strip_tac >>
  `well_typed_expr env rhs` by
    metis_tac[bodyAppendStorageFactsTheory.append_typing_target] >>
  `supported_expr fp.jc_tops rhs` by
    simp[supportedExprsTheory.supported_expr_def] >>
  `call_evaluation_safe fp.jc_cx
     (int_calls_stmt (Append (TopLevelNameTarget (src,id)) rhs))` by
    (simp[vyperTypeCallGraphTheory.int_calls_stmt_def] >>
     fs[intcall_frame_ok_def,
        vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
     metis_tac[]) >>
  `expr_body_pre ce fp.jc_cx env rhs es` by
    (irule bodyAppendStorageAdapterTheory.body_append_expr_pre >>
     simp[] >>
     fs[supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
     metis_tac[]) >>
  suspend "code"
QED

Resume intcall_append_stmt_step[code]:
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
       exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  drule_all bodyAppendStorageFactsTheory.append_storage_compiler_location >>
  strip_tac >>
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
  qpat_x_assum `!e. intcall_expr_producer _ _ /\ _`
    (qspec_then `rhs` strip_assume_tac) >>
  qpat_x_assum `intcall_forced_producer _ _` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then drule_all >> strip_tac >>
  suspend "compose"
QED

Resume intcall_append_stmt_step[compose]:
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
  suspend "suffix"
QED

Resume intcall_append_stmt_step[suffix]:
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
    fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
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
  suspend "landing"
QED

Resume intcall_append_stmt_step[landing]:
  drule_all gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
  qpat_x_assum `eval_stmt _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `supported_stmt fp.jc_tops []
      (Append (TopLevelNameTarget (src,id)) rhs)` by
    simp[supportedStmtsTheory.supported_stmt_def,
         supportedStmtsTheory.supported_append_target_def] >>
  `expr_sim_inv ce fp.jc_cx env
      (es with gas_obs := gas_explicit (marks ++ marks') s.vs_gas_readings ++ [])` by
    simp[] >>
  `expr_sim_inv ce fp.jc_cx env' (raw with gas_obs := [])` by
    (drule_at (Pos (el 7)) bodyExprPreFactsTheory.expr_sim_inv_stmt >>
     disch_then irule >>
     fs[bodySimTheory.body_inv_def] >>
     conj_tac >- (qexists `[]` >> simp[]) >>
     qexistsl [`ce`, `env`,
       `es with gas_obs := gas_explicit (marks ++ marks') s.vs_gas_readings`,
       `lctx`, `fp.jc_ret_ty`, `sa`, `sb`] >>
     simp[] >>
     qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[loweringPostsTheory.stmt_env_def,
          stmtLoweringTheory.declare_stmt_local_def,
          stmtLoweringTheory.compile_stmt_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
          stmtLoweringTheory.target_root_type_def]) >>
  `env' = env` by
    fs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >> gvs[] >>
  `~block_is_terminated sb` by
    (irule appendStorageComposeFactsPtrTheory.primitive_append_nonterminator_open >>
     goal_assum (drule_at Any) >>
     Cases_on `tr` >> simp[venomInstTheory.is_terminator_def]) >>
  simp[loweringPostsTheory.stmt_lands_def, loweringPostsTheory.cenv_top_ext_def] >>
  suspend "resources"
QED

Resume intcall_append_stmt_step[resources]:
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
    (fs[compileEnvTheory.not_fresh_at_def] >> decide_tac) >>
  `lookup_var x t = SOME w` by metis_tac[] >>
  metis_tac[]
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
  cheat
QED
