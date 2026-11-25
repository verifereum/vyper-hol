Theory bodyNormalHeadTailMods
Ancestors
  bodyExprPreFacts bodyFullPredsMods bodyFullPostsMods bodyInvExecutionProps
  constSubstCorrect vyperConstantFoldReplay vyperTypeContractStaticMaps
  vyperTypeEnvExtension vyperTypeEvalSoundness vyperTypeInvariants
  vyperEvalOutcomeSuffix vyperCallOutcomeStorage exprOracleStorageInterfaces
  vyperTypeCallStackSoundness vyperSubscriptOverlap alist finite_map placeTypingProps
  vyperState vyperAST vyperTypeContract vyperTypeExprSoundness exprSimHypsDefs
  vyperTypeSystem stmtLowering stmtSimProps allocLimits bodySim compileEnv
  supportedStmts supportedStmtTraverse vyperTypeCallGraph

(* Project only the immutable slot of the current account. *)
Theorem constant_slot_lookup_frame[local]:
  protected_cell_frame addr src id st st' ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP st'.immutables addr of NONE => empty_immutables | SOME imms => imms)) id =
  FLOOKUP (get_source_immutables src
    (case ALOOKUP st.immutables addr of NONE => empty_immutables | SOME imms => imms)) id
Proof
  Cases_on `ALOOKUP st.immutables addr` >>
  Cases_on `ALOOKUP st'.immutables addr` >>
  simp[protected_cell_frame_def, empty_immutables_def, get_source_immutables_def]
QED

Theorem constants_fold_module_key_origin_mods[local]:
  !mods imms src ts acc out id.
    constants_fold_module mods imms src ts acc = SOME out /\ id IN FDOM out ==>
    id IN FDOM acc \/ ?vis e ty init. MEM (VariableDecl vis (Constant e) id ty init) ts
Proof
  ho_match_mp_tac constants_fold_module_ind >>
  rw[constants_fold_module_def] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
  metis_tac[]
QED

(* Constructor execution can change other immutables. Re-run each fold
   against the new slot using just the unchanged declared constant cells. *)
Theorem constant_module_fold_frame[local]:
  check_contract mode cx.layouts cx.txn.target mods = SOME art /\
  MEM (src,tops) mods /\
  constants_fold_module mods imms src tops FEMPTY = SOME A /\
  A SUBMAP get_source_immutables src imms /\
  (!sid id. declared_constant mods sid id ==>
    FLOOKUP (get_source_immutables sid imms') id =
    FLOOKUP (get_source_immutables sid imms) id) ==>
  constants_fold_module mods imms' src tops FEMPTY = SOME A /\
  A SUBMAP get_source_immutables src imms'
Proof
  strip_tac >>
  `ALOOKUP mods src = SOME tops` by
    (drule_then assume_tac check_contract_runtime_namespaces >>
     irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
  conj_tac
  >- (irule constants_fold_module_replay_present >> reverse conj_tac
      >- (qexists `imms` >> simp[]) >>
      rpt strip_tac >> drule_all check_contract_toplevel_decl_MEM_checked >>
      simp[check_toplevel_decl_def]) >>
  simp[SUBMAP_FLOOKUP_EQN] >> rpt strip_tac >>
  `declared_constant mods src x` by
    (`x IN FDOM A` by metis_tac[flookup_thm] >>
     drule_all constants_fold_module_key_origin_mods >> simp[declared_constant_def] >>
     metis_tac[]) >>
  metis_tac[SUBMAP_FLOOKUP_EQN]
QED

Theorem body_const_cells_agree_mods_stmt:
  body_const_cells_agree_mods mods cx env es /\
  type_stmt env ret_ty s = SOME env1 /\ eval_stmt cx s es = (res,es1) ==>
  body_const_cells_agree_mods mods cx env1 es1
Proof
  strip_tac >>
  drule_then strip_assume_tac type_stmt_env_preserved_static >>
  qpat_x_assum `body_const_cells_agree_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  `!addr src id. declared_constant mods src id ==>
      protected_cell_frame addr src id es es1` by
    (rpt strip_tac >>
     `checked_frame_context cx mods art src id env` by
       (simp[checked_frame_context_def] >> metis_tac[]) >>
     drule (cj 1 checked_protected_cell_frame_mutual) >>
     disch_then (drule_at (Pat `checked_frame_context _ _ _ _ _ _`)) >>
     simp[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  qabbrev_tac `imms1 = case ALOOKUP es1.immutables cx.txn.target of
                         NONE => empty_immutables | SOME cells => cells` >>
  `!sid id. declared_constant mods sid id ==>
      FLOOKUP (get_source_immutables sid imms1) id =
      FLOOKUP (get_source_immutables sid imms) id` by
    (unabbrev_all_tac >> rpt strip_tac >>
     qpat_assum `imms = _` SUBST1_TAC >>
     irule constant_slot_lookup_frame >> simp[]) >>
  simp[body_const_cells_agree_mods_def] >>
  qexists `roots` >>
  rpt conj_tac
  >- (irule type_stmt_frame_maps >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      drule_all constant_module_fold_frame >> metis_tac[])
  >- (rpt strip_tac >> irule checked_frame_context_type_stmt >>
      goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  irule protected_cell_frame_cells_agree >> qexists `es` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  first_x_assum drule >> simp[checked_frame_context_def]
QED

Theorem normal_stmt_runtime_mods[local]:
  type_stmt env ret_ty s = SOME env1 /\
  call_evaluation_safe cx (int_calls_stmt s) /\
  eval_stmt cx s es = (INL (),es1) /\
  env_consistent env cx es /\ state_well_typed es /\
  accounts_well_typed es.accounts /\ context_well_typed cx /\
  functions_well_typed cx /\ popped_keys_indexed es.scopes /\
  outcomes_accounts_typed es.outcomes /\ IS_SOME es.outcomes ==>
  env_consistent env1 cx es1 /\ state_well_typed es1 /\
  accounts_well_typed es1.accounts /\ popped_keys_indexed es1.scopes /\
  outcomes_accounts_typed es1.outcomes /\ IS_SOME es1.outcomes
Proof
  strip_tac >> drule_all_then strip_assume_tac (cj 1 eval_scc_type_sound_mutual) >>
  fs[] >>
  `popped_keys_indexed es1.scopes` by
    (irule (cj 1 eval_stmts_popped_keys_indexed) >>
     goal_assum (drule_at (Pat `eval_stmt _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >>
     simp[runtime_consistent_def]) >>
  drule_then assume_tac (cj 1 eval_outcome_suffix_mutual) >>
  `outcomes_accounts_typed es1.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[outcomes_accounts_typed_def]) >>
  drule_all_then assume_tac outcome_suffix_IS_SOME >> simp[]
QED

Theorem normal_stmt_local_tables[local]:
  type_stmt env ret_ty s = SOME env1 /\ stmt_env cenv lctx ret_ty s sa = (c,sm) /\
  cenv.ce_alloca_locals /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
      ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> cenv.ce_var_type id = SOME ty) ==>
  (!id ty. FLOOKUP env1.var_types id = SOME ty ==>
      ?p sz. FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  (!id ty. FLOOKUP env1.var_types id = SOME ty ==> c.ce_var_type id = SOME ty)
Proof
  strip_tac >> drule_then strip_assume_tac stmt_env_declare >>
  Cases_on `?id typ e. s = AnnAssign id typ e`
  >- (gvs[type_stmt_def, declare_stmt_local_def] >>
      drule_all_then strip_assume_tac declare_local_ptr >>
      drule_then assume_tac stmt_env_var_type >> gvs[decl_var_type_def] >>
      conj_tac >> rpt gen_tac >> rename1 `FLOOKUP _ n = SOME ty ==> _` >>
      Cases_on `n = id` >>
      simp[extend_local_def, FLOOKUP_UPDATE, combinTheory.C_THM,
           combinTheory.APPLY_UPDATE_THM] >> metis_tac[]) >>
  drule_all_then assume_tac declare_stmt_local_other >>
  drule_all_then assume_tac type_stmt_other >> gvs[]
QED

Theorem expr_sim_inv_mods_normal_stmt:
  expr_sim_inv_mods mods cenv cx env es /\
  same_frame cenv c /\ cenv.ce_alloca_locals /\
  type_stmt env ret_ty s = SOME env1 /\ call_evaluation_safe cx (int_calls_stmt s) /\
  eval_stmt cx s es = (INL (),es1) /\ stmt_env cenv lctx ret_ty s sa = (c,sm) ==>
  expr_sim_inv_mods mods c cx env1 es1
Proof
  simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all_then strip_assume_tac normal_stmt_runtime_mods >>
  drule_all_then strip_assume_tac normal_stmt_local_tables >>
  drule_then strip_assume_tac type_stmt_env_preserved_static >>
  fs[same_frame_def] >>
  qpat_assum `_ = cenv`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  drule_all_then (fn th => simp[th]) place_map_tables_agree_on_defined_cong >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem frame_ret_ok_full_mods_same_frame[local]:
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\ same_frame cenv c ==>
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ c ret_ty
Proof
  simp[frame_ret_ok_full_mods_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[same_frame_trans]
QED

Theorem unallocated_bare_global_root_tables[local]:
  c.ce_module_vars = cenv.ce_module_vars /\ env1.bare_globals = env.bare_globals ==>
  unallocated_bare_global_root c env1 = unallocated_bare_global_root cenv env
Proof
  strip_tac >> simp[FUN_EQ_THM] >> Cases >> simp[unallocated_bare_global_root_def]
QED

Theorem normal_head_tail_inputs_mods:
  eval_stmt cx s es = (INL (),es1) /\
  stmt_env cenv lctx ret_ty s sa = (c,sm) /\
  cenv_top_ext cenv c es1.scopes /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  supported_stmts tops bindings (s::ss) /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) (s::ss) ==>
     EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods cenv cx env es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty s = SOME env1 /\ type_stmts env1 ret_ty ss = SOME env' /\
  stmts_exprs_ok cenv (s::ss) /\
  ~supported_stmts_expr_exists (unallocated_bare_global_root cenv env) (s::ss) /\
  (!key. MEM (WriteAcc (StateRef key)) (accesses_stmts (s::ss)) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmts (s::ss)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty ==>
  contract_inv mods exps ctx c cx /\ module_body_inv mods src tops c cx /\
  supported_stmts tops bindings ss /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
     EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env1 es1 /\ expr_sim_inv_mods mods c cx env1 es1 /\
  ce_locals_declared c env1 /\ locals_alloc_ok c env1 /\
  type_stmts env1 ret_ty ss = SOME env' /\ stmts_exprs_ok c ss /\
  ~supported_stmts_expr_exists (unallocated_bare_global_root c env1) ss /\
  (!key. MEM (WriteAcc (StateRef key)) (accesses_stmts ss) /\
         IS_SOME (FLOOKUP env1.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP c.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ c ret_ty
Proof
  simp[supported_stmt_def, supported_stmt_expr_exists_def, stmts_exprs_ok_def,
       int_calls_stmt_def, accesses_stmt_def] >>
  strip_tac >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  drule_then assume_tac call_evaluation_safe_append_right >>
  drule_then assume_tac cenv_top_ext_same_frame >>
  drule_all_then strip_assume_tac body_inv_same_frame_mods >>
  drule_all_then assume_tac body_const_cells_agree_mods_stmt >>
  `cenv.ce_alloca_locals` by (irule contract_inv_alloca_locals >> metis_tac[]) >>
  drule_all_then assume_tac expr_sim_inv_mods_normal_stmt >>
  drule_all_then assume_tac ce_locals_declared_stmt >>
  drule_all_then assume_tac locals_alloc_ok_stmt >>
  drule_all_then assume_tac frame_ret_ok_full_mods_same_frame >>
  drule_all_then assume_tac stmt_env_stmts_exprs_ok >>
  drule_then strip_assume_tac type_stmt_env_preserved_static >>
  `c.ce_module_vars = cenv.ce_module_vars` by
    (fs[same_frame_def] >> qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  drule_all_then assume_tac unallocated_bare_global_root_tables >>
  simp[] >> metis_tac[]
QED
