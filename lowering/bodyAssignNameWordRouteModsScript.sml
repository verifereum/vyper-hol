(* Linked assignment to a scalar local: use the same RHS endpoint and
   MSTORE for every valid storage horizon. *)
Theory bodyAssignNameWordRouteMods
Ancestors
  bodyAssignNameLinkedSetup bodyAssignLocalWordPathMods bodySimStmtFacts
  bodyFullShared bodyFullPostsMods bodyFullShadowBodyInv
  stmtSimAssign stmtSimAssignSource stmtSimDeclStore stmtSimAugAssign
  gasOutcomeFullMods gasOutcomeFullPostMods bodyAssignNameOutcomeMods
  gasShadowCompileStmtHelpers gasShadowState gasShadow
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperStorageTrace
  vyperStorageFootprint vyperLookup exprBodyPreProps exprSimHypsDefs
  exprLoweringProps loweringPosts loweringStateRelDefs fragGasOriginPtrExec
  stmtSimDefs stmtSimProps bodyPtrDefs abiValueEncoding
  gasStorage vyperInterpreter vyperState fragExec exprSimDefs
  bodyFullMemoryFrames bodyInvSplit bodyMemoryDefs contextCodegenRel
  fragGasOriginPtr compileEnv venomState stmtLowering

Theorem name_word_code_mods[local]:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)) shadow_sa =
      (gas_shadow_env T ce,shadow_sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  cenv.ce_var_type id = SOME (expr_type e) /\ is_word_type (expr_type e) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  gas_shadow_state sa shadow_sa ==>
  ce = cenv /\
  ?op sm shadow_sm.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\
    emit_void MSTORE [Var p;op] sm = ((),sb) /\
    cs_extends sa sm /\ fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\ gas_shadow_state sm shadow_sm
Proof
  strip_tac >> drule_all_then strip_assume_tac assign_local_word_code_parts >>
  qpat_x_assum `ce = cenv` SUBST_ALL_TAC >> simp[] >>
  rename1 `lower_value compile_expr cenv _ e sa = (op,sm)` >>
  drule_all_then strip_assume_tac assign_name_shadow_value_rhs_mods >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `is_word_type (expr_type (gas_shadow_expr e))` by simp[gas_shadow_expr_type] >>
     `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) cap)` by simp[] >>
     `(gas_shadow_env T cenv).ce_var_type id = SOME (expr_type (gas_shadow_expr e))` by
       simp[gas_shadow_expr_type] >>
     drule_all_then strip_assume_tac assign_local_word_code_parts >>
     gvs[gas_shadow_expr_type]) >>
  metis_tac[]
QED

Theorem name_word_rhs_typed_mods[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  FLOOKUP env.var_types id = SOME (expr_type e) /\ lookup_scopes id mid.scopes = SOME entry /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  entry.type = tv /\ value_has_type tv entry.value /\ value_has_type tv v /\
  well_formed_type_value tv
Proof
  strip_tac >>
  `(expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs) <=>
     expr_body_pre_mods mods cenv cx env e es)` by
    simp_tac (srw_ss()) [expr_body_pre_mods_def,expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] expr_body_pre_eval_mods) >>
  disch_then (drule_then strip_assume_tac) >>
  fs[expr_sim_inv_mods_def] >>
  `env.type_defs = get_tenv cx` by metis_tac[vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv] >>
  drule_all_then strip_assume_tac env_consistent_lookup_var_type >>
  fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, state_well_typed_def] >>
  drule_all_then strip_assume_tac scope_well_typed_lookup_scopes >> gvs[]
QED


Theorem assign_name_word_route_mods:
  linked_assign_name_context_mods mods exps cx id e
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    src tops bindings cenv env env' ret_ty RetQ es /\
  body_expr_full_ok_mods mods exps cx e /\
  FLOOKUP env.var_types id = SOME ty /\ is_word_type ty ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  strip_tac >> drule_all_then strip_assume_tac linked_assign_name_setup_mods >>
  `ty' = ty` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `ty' = ty` SUBST_ALL_TAC >>
  `expr_type e = ty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  qpat_x_assum `expr_type e = ty` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `linked_assign_name_context_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [linked_assign_name_context_mods_def]) >>
  rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`) >-
    (irule gas_outcome_full_mods_bad_nil >> simp[] >> gen_tac >>
     Cases_on `eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) (es with gas_obs := tail)` >>
     simp[] >>
     irule (INST_TYPE [alpha |-> ``:unit``] storage_trace_frame_preserves_bad_domain) >>
     qexistsl_tac [`eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)`,
                   `q`,`es with gas_obs := tail`] >> simp[evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    first_x_assum (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac name_word_code_mods >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  drule_then assume_tac assign_local_admissible_rhs >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ _ ExprR` >>
  drule_all_then (mp_tac o BETA_RULE) gas_outcome_full_mods_return_buf_allocas >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` kall_tac >>
  disch_tac >> qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ExprQ ExprR` >>
  qabbrev_tac `WordQ = \H res ee G tn t.
      ExprQ H res (ee with gas_obs := []) G tn t /\ ~t.vs_halted` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     WordQ ExprR` by
    (irule gas_outcome_full_mods_post_source >>
     qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ ExprQ ExprR` (irule_at Any) >>
     simp[Abbr `WordQ`] >> rpt strip_tac >>
     `ee with gas_obs := [] = ee` suffices_by simp[] >>
     simp[evaluation_state_component_equality]) >>
  irule assign_local_memory_full_outcome_mods >>
  conj_tac >- (qexists_tac `lctx` >> first_assum ACCEPT_TAC) >>
  qexists_tac `WordQ` >> reverse conj_tac
  >- (conj_tac >- (simp[Abbr `WordQ`, Abbr `ExprQ`, Excl "AND_IMP_INTRO"] >>
                   rpt strip_tac >> goal_assum (drule_at Any)) >>
      qpat_x_assum `Abbrev (ExprR = _)`
        (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      first_assum ACCEPT_TAC) >>
  suspend "normal"
QED

Resume assign_name_word_route_mods[normal]:
  map_every qx_gen_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `WordQ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, Abbr `WordQ`, Abbr `ExprQ`, Excl "AND_IMP_INTRO"] >> rpt strip_tac >>
  drule_all_then strip_assume_tac assign_local_continuation_all_tails >>
  `lookup_scopes id mid.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `lookup_scopes id (mid with gas_obs := []).scopes = SOME entry` by simp[] >>
  drule_all_then strip_assume_tac name_word_rhs_typed_mods >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx
      (mid with gas_obs := []) t` by fs[expr_post_mods_def,expr_post_def] >>
  `?dst. lookup_var p t = SOME dst` by
     (drule_all_then ACCEPT_TAC local_word_pointer_live) >>
  rename1 `find_containing_scope _ _ = SOME (pre,sc,entry,rest)` >>
  qabbrev_tac `out = mid with scopes :=
    pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest` >>
  qabbrev_tac `u = mstore (w2n dst) (typed_val_to_w256 tv v) t with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `tf = tn1 with t_mem := tn1.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst + 32}` >>
  qexistsl_tac [`out`,`u`,`G1`,`tf`] >>
  conj_tac >- simp[Abbr `out`,evaluation_state_fupdcanon] >>
  `out.storage_trace = mid.storage_trace` by simp[Abbr `out`] >>
  asm_rewrite_tac[] >> suspend "store_at_horizon"
QED

Resume assign_name_word_route_mods[store_at_horizon]:
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms, Excl "AND_IMP_INTRO"] >> strip_tac >>
  qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ t`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `local_ptrs_rel func cenv (mid with gas_obs := []).scopes t` by
    (drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
     first_assum ACCEPT_TAC) >>
  `32 <= cap` by
    (drule_all_then assume_tac abi_word_type_size >>
     drule_all_then strip_assume_tac nameLoweringPropsTheory.local_ptrs_rel_value >>
     qpat_assum `type_memory_size entry.type <= cap` mp_tac >>
     qpat_assum `entry.type = tv` (once_rewrite_tac o single) >> simp[]) >>
  `local_region cenv (mid with gas_obs := []).scopes t id (w2n dst) cap` by
    simp[local_region_def] >>
  `immutable_decl_sep_mods cenv cx (mid with gas_obs := []).scopes
     t.vs_vars t.vs_allocas t.vs_alloca_next` by
    (fs[immutable_frame_mods_def,immutable_alloca_sep_mods_def,
        immutable_decl_sep_mods_def,immutable_alloca_sep_def] >> metis_tac[]) >>
  `lo <= w2n dst` by
    (`0 < cap` by decide_tac >> `dead_lo_ok_mods H (DF H) lo cenv cx` by simp[] >>
     drule_all_then ACCEPT_TAC body_full_local_region_lower_bound_mods) >>
  `ptr_covers G1 tn1 p t 32` by
    (qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     disch_then (qspecl_then [`id`,`entry`,`p`,`cap`] mp_tac o cj 1) >> simp[] >>
     simp[ptr_covers_def] >> strip_tac >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    (`post_value_type cenv e = expr_type e` by (irule post_value_type_word >> simp[]) >>
     qpat_assum `expr_val_rel _ _ _ _ t` mp_tac >>
     qpat_assum `post_value_type cenv e = expr_type e` (once_rewrite_tac o single) >>
     disch_then (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
     qpat_assum `!vt. evaluate_type _ (expr_type e) = SOME vt ==> _`
       (qspec_then `tv` mp_tac) >> gvs[]) >>
  `op_taint tn1 op = {}` by fs[ptr_val_ok_def,post_value_type_word] >>
  `store_lays_out tv entry.type v` by metis_tac[store_lays_out_typed] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`sa`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `return_buf_frame d cenv sm t` by (drule return_buf_frame_frame >> simp[]) >>
  `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM es.scopes` by
    (drule_then mp_tac eval_read_preserves_scopes_dom >> simp[]) >>
  `return_buf_sep d cenv (mid with gas_obs := []) t` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- simp[arithmeticTheory.ADD_COMM] >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv (mid with gas_obs := []) t` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace) _ _ _ _ _ _`
       (mp_then Any irule stmtSimDefsTheory.alloca_frame_of_mem_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "word_write"
QED

Resume assign_name_word_route_mods[word_write]:
  `write_place cx (MemoryPlace id []) v (mid with gas_obs := []) = (INL (),out with gas_obs := [])` by
    simp[Abbr `out`,evaluation_state_fupdcanon] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
   value_has_type entry.type v` by
    (qpat_assum `entry.type = tv` (once_rewrite_tac o single) >> simp[]) >>
  `u = (mstore (w2n dst) (typed_val_to_w256 tv v) t with
        vs_inst_idx := LENGTH sb.cs_current_insts)` by simp[Abbr `u`] >>
  `tf = (tn1 with t_mem := tn1.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst + 32})` by
    simp[Abbr `tf`] >>
  drule_all
    (CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss()) [mem_path_offset_def,evaluate_subscripts_def]))
      (Q.INST [`path` |-> `[]`, `off` |-> `0`, `ptv` |-> `entry.type`,
               `old` |-> `entry.value`, `q` |-> `p`, `a` |-> `b`,
               `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
        assign_local_word_write_mods)) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  qpat_x_assum `u = _` kall_tac >> qpat_x_assum `tf = _` kall_tac >>
  qpat_x_assum `stmt_state_rel H _ _ _ _ (out with gas_obs := []) u`
    (assume_tac o PURE_REWRITE_RULE [exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  qpat_x_assum `alloca_frame cenv es sa s0 cenv (out with gas_obs := []) u`
    (assume_tac o PURE_REWRITE_RULE [alloca_frame_gas_obs]) >>
  `alloca_history func u` by
    (first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx (out with gas_obs := []) (FST H)` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ghost_kept_at_def]) >>
  asm_rewrite_tac[stmt_lands_def,cenv_top_ext_refl] >>
  rpt strip_tac >>
  `i IN tn1.t_mem` by
    (qpat_assum `_ SUBSET _` (irule o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
    (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Finalise assign_name_word_route_mods
