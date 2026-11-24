(* Linked local assignment with equal physical/annotated RHS types. *)
Theory bodyAssignNameEqualRhsWidenRouteMods
Ancestors
  bodyAssignNameLinkedSetup bodyAssignNameOutcomeMods bodyFullPostsMods
  bodyAssignNameEqualRhsWidenReadMods bodyAssignNameEqualRhsWidenSuffixMods
  assignRelayoutFrag assignPlaceEndpoint stmtSimDeclTypedCode stmtSimAssignSource
  gasShadow gasShadowCompileStmtBase gasOutcomeFullMods gasOutcomeFullPostMods
  fragGasOriginPtr fragGasMode bodyFullIfExpReach exprSimHypsDefs bodyInvCodeProps bodyPtrDefs
  stmtSimDefs loweringPosts vyperStorageFootprint vyperState venomState
Libs monadsyntax

(* Recover openness from the same normal path that supplies the RHS post. *)
Theorem assign_name_read_open[local]:
  cs_extends a b /\ fn_has_code a b func /\ ~block_is_terminated a /\
  s0.vs_current_bb = a.cs_current_bb /\ s0.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!H res ee G tn t. P H res ee G tn t ==>
    t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s0,G0,tn0) P R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s0,G0,tn0)
    (\H res ee G tn t. P H res ee G tn t /\ ~block_is_terminated b) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >>
      qpat_assum `!H res ee G tn t. P _ _ _ _ _ _ ==> _`
        (drule_then strip_assume_tac) >>
      drule_then assume_tac gas_origin_ptr_path_erase >>
      irule endpoint_path_open >>
      qexistsl_tac [`ctx`,`func`,`LENGTH marks`,`s0`,`a`,`t`] >>
      asm_rewrite_tac[gas_marked_path_def]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem assign_name_equal_rhs_widen_route_mods:
  linked_assign_name_context_mods mods exps cx id e
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    src tops bindings cenv env env' ret_ty RetQ es /\
  body_expr_full_ok_mods mods exps cx e /\
  FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
  0 < type_memory_bytes cenv ty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  lowered_value_type cenv e = expr_type e /\ expr_type e <> ty /\ ~is_bytestring_type ty ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac linked_assign_name_setup_mods >>
  `ty' = ty` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `ty' = ty` SUBST_ALL_TAC >>
  `contract_inv mods exps ctx cenv cx` by fs[linked_assign_name_context_mods_def] >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       len = type_memory_size tv) fields)` by
    (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_mods_def])
       exprBodyPrePropsTheory.expr_body_pre_mods_inv >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac assign_local_relayout_code_parts >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (opr,sm)` >>
  drule_all_then strip_assume_tac assign_name_shadow_value_rhs_mods >>
  rename1 `gas_shadow_state sm shadow_sm` >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by suspend "shadow" >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  drule_then assume_tac assign_local_admissible_rhs >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`opr`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all_then assume_tac gas_outcome_full_mods_return_buf_allocas >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G tn t. ?v. _) _` kall_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (mp_then (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`) mp_tac assign_name_read_open) >>
  disch_then (qspecl_then [`sm`,`sa`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt gen_tac >> strip_tac >> simp[])) >>
  disch_then (assume_tac o BETA_RULE) >>
  suspend "compose"
QED

Resume assign_name_equal_rhs_widen_route_mods[shadow]:
  qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  pure_rewrite_tac[gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def] >> strip_tac >>
  `expr_type (gas_shadow_expr e) = expr_type e` by simp[] >>
  `FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) cap)` by simp[] >>
  `(gas_shadow_env T cenv).ce_var_type id = SOME ty` by simp[] >>
  `~(has_length_word (expr_type (gas_shadow_expr e)) /\ is_empty_value_expr (gas_shadow_expr e))` by
    (pure_rewrite_tac[gas_shadow_expr_type,gas_shadow_is_empty_value_expr] >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac assign_local_relayout_code_parts >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _` mp_tac >> simp[]
QED

Resume assign_name_equal_rhs_widen_route_mods[compose]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ChildQ _` >>
  irule assign_local_memory_full_outcome_mods >>
  conj_tac >- (qexists_tac `lctx` >> first_assum ACCEPT_TAC) >>
  qexists_tac `\H res ee G tn t. ChildQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "continue" >>
  conj_tac >- (simp[Abbr `ChildQ`] >> metis_tac[]) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ ChildQ _` (irule_at Any) >> simp[]
QED

Resume assign_name_equal_rhs_widen_route_mods[continue]:
  qx_genl_tac [`marks`,`v`,`mid`,`Gi`,`ti`,`u`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` kall_tac >>
  qunabbrev_tac `ChildQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) [Excl "ADD_COMM"]) >>
  qabbrev_tac `prefix = gas_explicit marks s0.vs_gas_readings` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `~block_is_terminated sm` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC) >>
  `~block_is_terminated sb` by (drule_all compile_assign_value_typed_open >> simp[]) >>
  suspend "resources"
QED

Resume assign_name_equal_rhs_widen_route_mods[resources]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
      expr_store_bound cx (post_value_type cenv e) v opr u /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Gi ti u /\
      ptr_val_ok cx (post_value_type cenv e) v opr Gi ti u /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e opr Gi u) /\
      mid.gas_obs = [] /\ ~u.vs_halted /\
      u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `vv_location vv = vv_location vv` by REFL_TAC >>
  drule_all assign_name_equal_rhs_widen_read_mods >>
  disch_then (qx_choosel_then [`ff`,`entry`,`stv`,`xs`,`sw`,`dw`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "install"
QED

Resume assign_name_equal_rhs_widen_route_mods[install]:
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gi ti u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gi ti /\
    (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) u)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ~u.vs_halted /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `compile_assign_value cenv (Var p) LocMemory (Var xs) F (vv_location vv) ty
     (lowered_value_type cenv e) (type_memory_bytes cenv ty) sm = ((),sb)` by
    (qpat_assum `opr = Var xs` (fn eq => qpat_assum `compile_assign_value _ _ _ opr _ _ _ _ _ _ = _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  qexists_tac `ff` >> PURE_REWRITE_TAC [REFL_CLAUSE, IMP_CLAUSES] >>
  irule assign_name_equal_rhs_widen_suffix_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (fn th =>
    qpat_assum `compile_assign_value _ _ _ (Var xs) _ _ _ _ _ _ = _`
      (mp_then (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`) mp_tac th)) >>
  goal_assum (fn th =>
    qpat_assum `local_region _ _ _ _ _ _` (mp_then (Pat `local_region _ _ _ _ _ _`) mp_tac th)) >>
  goal_assum (fn th =>
    qpat_assum `lookup_scopes id mid.scopes = SOME entry`
      (mp_then (Pat `lookup_scopes _ _ = _`) mp_tac th)) >>
  qexistsl_tac [`tv`,`opr`,`prefix`,`stv`,`sw`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise assign_name_equal_rhs_widen_route_mods
