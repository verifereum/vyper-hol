(* Linked compatible and bytestring local-memory copy route. *)
Theory bodyAssignNameCopyRouteMods
Ancestors
  bodyAssignNameLinkedSetup bodyFullPredsMods bodyFullPostsMods bodyAssignNameOutcomeMods
  bodyAssignNameCopyReadFrontierMods bodyAssignNameCopyReadMods bodyAssignNameCopyStoreInputMods
  bodyAssignNameCopyStoreEffectMods bodyAssignNameCopyInstallMods
  stmtSimAssignMem stmtSimAssignSource exprBodyPreProps aggregateEvaluatedLayout
  typedCopyCompatibility logArgumentTypeEval vyperTypeEvalCaseProofs
  exprSimWordArgs stateRelProj vyperStorageFootprint loweringPosts bodyPtrDefs
  freshWrites gasShadow vyperState venomState bodyDeclMemoryCore words
Libs monadsyntax

Theorem assign_name_copy_route_mods:
  linked_assign_name_context_mods mods exps cx id e
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    src tops bindings cenv env env' ret_ty RetQ es /\
  body_expr_full_ok_mods mods exps cx e /\
  FLOOKUP env.var_types id = SOME ty /\
  ~is_word_type ty /\
  0 < type_memory_bytes cenv ty /\
  (lowered_value_type cenv e = ty \/ is_bytestring_type ty) /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type ty /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
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
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty` by suspend "widen" >>
  `~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `type_widens_to _ (expr_type e) ty`
       (strip_assume_tac o REWRITE_RULE [vyperTypeSystemTheory.type_widens_to_def]) >>
     qpat_assum `type_widens_to _ (lowered_value_type cenv e) ty`
       (strip_assume_tac o REWRITE_RULE [vyperTypeSystemTheory.type_widens_to_def]) >>
     metis_tac[arg_type_fits_word_type]) >>
  pure_rewrite_tac [stmt_frag_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac assign_local_memory_widen_code_parts >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (opr,sm)` >>
  drule_all_then strip_assume_tac assign_name_shadow_value_rhs_mods >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by suspend "shadow" >>
  drule_then assume_tac assign_local_admissible_rhs >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  drule_all_then (mp_tac o BETA_RULE) assign_name_copy_read_frontier_mods >>
  disch_then (qspec_then `ty` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ReadQ _` >>
  irule assign_local_memory_full_outcome_mods >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ ReadQ _` (irule_at Any) >>
  qexists_tac `lctx` >> simp[] >> reverse conj_tac
  >- (simp[Abbr `ReadQ`, Excl "AND_IMP_INTRO"] >> rpt strip_tac >> goal_assum (drule_at Any)) >>
  suspend "continue"
QED

Resume assign_name_copy_route_mods[widen]:
  irule type_widens_to_trans >> qexists_tac `expr_type e` >> simp[] >>
  `well_formed_type (get_tenv cx) (expr_type e)` by
    (drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule expr_body_pre_mods_inv >>
     disch_then (strip_assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
     drule env_consistent_type_defs_get_tenv >> strip_tac >>
     drule_all checked_expr_type_well_formed >> simp[]) >>
  qpat_assum `lowered_value_type cenv e = expr_type e \/ _`
    (DISJ_CASES_THEN strip_assume_tac) >> simp[vyperTypeSystemTheory.type_widens_to_def]
QED

Resume assign_name_copy_route_mods[shadow]:
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o REWRITE_RULE [gas_shadow_stmt_def,gas_shadow_assignment_def,gas_shadow_expr_def]) >>
  `(gas_shadow_env T cenv).ce_var_type id = SOME ty /\
   FLOOKUP (gas_shadow_env T cenv).ce_vars id = SOME (PtrVar (Var p) cap)` by simp[] >>
  `~(has_length_word (expr_type (gas_shadow_expr e)) /\ is_empty_value_expr (gas_shadow_expr e)) /\
   (lowered_value_type (gas_shadow_env T cenv) (gas_shadow_expr e) = ty \/ is_bytestring_type ty)` by
    (pure_rewrite_tac[gas_shadow_expr_type] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `stmt_env cenv _ _ (Assign _ e) sa = _` kall_tac >>
  qpat_assum `stmt_env (gas_shadow_env T cenv) _ _ (Assign _ (gas_shadow_expr e)) _ = _`
    (mp_then (Pat `stmt_env _ _ _ _ _ = _`) mp_tac assign_local_memory_widen_code_parts) >>
  disch_then (qspecl_then [`shadow_func`,`p`,`cap`,`ty`] mp_tac) >>
  (impl_tac >- (simp[gas_shadow_expr_type] >> metis_tac[])) >>
  strip_tac >> gvs[gas_shadow_expr_type]
QED

Resume assign_name_copy_route_mods[continue]:
  qx_genl_tac [`marks`,`v`,`mid`,`Gi`,`ti`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ ReadQ _` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ReadQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `ReadQ`, Excl "AND_IMP_INTRO"] >> disch_tac >>
  qabbrev_tac `prefix = gas_explicit marks s0.vs_gas_readings` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
    expr_store_bound cx (post_value_type cenv e) v opr u /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gi ti u /\
    ptr_val_ok cx (post_value_type cenv e) v opr Gi ti u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e opr Gi u) /\
    mid.gas_obs = [] /\ ~u.vs_halted /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then (qx_choosel_then [`ff`,`entry`,`pt`,`rt`,`xs`,`sw`,`dw`]
    (map_every assume_tac o CONJUNCTS)) assign_name_copy_read_ready_mods >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ expr_store_bound _ _ _ _ _ /\ ghost_inv_at_mods _ _ _ _ _ _ _ _ _ /\ _`
    kall_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H0 ctx func cenv cx mid u` by
    (qpat_assum `expr_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_state) >>
  qpat_x_assum `opr = Var xs` SUBST_ALL_TAC >>
  `(vv_location vv = SOME LocMemory ==> w2n sw + type_memory_size rt <= u.vs_alloca_next)` by
    (disch_tac >> Cases_on `is_bytestring_type ty`
     >- (`eval_operand (Var xs) u = SOME sw` by simp[eval_operand_def] >>
         qpat_assum `is_bytestring_type ty /\ vv_location vv = SOME LocMemory ==> _` mp_tac >>
         (impl_tac >- simp[]) >> disch_then (qspecl_then [`rt`,`sw`] mp_tac) >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (DISJ_CASES_THEN assume_tac)
         >- (qpat_assum `0 < type_memory_size rt` mp_tac >> simp[]) >>
         once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
     `lowered_value_type cenv e = ty` by fs[] >>
     `evaluate_type (get_tenv cx) ty = SOME rt` by fs[] >>
     drule_all_then (qspec_then `v` assume_tac) val_store_size_non_bytestring >>
     qpat_assum `val_store_size rt v = type_memory_size rt` (fn eq =>
       qpat_assum `w2n sw + val_store_size rt v <= _` (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  drule_all assign_name_copy_store_input_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`sc`,`z`,`Gz`,`tz`,`ys`,`wy`] (map_every assume_tac o CONJUNCTS))) >>
  `alloca_inv z` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ u ==> _` (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `0 < type_memory_size tv` by fs[] >>
  drule_all assign_name_copy_store_effect_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`bytes`,`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "install"
QED

Resume assign_name_copy_route_mods[install]:
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `write_place cx (MemoryPlace id []) v mid = (INL (),ff)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn eq =>
       qpat_assum `write_place _ _ _ (mid with gas_obs := []) = _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post_mods H ctx func cenv cx e es sa sm s0 mid v (Var xs) u /\
     ghost_inv_at_mods (DF H) lo d cenv cx mid Gi ti u /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 Gi ti /\ s0.vs_alloca_next <= u.vs_alloca_next` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) u` by
    (qpat_assum `!bw capacity. d = SOME (bw,capacity) ==> allocas_from _ u` mp_tac >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM] >> disch_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ghost_kept_at lo cenv mid sm Gi ti u Gz tz`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_kept_at_def]) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u /\
       FLOOKUP Gz x = FLOOKUP Gi x /\ op_taint tz (Var x) = op_taint ti (Var x)` by
    (gen_tac >> disch_tac >> rpt conj_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  `!x. not_fresh_at sc x ==> FLOOKUP Gf x = FLOOKUP Gz x /\
       op_taint tf (Var x) = op_taint tz (Var x)` by
    (gen_tac >> disch_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  qexistsl_tac [`ff`,`t`,`Gf`,`tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `ff.storage_trace = mid.storage_trace` (once_rewrite_tac o single) >>
  qpat_assum `~t.vs_halted` (fn nh =>
    qpat_assum `~block_is_terminated sb` (fn nt =>
      qpat_assum `alloca_history func t` (fn ah => simp[NoAsms,nh,nt,ah]))) >>
  match_mp_tac (Q.INST [`opr` |-> `Var xs`]
    (SIMP_RULE (srw_ss()) [] (cj 3 assign_name_copy_install_mods))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!D d. ghost_inv_at_mods D _ d _ _ _ _ _ u ==> _`
        (qspecl_then [`D`,`d`] (drule_then ACCEPT_TAC))) >>
  qpat_assum `!i. ~(w2n dw <= i /\ _) ==> _`
    (ACCEPT_TAC o REWRITE_RULE [DE_MORGAN_THM])
QED

Finalise assign_name_copy_route_mods
