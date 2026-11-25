(* Linked AugAssign: use the same reached place throughout the load, RHS,
   operator, and writeback intervals. *)
Theory bodyPlaceAugAssignFullMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyPlacePairedStagesMods
  bodyPlaceWriteSourceMods bodyPlaceWriteRootReadyMods bodyPlaceRhsActiveMods
  bodyWritePlaceRunMods bodyAugIdentifiedStoreMods
  bodyAugMemoryRouteJoinMods bodyAugSlotRouteJoinMods bodyAugImmRouteJoinMods
  stmtSimAugAssignPlace stmtSimAugAssign bodyExprPreFacts exprBodyPreProps
  allocLimits vyperTypeSystem vyperTypeInvariants loweringPosts option
  bodyWriteTargetStageMods

Theorem place_augassign_full_mods:
  !mods exps cx ty bt bop e.
    (!ctx cenv src tops env es bindings s ret_ty env'.
       contract_inv mods exps ctx cenv cx /\
       module_body_inv mods src tops cenv cx /\
       expr_sim_inv_mods mods cenv cx env es /\
       body_const_cells_agree_mods mods cx env es /\
       supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
       EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
    (!s p t s3 cur t3 s4 ptv t4.
       eval_target_place cx bt s = (INL p,t) /\
       read_place cx p s3 = (INL cur,t3) /\
       place_type_value cx p s4 = (INL ptv,t4) ==>
       body_expr_full_ok_mods mods exps cx e) /\
    body_base_target_full_ok_mods mods exps cx bt ==>
    body_stmt_full_ok_mods mods exps cx (AugAssign ty bt bop e)
Proof
  rpt gen_tac >> disch_then (mk_asm "resolve") >> strip_tac >>
  rw[body_stmt_full_ok_mods_def] >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (AugAssign ty bt bop e))` by
    (asm "resolve" irule >> rpt (first_assum (irule_at Any))) >>
  asm_x "resolve" kall_tac >>
  drule_then (assume_tac o CONJUNCT1) aug_place_typing >>
  `is_word_type ty` by
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS) aug_place_typing >>
     drule_then assume_tac expr_sim_inv_mods_env >>
     `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
     `?tv. evaluate_type (get_tenv cx) ty = SOME tv` by
       metis_tac[assignable_type_well_formed, well_formed_type_def, IS_SOME_EXISTS] >>
     drule_all_then (ACCEPT_TAC o CONJUNCT1) well_typed_binop_augassign_is_word) >>
  `alloc_limits_target cenv bt /\ ~aug_assign_overlap cenv bt e` by
    fs[stmt_exprs_ok_flat, alloc_limits_stmt_def] >>
  `!i st. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env i st` by
    (match_mp_tac (GEN_ALL place_write_index_pre_mods) >>
     qpat_assum `type_place_target env bt = SOME _` (fn th => simp[th]) >>
     qpat_assum `supported_stmt _ _ (AugAssign _ _ _ _)` (irule_at Any) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_root cx bt ==>
     ?owner id off. target_root bt = TopLevelNameTarget (owner,id) /\
         cenv.ce_is_ctor /\ FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off)` by
    (match_mp_tac (GEN_ALL place_write_immutable_root_ready_mods) >>
     qpat_assum `type_stmt _ _ (AugAssign _ _ _ _) = _` (irule_at Any) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx env bt es` by
    (irule write_target_place_run_mods >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `type_place_target env bt = SOME _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!reads p mid. eval_target_place cx bt (es with gas_obs := reads) = (INL p,mid) ==>
      body_const_cells_agree_mods mods cx env mid /\ expr_body_pre_mods mods cenv cx env e mid` by
    (rpt gen_tac >> strip_tac >>
     `expr_sim_inv_mods mods cenv cx env (es with gas_obs := reads) /\
        body_const_cells_agree_mods mods cx env (es with gas_obs := reads)` by simp[] >>
     `IS_SOME (type_place_target env bt)` by simp[] >>
     drule_all_then strip_assume_tac bodyPlaceWriteSourceModsTheory.place_write_reached_source_mods >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule augassign_active_rhs_pre_mods >>
     qpat_assum `type_stmt _ _ (AugAssign _ _ _ _) = _` (irule_at Any) >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "paired_prefix"
QED

Resume place_augassign_full_mods[paired_prefix]:
  rw[stmt_frag_full_mods_def] >>
  drule_all_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`r`,`sT`,`shadow_sT`] (MAP_EVERY assume_tac o CONJUNCTS)))
    augassign_paired_stages_mods >>
  `write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx bt es st0 sa sT shadow_sa shadow_sT r s0 G0 tn0` by
    (simp[write_target_entry_mods_def] >>
     rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
     fs[ret_pc_ok_def] >> metis_tac[]) >>
  irule augassign_identified_store_mods >>
  qpat_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ (AugAssign _ _ _ _) = _` (irule_at Any) >>
  qexistsl_tac [`sb`,`lctx`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
  >~ [`FST (SND r) = NONE \/ _`]
  >- (qpat_x_assum `FST (SND r) = NONE /\ _ \/ _`
        (DISJ_CASES_THEN2 (MAP_EVERY assume_tac o CONJUNCTS)
          (qx_choosel_then [`loc`,`old`,`rhsop`,`result`,`s1`,`s2`,`s3`,
                            `shadow_s1`,`shadow_s2`,`shadow_s3`]
             (MAP_EVERY assume_tac o CONJUNCTS)))
      >- (disj1_tac >> first_assum ACCEPT_TAC) >>
      disj2_tac >> qexistsl_tac [`loc`,`old`,`rhsop`,`result`,`s1`,`s2`,`s3`,
                                `shadow_s1`,`shadow_s2`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >> suspend "store"
QED

Resume place_augassign_full_mods[store]:
  qx_genl_tac [`p`,`value`,`ee`,`w`,`Gw`,`tnw`,`ptv`,`result`,`s3`] >>
  strip_tac
  >- (qpat_x_assum `p = StoragePlace _ _ _` SUBST_ALL_TAC >>
      irule (INST_TYPE [alpha |-> ``:data_location option # place_ty option``]
        augassign_slot_route_join_mods) >>
      rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
      >- (qexists_tac `ty` >> simp[])
      >- (qexistsl_tac [`ff`,`res`] >> first_assum ACCEPT_TAC)
      >- (qexistsl_tac [`r`,`result`,`s3`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`delta`,`path`,`root`,`rtv`] >> simp[])
  >- (qpat_x_assum `p = MemoryPlace _ _` SUBST_ALL_TAC >>
      irule augassign_memory_route_join_mods >>
      qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
      qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `evaluate_subscripts _ _ _ = _` (irule_at Any) >>
      qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
      qexistsl_tac [`ptv`,`mods`,`exps`,`env`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `p = ImmutablePlace _ _ _` SUBST_ALL_TAC >>
  irule (INST_TYPE [alpha |-> ``:data_location option # place_ty option``]
    augassign_immutable_route_join_mods) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
  >- (qexists_tac `target_tops` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `ff` >> first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`imms`,`itv`,`k`,`now`,`off`,`ptv`,`r`,`result`,`s3`,`ty`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`env`,`exps`,`mods`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise place_augassign_full_mods
