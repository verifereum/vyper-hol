(* Append executes the target before the RHS and reuses both reached posts. *)
Theory bodyPlaceAppendFullMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyPlacePairedStagesMods
  bodyPlaceWriteSourceMods bodyPlaceWriteRootReadyMods bodyPlaceRhsActiveMods
  bodyWritePlaceRunMods bodyWriteTargetStageMods bodyAppendStageJoinMods
  bodyAppendReachedFrameMods bodyAppendMemoryRouteJoinMods bodyAppendWordReplayMods
  bodyAppendCopyRouteJoinMods bodyPlaceWriteTailAdmissibleMods
  bodyAppendStorageFacts bodyExprPreFacts exprBodyPreProps exprSimHypsDefs
  loweringPosts bodySim allocLimits vyperTypeEnv vyperTypeInvariants vyperState
  targetPlaceSim targetPlaceSimCasesBase loweringStateRelDefs vyperTypeSystem
  vyperPlaceResultTyping placeTypingProps vyperAST exprLowering exprLoweringProps
  compileEnv stmtSimProps vyperStorageFootprint gasOutcomeFull finite_map option alist list
Libs
  monadsyntax pairLib

Theorem append_static_field_lookup[local]:
  !fields args fld fty.
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args /\
    ALOOKUP args fld = SOME fty ==>
    ?fsz. ALOOKUP fields fld = SOME (fty,fsz)
Proof
  Induct >> Cases_on `args` >> simp[] >>
  PairCases_on `h` >> gen_tac >> PairCases_on `h'` >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem append_typed_static_place_mods[local]:
  !bt mods cenv cx env es vt.
    expr_sim_inv_mods mods cenv cx env es /\ ~immutable_root cx bt /\
    type_place_target env bt = SOME vt ==>
    target_place_type cenv bt = SOME (value_type_place vt)
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- suspend "name"
  >- suspend "top"
  >- suspend "subscript" >>
  suspend "attribute"
QED

Resume append_typed_static_place_mods[name]:
  rpt gen_tac >> simp[type_place_target_NameTarget,target_place_type_def] >>
  strip_tac >> gvs[value_type_place_def] >>
  qhdtm_assum `expr_sim_inv_mods` (mp_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Resume append_typed_static_place_mods[top]:
  gen_tac >> PairCases_on `nsid` >> rpt gen_tac >> strip_tac >>
  rename1 `type_place_target env (TopLevelNameTarget (src,id)) = SOME vt` >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `!ts. get_module_code cx src = SOME ts ==> find_var_decl_by_name id ts <> NONE` by
    fs[immutable_root_def,target_root_def] >>
  drule_all_then strip_assume_tac toplevel_target_decl >> gvs[]
  >- (qhdtm_assum `expr_sim_inv_mods`
        (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
      qpat_assum `!src id ts tr typ id_str. _ ==> cenv.ce_hashmap_info _ = NONE /\ _`
        (drule_all_then strip_assume_tac) >>
      simp[target_place_type_def,value_type_place_def]) >>
  drule_all_then assume_tac type_place_target_global_lookup >>
  `place_map_tables_agree_on_defined cenv env` by fs[expr_sim_inv_mods_def] >>
  qpat_x_assum `place_map_tables_agree_on_defined _ _`
    (mp_tac o REWRITE_RULE [place_map_tables_agree_on_defined_def]) >>
  disch_then drule >> Cases_on `cenv.ce_hashmap_info (src,id)` >>
  simp[target_place_type_def,value_type_place_def] >> PairCases_on `x` >> simp[]
QED

Resume append_typed_static_place_mods[subscript]:
  simp[type_place_target_SubscriptTarget,immutable_root_def,target_root_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  rename1 `subscript_vtype base_vt (expr_type key) = SOME vt` >>
  Cases_on `base_vt` >> gvs[value_type_place_def,target_place_type_def,subscript_vtype_def,AllCaseEqs()] >>
  rename1 `subscript_vtype (Type ty) _ = _` >> Cases_on `ty` >>
  gvs[subscript_vtype_def,AllCaseEqs(),value_type_place_def]
QED

Resume append_typed_static_place_mods[attribute]:
  simp[type_place_target_AttributeTarget,immutable_root_def,target_root_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  Cases_on `tgt_ty` >> gvs[attribute_type_def,AllCaseEqs()] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_mods_def] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all_then strip_assume_tac append_static_field_lookup >>
  simp[target_place_type_def,value_type_place_def,get_struct_fields_def]
QED

Finalise append_typed_static_place_mods

Theorem place_append_full_mods:
  !mods exps cx bt e.
    (!ctx cenv src tops env es bindings s ret_ty env'.
       contract_inv mods exps ctx cenv cx /\
       module_body_inv mods src tops cenv cx /\
       expr_sim_inv_mods mods cenv cx env es /\
       body_const_cells_agree_mods mods cx env es /\
       supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
       EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
    body_base_target_full_ok_mods mods exps cx bt /\
    (!s p s'. eval_target_place cx bt s = (INL p,s') ==>
              body_expr_full_ok_mods mods exps cx e) ==>
    body_stmt_full_ok_mods mods exps cx (Append bt e)
Proof
  rpt gen_tac >> disch_then (mk_asm "resolve") >> strip_tac >>
  rw[body_stmt_full_ok_mods_def] >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (Append bt e))` by
    (asm "resolve" irule >> rpt (first_assum (irule_at Any))) >>
  asm_x "resolve" kall_tac >>
  drule_then (qx_choosel_then [`elem`,`cap`] strip_assume_tac) append_typing_target >>
  `alloc_limits_target cenv bt` by fs[stmt_exprs_ok_flat,alloc_limits_stmt_def] >>
  `!i st. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env i st` by
    (match_mp_tac (GEN_ALL place_write_index_pre_mods) >>
     qpat_assum `type_place_target env bt = SOME _` (fn th => simp[th]) >>
     qpat_assum `supported_stmt _ _ (Append _ _)` (irule_at Any) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_root cx bt ==>
     ?owner id off. target_root bt = TopLevelNameTarget (owner,id) /\
         cenv.ce_is_ctor /\ FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off)` by
    (match_mp_tac (GEN_ALL place_write_immutable_root_ready_mods) >>
     qpat_assum `type_stmt _ _ (Append _ _) = _` (irule_at Any) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `~immutable_root cx bt` by
    (strip_tac >> qpat_assum `immutable_root cx bt ==> _` (drule_then strip_assume_tac) >>
     fs[stmt_exprs_ok_flat,alloc_limits_stmt_def,popTargetPreTheory.target_in_immutables_root]) >>
  `target_place_type cenv bt = SOME (ValPT (ArrayT elem (Dynamic cap)))` by
    (drule_all_then (ACCEPT_TAC o REWRITE_RULE [value_type_place_def])
       append_typed_static_place_mods) >>
  `assignable_type (get_tenv cx) elem` by
    (drule_then assume_tac expr_sim_inv_mods_env >>
     fs[env_consistent_def,env_context_consistent_def]) >>
  `write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es` by
    (irule write_target_place_run_mods >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  suspend "paired_prefix"
QED

Resume place_append_full_mods[paired_prefix]:
  rw[stmt_frag_full_mods_def] >>
  drule_all_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`r`,`sp`,`shadow_sp`,`loc`,`elem'`,`cap'`,`op`,`sm`,`shadow_sm`]
        (MAP_EVERY assume_tac o CONJUNCTS)))) append_paired_stages_mods >>
  `write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx bt es st0 sa sp shadow_sa shadow_sp r s0 G0 tn0` by
    (simp[write_target_entry_mods_def] >> conj_tac >- fs[ret_pc_ok_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  pure_rewrite_tac [GSYM append_exit_mods_def,ETA_AX] >>
  irule append_staged_store_mods >>
  qpat_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `type_place_target env bt = SOME _` (irule_at Any) >>
  qexistsl_tac [`sm`,`shadow_sm`,`sb`,`op`,`lctx`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
  >- suspend "store"
  >- suspend "rhs_source" >>
  pure_rewrite_tac [LET_THM] >>
  qpat_assum `elem' = _` (fn th => pure_rewrite_tac [SYM th]) >>
  qpat_assum `cap' = _` (fn th => pure_rewrite_tac [SYM th]) >>
  qpat_assum `loc = _` (fn th => pure_rewrite_tac [SYM th]) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  conj_tac >- (pure_rewrite_tac [append_rhs_code_mods_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pure_rewrite_tac [append_store_code_mods_def] >>
  Cases_on `is_word_type elem'`
  >- (qpat_x_assum `if is_word_type elem' then _ else _` mp_tac >> simp[]) >>
  qpat_x_assum `if is_word_type elem' then _ else _` mp_tac >>
  simp[] >> disch_then (qx_choosel_then [`tmp`,`sc`,`sd`,`scs`,`sds`]
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`tmp`,`sc`,`sd`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume place_append_full_mods[rhs_source]:
  qx_genl_tac [`marks`,`p`,`mid`,`Gm`,`tm`,`t`] >> strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `mid with gas_obs := [] = mid` (fn eq =>
    qpat_assum `!tail. eval_target_place _ _ _ = _`
      (qspec_then `[]` (assume_tac o PURE_REWRITE_RULE [APPEND_NIL,eq]))) >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `IS_SOME (type_place_target env bt)` by simp[] >>
  drule_all_then strip_assume_tac bodyPlaceWriteSourceModsTheory.place_write_reached_source_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule append_active_rhs_pre_mods >>
  qpat_assum `type_stmt _ _ (Append _ _) = _` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume place_append_full_mods[store]:
  qx_genl_tac [`l`,`marks`,`p`,`mid`,`Gm`,`tm`,`t`,`rhsmarks`,`v`,`ee`,`G`,`tn`,`u`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then strip_assume_tac append_reached_store_frame_mods >>
  drule_then strip_assume_tac append_rhs_code_view_mods >>
  drule_all_then assume_tac append_reached_append_admissible_mods >>
  `!n b sz. local_region cenv ee.scopes u n b sz <=> local_region cenv es.scopes s0 n b sz` by
    (rpt gen_tac >> qpat_assum `!n b sz. local_region _ es.scopes s0 _ _ _ <=> _`
      (qspecl_then [`n`,`b`,`sz`] (ACCEPT_TAC o SYM))) >>
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  qpat_x_assum `(?id path. p = MemoryPlace id path /\ l = LocMemory) \/ _`
    (DISJ_CASES_THEN2
      (qx_choosel_then [`id`,`path`] (CONJUNCTS_THEN SUBST_ALL_TAC))
      (qx_choosel_then [`tr`,`slot`,`leaf`] (CONJUNCTS_THEN SUBST_ALL_TAC)))
  >- suspend "memory" >>
  Cases_on `is_word_type elem`
  >- suspend "word" >>
  suspend "copy"
QED

Resume place_append_full_mods[memory]:
  irule append_memory_route_join_mods >>
  qpat_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `!id path. MemoryPlace _ _ = MemoryPlace id path ==> _`
    (qspecl_then [`id`,`path`] mp_tac) >> (impl_tac >- REFL_TAC) >>
  disch_then (qx_choosel_then [`initial`,`v0`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v0`,`tm`,`t`,`sm`,`shadow_sm`,`rhsmarks`,`op`,`initial`,`exps`,`elem`,`cap`,`Gm`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume place_append_full_mods[word]:
  irule (Q.INST [`cenv0` |-> `cenv`] append_slot_word_replay_join_mods) >>
  qpat_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,`tm`,`t`,`sm`,`op`,
                `gas_explicit rhsmarks t.vs_gas_readings`,`elem`,`cap`,`Gm`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  irule cenv_top_ext_refl
QED

Resume place_append_full_mods[copy]:
  irule (Q.INST [`cenv0` |-> `cenv`] append_slot_copy_route_join_mods) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,`tm`,`sp`,`sm`,`t`,`op`,
                `slot_loc tr`,`gas_explicit rhsmarks t.vs_gas_readings`,`elem`,`r`,`cap`,`bt`,`Gm`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  irule cenv_top_ext_refl
QED

Finalise place_append_full_mods
