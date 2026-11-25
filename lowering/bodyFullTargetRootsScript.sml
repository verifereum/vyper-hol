(*
 * The roots of the joint target simulation: a local and a module variable
 * (storage, transient or a mapping) resolve with no code, so the joint
 * outcome is the empty path at the start state.  bodyPtrPopTargetSimRoots'
 * target_name_sim_ptr and target_toplevel_sim_ptr over target_sim_full.
 *
 * TOP-LEVEL:
 *   target_name_sim_full, target_toplevel_sim_full
 *)
Theory bodyFullTargetRoots
Ancestors
  bodyFullTargetDefs gasOutcomeFullCompose fragGasOriginPtr gasOutcomeFull
  bodyPtrDefs targetPlaceSim stmtSimAugAssign
  exprLoweringProps exprSimHypsDefs compileEnv
  loweringStateRelDefs loweringPosts exprLowering ptrDiscipline
  vyperTypeEnv vyperTyping vyperTypeSystem vyperPlaceResultTyping
  vyperTypeInvariants vyperInterpreter vyperState venomState
  bodySim bodyInvCodeProps bodyInvMetadataProps bodySimEntry bodyStorageMetadata
  bodyAugPlaceTarget constSubstCorrect targetPlaceSimCasesBase
  vyperTypeConstantCells bodyInvSplit finite_map option alist
  immutableDeployAssignFacts vyperFixedShapePath allocLimits stmtSimAssignAttr

(* The ghost invariant does not read the gas observations. *)
Theorem ghost_inv_at_gas_obs[local]:
  ghost_inv_at D lo d cenv cx (es with gas_obs := gs) G tn s <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_def]
QED

(* The roots have no emitted instructions. Keep their exact empty-run
   witness so that a scoped client need not infer confinement from a post. *)
Definition target_root_outcome_def:
  target_root_outcome bundle tops cx st0 sa sb source (es,s,G,tn) Q R <=>
    sb = sa /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ?res ee.
      (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
           Q H res (ee with gas_obs := []) G tn s)
End

Theorem target_name_root_outcome:
  target_pre cenv cx env (NameTarget id) es ==>
  target_sim_judgment target_root_outcome
    (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env (NameTarget id) es
Proof
  rw[target_sim_judgment_def, target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ (NameTarget _) sa = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  simp[target_root_outcome_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`] >>
  conj_tac
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def] >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (fs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     rpt strip_tac >> res_tac >>
     Cases_on `b` >> fs[vyperStorageBackendTheory.get_storage_def]) >>
  `?b. lookup_var p s0 = SOME b` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_origin_ptr_path_rules, ghost_kept_at_def, ghost_inv_at_gas_obs] >>
  rpt conj_tac >>
  TRY (qmatch_goalsub_rename_tac `target_ptr_ok _ _ _ _ _ _` >>
       qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
       simp[ghost_inv_at_def, ptr_covers_def, target_ptr_ok_def, op_prov_def] >>
       strip_tac >>
       qpat_x_assum `!name entry p sz. lookup_scopes _ _ = _ /\ _ ==> _`
         (qspecl_then [`id`, `entry`, `p`, `sz`] mp_tac) >>
       simp[] >> NO_TAC) >>
  simp[target_post_def, value_type_place_def, stmt_state_rel_start_gas_obs] >>
  simp[eval_operand_def, place_ptr_rel_def, mem_path_offset_def,
       place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, wordsTheory.WORD_ADD_0]
QED

Theorem compile_target_name_no_code:
  compile_get_target_ptr cfn cenv (NameTarget id) sa = (r,sb) ==> sb = sa
Proof
  simp[compile_get_target_ptr_def] >> Cases_on `FLOOKUP cenv.ce_vars id`
  >- simp[comp_return_def] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[comp_return_def]
QED

Theorem compile_target_toplevel_no_code:
  compile_get_target_ptr cfn cenv (TopLevelNameTarget nsid) sa = (r,sb) ==>
  sb = sa
Proof
  simp[compile_get_target_ptr_def, LET_THM] >>
  Cases_on `FLOOKUP cenv.ce_module_vars nsid`
  >- simp[comp_return_def] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[comp_return_def]
QED

Theorem target_toplevel_root_outcome:
  target_pre cenv cx env (TopLevelNameTarget (src,id)) es ==>
  target_sim_judgment target_root_outcome
    (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env (TopLevelNameTarget (src,id)) es
Proof
  rw[target_sim_judgment_def, target_pre_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts <> NONE` by
    (fs[immutable_root_def, target_root_def] >> metis_tac[]) >>
  drule compile_target_toplevel_no_code >> strip_tac >> gvs[] >>
  drule_all toplevel_target_decl >> strip_tac >> gvs[]
  >- suspend "storage" >>
  suspend "mapping"
QED

Resume target_toplevel_root_outcome[storage]:
  `cenv.ce_hashmap_info (src,id) = NONE /\
   cenv.ce_module_var_type (src,id) = SOME ty` by
    metis_tac[toplevel_target_env] >>
  qabbrev_tac `es1 = es with storage_trace :=
                 es.storage_trace ++ [StorageRoot tr slot tv]` >>
  simp[target_root_outcome_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tv))`, `es1`] >>
  conj_tac
  >- (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
        bind_def, ignore_bind_def, record_storage_event_def,
        lift_option_type_def, return_def, LET_THM, Abbr `es1`]) >>
  simp[] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    fs[Abbr `es1`, vyperStorageFootprintTheory.valid_horizon_def] >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  `storage_well_formed_on cx (es1 with gas_obs := []) (FST H)` by
    (fs[Abbr `es1`, vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     rpt strip_tac >> res_tac >>
     Cases_on `b` >> fs[vyperStorageBackendTheory.get_storage_def]) >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qspecl_then [`cenv`, `cx`, `src`, `id`, `ts`, `StorageVarDecl tr ty`,
               `id_str`, `tr`, `slot`] mp_tac toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (TopLevelNameTarget _) sa = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[gas_origin_ptr_path_rules, ghost_kept_at_def, target_post_def,
       stmt_state_rel_start_gas_obs, Abbr `es1`, eval_operand_def,
       place_ptr_rel_def, slot_loc_def, value_type_place_def,
       place_readable_def, target_ptr_ok_def, op_taint_def, op_prov_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  simp[] >> strip_tac >> fs[ghost_inv_at_def] >> metis_tac[]
QED

Resume target_toplevel_root_outcome[mapping]:
  `?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt')` by
    metis_tac[toplevel_target_env] >>
  simp[target_root_outcome_def] >>
  qexistsl_tac [`INL (HashMapRef tr (n2w slot) kt vt')`, `es`] >>
  conj_tac
  >- (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
        bind_def, lift_option_type_def, return_def, LET_THM]) >>
  simp[] >> gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (fs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     rpt strip_tac >> res_tac >>
     Cases_on `b` >> fs[vyperStorageBackendTheory.get_storage_def]) >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qspecl_then [`cenv`, `cx`, `src`, `id`, `ts`, `HashMapVarDecl tr kt vt'`,
               `id_str`, `tr`, `slot`] mp_tac toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (TopLevelNameTarget _) sa = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[gas_origin_ptr_path_rules, ghost_kept_at_def, target_post_def,
       stmt_state_rel_start_gas_obs, eval_operand_def,
       place_ptr_rel_def, slot_loc_def, value_type_place_def,
       place_readable_def, target_ptr_ok_def, op_taint_def, op_prov_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  simp[] >> strip_tac >> fs[ghost_inv_at_def] >> metis_tac[]
QED

Finalise target_toplevel_root_outcome

Theorem target_root_outcome_full:
  target_root_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 sa sb
    source (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    source (es,s,G,tn) Q R
Proof
  rw[target_root_outcome_def] >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G`, `ee`, `res`, `s`, `tn`] >>
  simp[gas_origin_ptr_path_rules]
QED

Theorem target_name_sim_full:
  target_pre cenv cx env (NameTarget id) es ==>
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env (NameTarget id) es
Proof
  strip_tac >> simp[target_sim_full_internal_def] >>
  irule target_sim_judgment_mono >> qexists_tac `target_root_outcome` >>
  simp[target_name_root_outcome, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> drule target_root_outcome_full >> simp[]
QED

Theorem target_toplevel_sim_full:
  target_pre cenv cx env (TopLevelNameTarget (src,id)) es ==>
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env (TopLevelNameTarget (src,id)) es
Proof
  strip_tac >> simp[target_sim_full_internal_def] >>
  irule target_sim_judgment_mono >> qexists_tac `target_root_outcome` >>
  simp[target_toplevel_root_outcome, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> drule target_root_outcome_full >> simp[]
QED

Theorem base_target_root_eq_target_root[local]:
  !bt. base_target_root bt = target_root bt
Proof
  recInduct base_assignment_target_induct >>
  simp[base_target_root_def, target_root_def]
QED

Theorem typed_immutable_target_root:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  immutable_root cx bt /\ IS_SOME (type_place_target env bt) ==>
  ?id root_ty. target_root bt = TopLevelNameTarget (NONE,id) /\
    FLOOKUP env.bare_globals (NONE,id) = SOME root_ty /\
    FLOOKUP env.bare_global_assignable (NONE,id) = SOME root_ty /\
    cx.in_deploy /\ cenv.ce_is_ctor /\ ~cx_const_name cx (NONE,id)
Proof
  strip_tac >> drule type_place_target_root >>
  simp[base_target_root_eq_target_root] >> strip_tac >>
  qpat_x_assum `immutable_root _ _`
    (strip_assume_tac o REWRITE_RULE[immutable_root_def]) >>
  drule_then (assume_tac o Q.SPEC `src` o
              MATCH_MP contract_inv_module_codes) body_inv_contract >>
  Cases_on `src` >> gvs[ALOOKUP_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `?ty. FLOOKUP env.bare_global_assignable (NONE,id) = SOME ty` by
    (Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
     gvs[] >> rename1 `type_place_target _ _ = SOME vt` >>
     Cases_on `vt` >> gvs[type_place_target_TopLevelNameTarget] >>
     fs[env_consistent_def, env_context_consistent_def]
     >- (qpat_assum `!src id ty. _ /\ _ ==> ?ts tr id_str.
             _ /\ find_var_decl_by_name _ _ = SOME (StorageVarDecl _ _,_) /\ _`
           (drule_all_then strip_assume_tac) >> gvs[]) >>
     qpat_assum `!src id kt vt. _ ==> ?ts tr id_str.
          _ /\ find_var_decl_by_name _ _ = SOME (HashMapVarDecl _ _ _,_) /\ _`
       (drule_all_then strip_assume_tac) >> gvs[]) >>
  `FLOOKUP env.bare_globals (NONE,id) = SOME ty` by
    (fs[env_consistent_def, env_context_consistent_def] >>
     qpat_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = SOME _ ==> _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  `cx.in_deploy` by
    (Cases_on `cx.in_deploy` >> gs[env_consistent_def, env_context_consistent_def,
                                  bare_global_assignable_complete_def]) >>
  `cenv.ce_is_ctor` by metis_tac[body_inv_contract, contract_inv_constructor] >>
  qexists_tac `ty` >> simp[] >> strip_tac >>
  drule_all_then strip_assume_tac body_inv_const_name_decl >>
  drule_then strip_assume_tac supported_variable_decl_mem >>
  drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
  gvs[] >>
  `?vis ty slot. MEM (VariableDecl vis Immutable id ty slot) tops` by
    (irule bare_global_clause_immutable >> simp[] >>
     qexistsl [`cx`,`env`,`es`] >> simp[]) >>
  drule body_inv_modules_aligned >>
  metis_tac[module_immutable_constant_names_distinct]
QED

Theorem immutable_toplevel_target_root_outcome:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  immutable_root cx (TopLevelNameTarget (NONE,id)) /\ ~cx_const_name cx (NONE,id) ==>
  imm_target_place_sim_judgment target_root_outcome
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (TopLevelNameTarget (NONE,id)) es
Proof
  strip_tac >> simp[imm_target_place_sim_judgment_def] >> rpt gen_tac >> strip_tac >>
  `IS_SOME (type_place_target env (TopLevelNameTarget (NONE,id)))` by simp[] >>
  drule_all_then strip_assume_tac typed_immutable_target_root >>
  gvs[target_root_def, type_place_target_TopLevelNameTarget] >>
  drule_all_then (strip_assume_tac o Q.SPEC `compile_expr`)
    immutable_assign_target_layout >>
  qpat_x_assum `compile_get_target_ptr _ _ (TopLevelNameTarget _) sa = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
  drule_all_then strip_assume_tac env_consistent_bare_global_ready_src >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables NONE imms) id` >>
  gvs[get_source_immutables_def] >>
  rename1 `_ = SOME entry` >> PairCases_on `entry` >>
  simp[target_root_outcome_def] >>
  qexistsl_tac [`INL (ImmutablePlace NONE id [])`,`es`] >>
  conj_tac >-
    (simp[Once evaluate_def, bind_def] >>
     simp[Once evaluate_def, lookup_global_def, get_immutables_def,
          get_address_immutables_def, get_place_def, bind_def, return_def,
          lift_option_type_def, lift_sum_def, get_source_immutables_def]) >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >>
  strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (fs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     rpt strip_tac >> res_tac >>
     Cases_on `b` >> fs[vyperStorageBackendTheory.get_storage_def]) >>
  `evaluate_type (get_tenv cx) root_ty = SOME entry0` by
    (fs[env_consistent_def, env_immutables_consistent_def, get_source_immutables_def] >>
     metis_tac[]) >>
  simp[imm_target_post_def, gas_origin_ptr_path_rules, ghost_kept_at_def,
       ghost_inv_at_gas_obs, target_ptr_ok_def, op_taint_def, op_prov_def,
       stmt_state_rel_start_gas_obs, eval_operand_def, target_root_def,
       mem_path_offset_def, evaluate_subscripts_def, get_source_immutables_def,
       fixed_shape_path_def]
QED

Theorem immutable_toplevel_target_sim_full:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  immutable_root cx (TopLevelNameTarget (NONE,id)) /\ ~cx_const_name cx (NONE,id) ==>
  imm_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (TopLevelNameTarget (NONE,id)) es
Proof
  strip_tac >> simp[imm_target_place_sim_full_internal_def] >>
  irule imm_target_place_sim_judgment_mono >>
  qexists_tac `target_root_outcome` >>
  simp[pairTheory.FORALL_PROD] >>
  conj_tac
  >- metis_tac[target_root_outcome_full] >>
  irule immutable_toplevel_target_root_outcome >> metis_tac[]
QED

Theorem immutable_target_place_type:
  !bt tops ctx cenv cx env es vt.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    immutable_root cx bt /\ type_place_target env bt = SOME vt ==>
    ?ty. vt = Type ty /\ target_place_type cenv bt = SOME (ValPT ty)
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- simp[immutable_root_def,target_root_def]
  >- (rpt gen_tac >> strip_tac >>
      `IS_SOME (type_place_target env (TopLevelNameTarget nsid))` by simp[] >>
      drule_all_then strip_assume_tac typed_immutable_target_root >>
      gvs[target_root_def,type_place_target_TopLevelNameTarget] >>
      `cenv.ce_hashmap_info (NONE,id) = NONE` by fs[expr_sim_inv_def] >>
      drule_all_then (strip_assume_tac o Q.SPEC `compile_expr`)
        immutable_assign_target_layout >>
      simp[target_place_type_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `immutable_root cx bt` by fs[immutable_root_def,target_root_def] >>
  gvs[Once well_typed_expr_def,AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
  >- (Cases_on `ty` >> gvs[subscript_vtype_def] >> simp[target_place_type_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  Cases_on `tgt_ty` >> gvs[attribute_type_def] >>
  `attribute_type (get_tenv cx) (StructT p) s = SOME ty` by
    simp[attribute_type_def] >>
  drule_all_then strip_assume_tac attribute_type_struct_field >>
  simp[target_place_type_def]
QED

Theorem immutable_target_base_place_result:
  !bt cx es pv ee.
    immutable_root cx bt /\ eval_base_place cx bt es = (INL pv,ee) ==>
    ?src id path. pv = PlaceR (ImmutablePlace src id path) /\
                  target_root bt = TopLevelNameTarget (src,id)
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- simp[immutable_root_def, target_root_def]
  >- (PairCases_on `nsid` >> simp[immutable_root_def, target_root_def] >>
      rpt strip_tac >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, lookup_global_def, bind_def,
           lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `FLOOKUP imms nsid1` >> gvs[return_def, raise_def]) >>
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ es = (INL pv,ee)` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `immutable_root cx bt` by fs[immutable_root_def,target_root_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, extend_memory_place_def, bind_def, ignore_bind_def,
       return_def, AllCaseEqs(), target_root_def] >> rpt strip_tac >> gvs[]
QED

Theorem immutable_target_attribute_source:
  immutable_root cx bt ==>
  eval_target_place cx (AttributeTarget bt fld) =
  bind (eval_target_place cx bt)
    (\p. bind (extend_place cx (PlaceR p) (AttrSubscript fld)) get_place)
Proof
  strip_tac >> simp[FUN_EQ_THM, Once evaluate_def] >> gen_tac >>
  simp[Once evaluate_def, Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt x` >> Cases_on `q` >> simp[] >>
  drule_all immutable_target_base_place_result >> strip_tac >>
  simp[get_place_def, return_def]
QED

Theorem immutable_target_subscript_source:
  immutable_root cx bt ==>
  eval_target_place cx (SubscriptTarget bt idx) =
  bind (eval_target_place cx bt) (\p.
    bind (eval_expr cx idx) (\raw. bind (read_result cx raw) (\v.
      bind (extend_place cx (PlaceR p) (ValueSubscript v)) get_place)))
Proof
  strip_tac >> simp[FUN_EQ_THM, Once evaluate_def] >> gen_tac >>
  simp[Once evaluate_def, Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt x` >> Cases_on `q` >> simp[] >>
  drule_all immutable_target_base_place_result >> strip_tac >>
  simp[get_place_def, return_def] >>
  Cases_on `eval_expr cx idx r` >> Cases_on `q` >> simp[] >>
  rename1 `eval_expr cx idx r = (INL raw,ix)` >>
  Cases_on `read_result cx raw ix` >> Cases_on `q` >> simp[]
QED

Theorem immutable_target_extend:
  FLOOKUP (get_source_immutables src imms) id = SOME (itv,iv) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  subscripts_type itv path = SOME ptv /\
  evaluate_subscripts itv iv path = INL value ==>
  bind (extend_place cx (PlaceR (ImmutablePlace src id path)) sb) get_place es =
    ((case evaluate_subscripts ptv value [sb] of
       INL _ => INL (ImmutablePlace src id (path ++ [sb]))
     | INR err => INR (Error err)), es)
Proof
  strip_tac >> Cases_on `evaluate_subscripts ptv value [sb]` >>
  simp[extend_place_def, place_type_value_def, read_place_def, get_immutables_def,
       get_address_immutables_def, extend_memory_place_def, get_place_def,
       bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def]
QED

Theorem immutable_target_fixed_snoc:
  fixed_shape_path itv path /\ mem_path_offset itv path = SOME (k,tv) /\
  mem_path_offset itv (path ++ [sb]) = SOME (k',tv') /\
  (~(?et n. tv = ArrayTV et (Dynamic n))) ==>
  fixed_shape_path itv (path ++ [sb])
Proof
  strip_tac >> imp_res_tac exprSimPropsTheory.mem_path_offset_sound >>
  fs[fixed_shape_path_append, fixed_shape_path_def,
       vyperPlaceStatePreservationTheory.subscripts_type_append,
       subscripts_type_def, AllCaseEqs(), SF CONJ_ss] >> metis_tac[]
QED
