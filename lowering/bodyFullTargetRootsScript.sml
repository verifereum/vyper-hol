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
  bodyPtrPopTargetDefs bodyPtrDefs targetPlaceSim stmtSimAugAssign
  exprLoweringProps exprSimHypsDefs compileEnv
  loweringStateRelDefs loweringPosts exprLowering ptrDiscipline
  vyperTypeEnv vyperTyping vyperTypeSystem vyperPlaceResultTyping
  vyperTypeInvariants vyperInterpreter vyperState venomState

(* The ghost invariant does not read the gas observations. *)
Theorem ghost_inv_at_gas_obs[local]:
  ghost_inv_at D lo d cenv cx (es with gas_obs := gs) G tn s <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_def]
QED

Theorem target_name_sim_full:
  target_pre cenv cx env (NameTarget id) es ==>
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env (NameTarget id) es
Proof
  rw[target_sim_full_def, target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ (NameTarget _) sa = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (PlaceR (MemoryPlace id []))`, `s0`, `tn0`] >>
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

Theorem target_toplevel_sim_full:
  target_pre cenv cx env (TopLevelNameTarget (src,id)) es ==>
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env (TopLevelNameTarget (src,id)) es
Proof
  rw[target_sim_full_def, target_pre_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts <> NONE` by
    (fs[immutable_root_def, target_root_def] >> metis_tac[]) >>
  drule_all toplevel_target_decl >> strip_tac >> gvs[]
  >- suspend "storage" >>
  suspend "mapping"
QED

Resume target_toplevel_sim_full[storage]:
  `cenv.ce_hashmap_info (src,id) = NONE /\
   cenv.ce_module_var_type (src,id) = SOME ty` by
    metis_tac[toplevel_target_env] >>
  qabbrev_tac `es1 = es with storage_trace :=
                 es.storage_trace ++ [StorageRoot tr slot tv]` >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es1`, `INL (PlaceR (StoragePlace tr (n2w slot) tv))`,
                `s0`, `tn0`] >>
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

Resume target_toplevel_sim_full[mapping]:
  `?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt')` by
    metis_tac[toplevel_target_env] >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (HashMapRef tr (n2w slot) kt vt')`,
                `s0`, `tn0`] >>
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

Finalise target_toplevel_sim_full
