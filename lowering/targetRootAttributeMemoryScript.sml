(* Counted target roots and field extension. *)
Theory targetRootAttributeMemory
Ancestors
  targetMemoryContracts
  targetPlaceSim targetPlaceSimDefs exprSimDefs loweringPosts
  vyperTypeSystem exprLowering compileEnv stmtSimProps
  vyperInterpreter vyperState vyperEvalMisc loweringStateRelDefs
  venomState valueEncoding exprSimHypsDefs exprLoweringProps
  gasContext fragExec vyperTypeEnv vyperTypeInvariants vyperValue
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  accountsRelProps vyperStorageFootprint
  exprSimPopNestedBase
  gasOutcome gasSummary fragGasMode fragGasPath
Libs
  pairLib

Theorem target_name_memory:
  target_pre cenv cx env (NameTarget id) es /\
  type_place_target env (NameTarget id) = SOME vt /\
  compile_get_target_ptr compile_expr cenv (NameTarget id) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (NameTarget id)) target_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (eval_base_place cx (NameTarget id)) (es,s0)
    (\H res ee t. ?pv. res = INL pv /\
      target_post H ctx func cenv cx es sa sb s0 ee pv vt op t /\
      (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
        slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
        storage_read_live H tr (get_storage cx ee tr) slot tv) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  rw[target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[gasOutcomeTheory.gas_outcome_def, gasSummaryTheory.gas_summary_at_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def, fragGasPathMemTheory.gas_path_mem_rules,
          Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def] >>
  simp[exit_result_def] >> gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (fs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     rpt strip_tac >> res_tac >>
     Cases_on `b` >> fs[vyperStorageBackendTheory.get_storage_def]) >>
  `?b. lookup_var p s0 = SOME b` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  simp[target_post_def, value_type_place_def, stmt_state_rel_start_gas_obs] >>
  simp[eval_operand_def, place_ptr_rel_def, mem_path_offset_def,
       place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, wordsTheory.WORD_ADD_0]
QED

Theorem target_toplevel_memory:
  target_pre cenv cx env (TopLevelNameTarget nsid) es /\
  type_place_target env (TopLevelNameTarget nsid) = SOME vt /\
  compile_get_target_ptr compile_expr cenv (TopLevelNameTarget nsid) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (TopLevelNameTarget nsid)) target_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (eval_base_place cx (TopLevelNameTarget nsid)) (es,s0)
    (\H res ee t. ?pv. res = INL pv /\
      target_post H ctx func cenv cx es sa sb s0 ee pv vt op t /\
      (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
        slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
        storage_read_live H tr (get_storage cx ee tr) slot tv) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  rw[target_pre_def] >>
  PairCases_on `nsid` >> rename1 `TopLevelNameTarget (src,id)` >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts <> NONE` by
    (fs[immutable_root_def, target_root_def] >> metis_tac[]) >>
  drule_all toplevel_target_decl >> strip_tac >> gvs[]
  >- suspend "storage" >>
  suspend "mapping"
QED

Resume target_toplevel_memory[storage]:
  `cenv.ce_hashmap_info (src,id) = NONE /\
   cenv.ce_module_var_type (src,id) = SOME ty` by
    metis_tac[toplevel_target_env] >>
  simp[gasOutcomeTheory.gas_outcome_def, gasSummaryTheory.gas_summary_at_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qabbrev_tac `es1 = es with storage_trace :=
                 es.storage_trace ++ [StorageRoot tr slot tv]` >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tv))`, `es1`, `OK s0`] >>
  conj_tac
  >- (`!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
            (INL (PlaceR (StoragePlace tr (n2w slot) tv)), es1 with gas_obs := gs)` by
        (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
           bind_def, ignore_bind_def, record_storage_event_def,
           lift_option_type_def, return_def, LET_THM, Abbr `es1`]) >>
      simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
           fragGasPathMemTheory.gas_path_mem_rules]) >>
  simp[exit_result_def] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    fs[Abbr `es1`, vyperStorageFootprintTheory.valid_horizon_def] >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  `storage_well_formed_on cx (es1 with gas_obs := []) (FST H)` by
    (fs[Abbr `es1`, vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     rpt strip_tac >> res_tac >>
     Cases_on `b` >> fs[vyperStorageBackendTheory.get_storage_def]) >>
  `MEM (tr,n2w slot,tv) (FST H)` by
    fs[Abbr `es1`, valid_horizon_def, storage_observations_ok_def,
       storage_trace_regions_def] >>
  `slots_in_range (get_storage cx (es1 with gas_obs := []) tr)
     (w2n (n2w slot:bytes32)) tv` by
    metis_tac[storage_well_formed_on_def] >>
  `storage_read_live H tr (get_storage cx (es1 with gas_obs := []) tr)
     (n2w slot) tv` by metis_tac[observed_storage_region_read_live] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qspecl_then [`cenv`, `cx`, `src`, `id`, `ts`, `StorageVarDecl tr ty`,
               `id_str`, `tr`, `slot`] mp_tac toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[target_post_def, stmt_state_rel_start_gas_obs, Abbr `es1`] >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Resume target_toplevel_memory[mapping]:
  `?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt')` by
    metis_tac[toplevel_target_env] >>
  simp[gasOutcomeTheory.gas_outcome_def, gasSummaryTheory.gas_summary_at_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL (HashMapRef tr (n2w slot) kt vt')`, `es`, `OK s0`] >>
  conj_tac
  >- (`!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
            (INL (HashMapRef tr (n2w slot) kt vt'), es with gas_obs := gs)` by
        (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
           bind_def, lift_option_type_def, return_def, LET_THM]) >>
      simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
           fragGasPathMemTheory.gas_path_mem_rules]) >>
  simp[exit_result_def] >> gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (fs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     rpt strip_tac >> res_tac >>
     Cases_on `b` >> fs[vyperStorageBackendTheory.get_storage_def]) >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qspecl_then [`cenv`, `cx`, `src`, `id`, `ts`, `HashMapVarDecl tr kt vt'`,
               `id_str`, `tr`, `slot`] mp_tac toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[target_post_def, stmt_state_rel_start_gas_obs] >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Finalise target_toplevel_memory
