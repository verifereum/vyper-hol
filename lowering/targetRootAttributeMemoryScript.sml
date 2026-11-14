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
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_base_place cx (NameTarget id)) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
      (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
        slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
        storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  rw[target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_def, gas_summary_at_def] >> qexists `[]` >> disj1_tac >>
  qexistsl [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
          fragGasPathMemTheory.gas_path_mem_rules,
          Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def] >>
  simp[exit_result_def] >>
  `?b. lookup_var p s0 = SOME b` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  simp[target_post_def, value_type_place_def] >>
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
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_base_place cx (TopLevelNameTarget nsid)) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
      (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
        slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
        storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
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
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- gvs[stmt_state_rel_def, state_rel_def] >>
  fs[] >>
  drule_at (Pat `find_var_decl_by_name _ _ = _`) toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> disch_then drule_all >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists `[]` >> disj1_tac >>
  qexistsl [`INL (PlaceR (StoragePlace tr (n2w slot) tv))`, `es`, `OK s0`] >>
  conj_tac
  >- (`!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
            (INL (PlaceR (StoragePlace tr (n2w slot) tv)), es with gas_obs := gs)` by
        (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
           bind_def, lift_option_type_def, return_def, LET_THM]) >>
      simp[gas_marked_exec_def, gas_marked_path_def,
           fragGasPathMemTheory.gas_path_mem_rules]) >>
  `lookup_global cx src id (es with gas_obs := []) =
     (INL (PlaceR (StoragePlace tr (n2w slot) tv)), es with gas_obs := [])` by
    simp[lookup_global_def, bind_def, lift_option_type_def, return_def, LET_THM] >>
  `contract_storage_well_formed cx (es with gas_obs := [])` by
    (irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_storage_frame >>
     qexists `es` >> conj_tac
     >- (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     fs[expr_sim_inv_def]) >>
  drule_all nested_pop_lookup_global_slots >>
  drule targetPlaceLiveTheory.nested_pop_lookup_global_live >>
  simp[nested_pop_result_slots_def, targetPlaceLiveTheory.nested_pop_result_live_def,
       vyperStorageBackendTheory.get_storage_backend_eq] >>
  rpt strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exit_result_def, target_post_def] >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Resume target_toplevel_memory[mapping]:
  `?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt')` by
    metis_tac[toplevel_target_env] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- gvs[stmt_state_rel_def, state_rel_def] >>
  fs[] >>
  drule_at (Pat `find_var_decl_by_name _ _ = _`) toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> disch_then drule_all >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists `[]` >> disj1_tac >>
  qexistsl [`INL (HashMapRef tr (n2w slot) kt vt')`, `es`, `OK s0`] >>
  conj_tac
  >- (`!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
            (INL (HashMapRef tr (n2w slot) kt vt'), es with gas_obs := gs)` by
        (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
           bind_def, lift_option_type_def, return_def, LET_THM]) >>
      simp[gas_marked_exec_def, gas_marked_path_def,
           fragGasPathMemTheory.gas_path_mem_rules]) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exit_result_def, target_post_def] >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Finalise target_toplevel_memory
