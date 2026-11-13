(* Counted root target evaluation: roots emit no instructions. *)
Theory popNestedTargetRootsMemory
Ancestors
  popNestedTargetReadinessMemory
  targetPlaceSimMem targetPlaceSim stmtSimAugAssign fragGasPathMem
  exprLoweringProps fragExec vyperAST
  exprSimHypsDefs exprLowering emitHelper stmtSimProps exprSimDefs
  loweringPosts loweringStateRelDefs compileEnv gasOutcome gasSummary fragGasMode
  vyperTypeSystem vyperInterpreter vyperState venomState

Theorem pop_nested_target_name_mem:
  target_pre cenv cx env (NameTarget id) es ==>
  target_sim_mem ctx func cenv cx env (NameTarget id) es
Proof
  rw[target_sim_mem_def] >>
  irule pop_nested_target_outcome_ready_mem >>
  conj_tac >- (qexists `env` >> first_assum ACCEPT_TAC) >>
  fs[target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_def, gas_summary_at_def] >> qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules,
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

Theorem pop_nested_target_toplevel_mem:
  target_pre cenv cx env (TopLevelNameTarget nsid) es /\
  ~immutable_root cx (TopLevelNameTarget nsid) ==>
  target_sim_mem ctx func cenv cx env (TopLevelNameTarget nsid) es
Proof
  rw[target_sim_mem_def] >>
  irule pop_nested_target_outcome_ready_mem >>
  conj_tac >- (qexists `env` >> first_assum ACCEPT_TAC) >>
  fs[target_pre_def] >>
  PairCases_on `nsid` >> rename1 `TopLevelNameTarget (src,id)` >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts <> NONE` by
    (fs[immutable_root_def, target_root_def] >> metis_tac[]) >>
  drule_all toplevel_target_decl >> strip_tac >> gvs[]
  >- suspend "storage" >>
  suspend "mapping"
QED

Resume pop_nested_target_toplevel_mem[storage]:
  `cenv.ce_hashmap_info (src,id) = NONE /\
   cenv.ce_module_var_type (src,id) = SOME ty` by
    metis_tac[toplevel_target_env] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- gvs[stmt_state_rel_def, state_rel_def] >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_decl_ce_vars >>
     goal_assum (drule_at Any) >> simp[var_decl_transient_def]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tv))`, `es`, `OK s0`] >>
  conj_tac
  >- (`!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
            (INL (PlaceR (StoragePlace tr (n2w slot) tv)), es with gas_obs := gs)` by
        (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
           bind_def, lift_option_type_def, return_def, LET_THM]) >>
      simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules]) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exit_result_def, target_post_def] >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Resume pop_nested_target_toplevel_mem[mapping]:
  `?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt')` by
    metis_tac[toplevel_target_env] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- gvs[stmt_state_rel_def, state_rel_def] >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_decl_ce_vars >>
     goal_assum (drule_at Any) >> simp[var_decl_transient_def]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (HashMapRef tr (n2w slot) kt vt')`, `es`, `OK s0`] >>
  conj_tac
  >- (`!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
            (INL (HashMapRef tr (n2w slot) kt vt'), es with gas_obs := gs)` by
        (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
           bind_def, lift_option_type_def, return_def, LET_THM]) >>
      simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules]) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exit_result_def, target_post_def] >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Finalise pop_nested_target_toplevel_mem
