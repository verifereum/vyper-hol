Theory bodyPtrPopTargetSimRoots
Ancestors
  bodyPtrPopTargetSimBoundary stmtSimAugAssign
  bodyPtrBopInNameBoundary fragGasPathPtr targetPlaceSim
  exprLoweringProps compileEnv loweringPosts vyperInterpreter vyperState
  ptrDiscipline bodyPtrPopTargetDefs bodyPtrDefs vyperTypeSystem
  exprLowering venomState fragExec stmtFragPtr exprSimSubscriptMap
  exprSimTopLevelProps vyperTypeEnv vyperTyping exprSimHypsDefs
  vyperPlaceResultTyping vyperTypeInvariants

Theorem target_name_sim_ptr:
  target_pre cenv cx env (NameTarget id) es ==>
  target_sim_ptr d ctx PG func cenv cx env (NameTarget id) es
Proof
  rw[target_sim_ptr_def, target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  `?b. lookup_var p s0 = SOME b` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `G0`, `tn0`, `OK s0`] >>
  conj_tac
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def] >>
  conj_tac >- simp[gas_path_ptr_rules] >>
  simp[exit_result_def, ghost_kept_refl] >>
  conj_tac
  >- (simp[target_post_def, value_type_place_def, eval_operand_def,
           place_ptr_rel_def, mem_path_offset_def, place_readable_def,
           read_place_def, bind_def, get_scopes_def, lift_option_type_def,
           return_def, lift_sum_def, read_memory_path_def,
           evaluate_subscripts_def, wordsTheory.WORD_ADD_0]) >>
  conj_tac
  >- simp[ghost_inv_gas_obs] >>
  simp[target_ptr_ok_def, op_prov_def] >>
  gvs[ghost_inv_def, ptr_covers_def] >> metis_tac[]
QED

Theorem target_toplevel_sim_ptr:
  target_pre cenv cx env (TopLevelNameTarget (src,id)) es ==>
  target_sim_ptr d ctx PG func cenv cx env (TopLevelNameTarget (src,id)) es
Proof
  rw[target_sim_ptr_def, target_pre_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts <> NONE` by
    (fs[immutable_root_def, target_root_def] >> metis_tac[]) >>
  `?ts tr id_str slot.
    get_module_code cx src = SOME ts /\
    ((?ty tv. vt = Type ty /\
       find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
       evaluate_type (get_tenv cx) ty = SOME tv /\
       lookup_var_slot_from_layout cx tr src id_str = SOME slot) \/
     (?kt vt'. vt = HashMapT kt vt' /\
       find_var_decl_by_name id ts = SOME (HashMapVarDecl tr kt vt',id_str) /\
       lookup_var_slot_from_layout cx tr src id_str = SOME slot))` by
    (drule_all type_place_target_global_lookup >> strip_tac >>
     Cases_on `vt`
     >- (Cases_on `FLOOKUP env.bare_globals (src,id)`
         >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
             gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
         drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[]) >>
     drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
     gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  gvs[] >- suspend "storage" >> suspend "mapping"
QED

Resume target_toplevel_sim_ptr[storage]:
  `cenv.ce_hashmap_info (src,id) = NONE /\
   cenv.ce_module_var_type (src,id) = SOME ty` by
    metis_tac[toplevel_target_env] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  `!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
     (INL (PlaceR (StoragePlace tr (n2w slot) tv)),es with gas_obs := gs)` by
    (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
       bind_def, lift_option_type_def, return_def, LET_THM]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tv))`, `es`,
                `G0`, `tn0`, `OK s0`] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[gas_path_ptr_rules, exit_result_def, target_post_def, eval_operand_def,
       place_ptr_rel_def, slot_loc_def, value_type_place_def, place_readable_def,
       ghost_inv_gas_obs, ghost_kept_refl, target_ptr_ok_def,
       op_taint_def, op_prov_def]
QED

Resume target_toplevel_sim_ptr[mapping]:
  `?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt')` by
    metis_tac[toplevel_target_env] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (drule (Q.INST [`d` |-> `HashMapVarDecl tr kt vt'`]
       toplevel_storage_ce_vars_decl) >>
     simp[var_decl_transient_def] >> metis_tac[]) >>
  `!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
     (INL (HashMapRef tr (n2w slot) kt vt'),es with gas_obs := gs)` by
    (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
       bind_def, lift_option_type_def, return_def, LET_THM]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (HashMapRef tr (n2w slot) kt vt')`, `es`,
                `G0`, `tn0`, `OK s0`] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[gas_path_ptr_rules, exit_result_def, target_post_def, eval_operand_def,
       place_ptr_rel_def, slot_loc_def, value_type_place_def, place_readable_def,
       ghost_inv_gas_obs, ghost_kept_refl, target_ptr_ok_def,
       op_taint_def, op_prov_def]
QED

Finalise target_toplevel_sim_ptr
