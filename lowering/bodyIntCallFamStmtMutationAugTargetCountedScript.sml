(* Counted target evaluation, by the base-target induction interface. *)
Theory bodyIntCallFamStmtMutationAugTargetCounted
Ancestors
  bodyIntCallFamStmtMutationAugArrayConstructor
  bodyIntCallFamStmtMutationAugTargetMapConstructor
  bodyIntCallFamStmtMutationAugTargetAttrCounted
  bodyIntCallFamStmtMutationBinop
  targetPlaceSim targetPlaceSimDefs targetPlaceSimCasesBase
  bodyIntCallJointContract bodyIntCallJointAggCore
  supportedTargets vyperTypeSystem exprLowering compileEnv
  gasOutcome gasSummary fragGasMode fragGasPath vyperInterpreter vyperState
  exprSimHypsDefs loweringStateRelDefs stmtSimAugAssign
  loweringPosts exprSimDefs venomState valueEncoding fragExec bodySim exprLoweringProps
  vyperPlaceResultTyping vyperTypeEnv vyperTypeInvariants

Theorem intcall_target_counted:
  !tg ce env es sa sb s vt op bindings.
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\ intcall_frame_ok fp /\
    body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    IS_SOME (supported_target_info fp.jc_tops bindings tg) /\
    target_pre ce fp.jc_cx env tg es /\ type_place_target env tg = SOME vt /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_target tg) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) tg ==>
       occurs_abi_decode_target target fp.jc_tops) /\
    compile_get_target_ptr compile_expr ce tg sa = (op,sb) /\
    fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    gas_admissible (eval_base_place fp.jc_cx tg) target_res_ok es /\
    intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
      (eval_base_place fp.jc_cx tg) (es,s)
      (\res ee u. ?pv. res = INL pv /\
        target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee pv vt op u /\
        intcall_expr_cont fp ce env es sa s ee sb u)
      (\res ee r. expr_exit res r)
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- suspend "name"
  >- suspend "toplevel"
  >- suspend "subscript" >>
  rpt gen_tac >> strip_tac >>
  drule intcall_target_attribute_counted >>
  disch_then (qspec_then `s` mp_tac) >> simp[]
QED

Resume intcall_target_counted[name]:
  rpt gen_tac >> strip_tac >>
  fs[target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `ce.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
          Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def] >>
  simp[exit_result_def] >>
  `?b. lookup_var p s = SOME b` by
    (fs[intcall_expr_res_def, stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `not_fresh_at sa p` by
    metis_tac[intcall_expr_res_def,local_ptrs_reserved_def] >>
  simp[target_post_def, value_type_place_def] >>
  simp[eval_operand_def, place_ptr_rel_def, mem_path_offset_def,
       place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, wordsTheory.WORD_ADD_0] >>
  simp[intcall_expr_cont_def] >> fs[intcall_expr_res_def] >> metis_tac[]
QED

Resume intcall_target_counted[toplevel]:
  rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  rename1 `TopLevelNameTarget (src,id)` >>
  `expr_sim_inv ce fp.jc_cx env es` by fs[target_pre_def] >>
  `env_consistent env fp.jc_cx es` by fs[expr_sim_inv_def] >>
  `!ts. get_module_code fp.jc_cx src = SOME ts ==>
        find_var_decl_by_name id ts <> NONE` by
    (fs[target_pre_def,immutable_root_def,target_root_def] >> metis_tac[]) >>
  drule_all type_place_target_global_lookup >> strip_tac >>
  Cases_on `vt`
  >- (Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
          gvs[optionTheory.IS_SOME_EXISTS] >> suspend "top_storage") >>
      drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >> suspend "top_mapping"
QED

Resume intcall_target_counted[top_storage]:
  rename1 `find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str)` >>
  rename1 `lookup_var_slot_from_layout _ tr src id_str = SOME slot` >>
  rename1 `evaluate_type _ ty = SOME tv` >>
  `ce.ce_hashmap_info (src,id) = NONE /\
   ce.ce_module_var_type (src,id) = SOME ty` by
    (drule_all toplevel_target_env >> simp[]) >>
  `storage_vars_rel ce fp.jc_cx /\ transient_vars_rel ce fp.jc_cx` by
    fs[intcall_expr_res_def,stmt_state_rel_def,state_rel_def] >>
  `FLOOKUP ce.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (Cases_on `tr` >>
     gvs[storage_vars_rel_def,transient_vars_rel_def] >>
     first_x_assum irule >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[var_decl_transient_def]) >>
  `op = (Lit (n2w slot),SOME (if tr then LocTransient else LocStorage),
         SOME (ValPT ty)) /\ sb = sa` by
    (qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
     Cases_on `tr` >> simp[compile_get_target_ptr_def,comp_return_def,LET_THM]) >>
  gvs[] >>
  simp[gas_outcome_def,gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tv))`, `es`, `OK s`] >>
  conj_tac
  >- (`!gs. eval_base_place fp.jc_cx (TopLevelNameTarget (src,id))
          (es with gas_obs := gs) =
          (INL (PlaceR (StoragePlace tr (n2w slot) tv)),es with gas_obs := gs)` by
        simp[Once evaluate_def,lookup_global_def,bind_def,lift_option_type_def,
             return_def,LET_THM] >>
      simp[gas_marked_exec_def,gas_marked_path_def,gas_path_rules]) >>
  simp[exit_result_def,target_post_def] >>
  simp[eval_operand_def,place_ptr_rel_def,slot_loc_def,value_type_place_def,
       place_readable_def] >>
  simp[intcall_expr_cont_def] >> fs[intcall_expr_res_def] >> metis_tac[]
QED

Resume intcall_target_counted[top_mapping]:
  rename1 `find_var_decl_by_name id ts = SOME (HashMapVarDecl tr kt vty,id_str)` >>
  rename1 `lookup_var_slot_from_layout _ tr src id_str = SOME slot` >>
  `?tr'. ce.ce_hashmap_info (src,id) = SOME (tr',kt,vty)` by
    (drule_all toplevel_target_env >> simp[]) >>
  `storage_vars_rel ce fp.jc_cx /\ transient_vars_rel ce fp.jc_cx` by
    fs[intcall_expr_res_def,stmt_state_rel_def,state_rel_def] >>
  `FLOOKUP ce.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (Cases_on `tr` >>
     gvs[storage_vars_rel_def,transient_vars_rel_def] >>
     first_x_assum irule >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[var_decl_transient_def]) >>
  `op = (Lit (n2w slot),SOME (if tr then LocTransient else LocStorage),
         SOME (MapPT kt vty)) /\ sb = sa` by
    (qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
     Cases_on `tr` >> simp[compile_get_target_ptr_def,comp_return_def,LET_THM]) >>
  gvs[] >>
  simp[gas_outcome_def,gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (HashMapRef tr (n2w slot) kt vty)`, `es`, `OK s`] >>
  conj_tac
  >- (`!gs. eval_base_place fp.jc_cx (TopLevelNameTarget (src,id))
          (es with gas_obs := gs) =
          (INL (HashMapRef tr (n2w slot) kt vty),es with gas_obs := gs)` by
        simp[Once evaluate_def,lookup_global_def,bind_def,lift_option_type_def,
             return_def,LET_THM] >>
      simp[gas_marked_exec_def,gas_marked_path_def,gas_path_rules]) >>
  simp[exit_result_def,target_post_def] >>
  simp[eval_operand_def,place_ptr_rel_def,slot_loc_def,value_type_place_def,
       place_readable_def] >>
  simp[intcall_expr_cont_def] >> fs[intcall_expr_res_def] >> metis_tac[]
QED

Resume intcall_target_counted[subscript]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `(?ety bd. type_place_target env bt = SOME (Type (ArrayT ety bd))) \/
   (?kt vty. type_place_target env bt = SOME (HashMapT kt vty))` by
    (qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
     simp[Once well_typed_expr_def, AllCaseEqs()] >> rpt strip_tac >>
     rename1 `subscript_vtype bty _ = _` >>
     Cases_on `bty` >> gvs[subscript_vtype_def] >>
     rename1 `subscript_vtype (Type aty) _ = _` >>
     Cases_on `aty` >> gvs[subscript_vtype_def, AllCaseEqs()])
  >- (drule intcall_target_array_counted >>
      disch_then (qspec_then `e` mp_tac) >>
      disch_then drule_all >> simp[]) >>
  drule intcall_target_mapping_counted >>
  disch_then (qspec_then `e` mp_tac) >>
  disch_then drule_all >> simp[]
QED

Finalise intcall_target_counted
