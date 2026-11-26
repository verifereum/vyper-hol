(* Dispatch the write on the endpoints of the two reached Assign stages. *)
Theory bodyQualifiedPlaceAssignFullMods
Ancestors
  bodyAssignQualifiedStageJoinMods bodyAssignPlaceRhsDispatchMods bodyAssignLocalPlaceRoutesMods
  bodyQualifiedPlaceTargetEntryMods bodyPlaceWriteTailAdmissibleMods
  bodyQualifiedAssignRawCutMods bodyQualifiedAssignSnapshotCutMods
  bodyQualifiedAssignSlotEmptyLandingMods bodyQualifiedAssignImmEmptyLandingMods
  bodyQualifiedAssignSlotWordLandingMods bodyQualifiedAssignSlotCopyLandingMods
  bodyQualifiedAssignImmWordLandingMods bodyQualifiedAssignImmCopyLandingMods
  bodyWriteOperandMods bodyPlaceWriteSourceMods bodyFullPredsMods bodyFullPostsMods
  vyperTypeContract[qualified,ignore_grammar] vyperTypeCallGraph vyperStorageFootprint
  bodyAnnNonwordReadTypesMods bodyCopyReadPhysicalTypeMods bodyFullShared loweringPosts list
  exprBodyPreProps vyperTypeEvalCaseProofs vyperTypeSystem vyperTypeArgFits
  placeRelayoutSemantic typedMemoryCopy vyperState bodyQualifiedAssignOperandCutMods
Libs monadsyntax horizonTypeLib[qualified]

(* Both copy landings use the layout of the successfully read RHS. *)
Theorem qualified_assign_copy_types[local]:
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_widens_to env.type_defs (expr_type e) dty /\
  expr_body_pre_mods mods cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  ~is_word_type dty ==>
  ~is_word_type (expr_type e) /\ assignable_type (get_tenv cx) dty /\
  assignable_type (get_tenv cx) (lowered_value_type cenv e) /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `assignable_type (get_tenv cx) (expr_type e)` by
    fs[Once type_stmt_def, AllCaseEqs()] >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by fs[] >>
  drule_all_then assume_tac type_widens_to_assignable_type >>
  `~is_word_type (expr_type e)` by metis_tac[return_source_word_widens_eq] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) ann_copy_nonword_layout_mods >>
  drule_all_then (strip_assume_tac o cj 3) copy_read_physical_type_gas_obs_mods >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  `well_formed_type (get_tenv cx) (lowered_value_type cenv e)` by
    simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  qpat_assum `type_widens_to _ (lowered_value_type _ _) dty` mp_tac >>
  pure_rewrite_tac[type_widens_to_def] >>
  disch_then (DISJ_CASES_THEN2 SUBST1_TAC strip_assume_tac)
  >- simp[] >>
  irule (cj 1 arg_type_fits_source_assignable) >>
  conj_tac >- (qexists `dty` >> simp[]) >> first_assum ACCEPT_TAC
QED

Theorem qualified_place_assign_full_mods:
  !mods exps cx bt e key.
    target_root bt = TopLevelNameTarget key /\
    EVERY (struct_args_unique o SND) mods /\
    vyperTypeContract$exports_ok cx.layouts cx.txn.target mods exps /\
    IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target mods) /\
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions mods exps))
      (int_calls_stmt (Assign (BaseTarget bt) e)) /\
    (!ctx cenv src tops env es bindings s ret_ty env'.
       contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
       expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
       supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
       EVERY (source_body_call_supported cx) (int_calls_stmt s)) /\
    body_expr_full_ok_mods mods exps cx e /\
    (!s pv se sr v sf. eval_expr cx e s = (INL pv,se) /\
       read_result cx pv sr = (INL v,sf) ==> body_base_target_full_ok_mods mods exps cx bt) ==>
    body_stmt_full_ok_mods mods exps cx (Assign (BaseTarget bt) e)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rw[body_stmt_full_ok_mods_def] >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (Assign (BaseTarget bt) e))` by
    (first_x_assum irule >> rpt (first_assum (irule_at Any))) >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (irule assign_rhs_body_pre_linked >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  rw[stmt_frag_full_mods_def] >>
  drule_all_then (CONJUNCTS_THEN2 SUBST_ALL_TAC (K ALL_TAC)) assign_place_paired_code_mods >>
  pure_rewrite_tac[GSYM assign_qualified_exit_mods_def, ETA_AX] >>
  irule (DISCH_ALL (CONJUNCT2 (UNDISCH assign_qualified_staged_routes_floor_mods))) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  qpat_assum `stmt_env _ _ _ (Assign _ _) _ = _` (irule_at Any) >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` (irule_at Any) >>
  qpat_assum `target_root bt = TopLevelNameTarget key` (irule_at Any) >>
  qhdtm_assum `return_buf_frame` (irule_at Any) >>
  qpat_assum `body_expr_full_ok_mods mods exps cx e` (irule_at Any) >>
  qexists `shadow_func` >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists `qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
     es sa shadow_sa sr shadow_sr saved s0 G0 tn0` >> BETA_TAC >>
  conj_tac
  >- (disch_tac >> irule (REWRITE_RULE [GSYM AND_IMP_INTRO] assign_place_rhs_dispatch_mods) >>
      qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
      qhdtm_assum `contract_inv` (irule_at Any) >>
      qhdtm_assum `module_body_inv` (irule_at Any) >>
      qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule qualified_place_target_entry_mods >>
      qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
      qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
      qpat_assum `supported_stmt _ _ (Assign _ _)` (irule_at Any) >>
      qpat_assum `target_root bt = TopLevelNameTarget key` (irule_at Any) >>
      qhdtm_assum `module_body_inv` (irule_at Any) >>
      qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
      qhdtm_assum `contract_inv` (irule_at Any) >>
      rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  suspend "reached_write"
QED

Resume qualified_place_assign_full_mods[reached_write]:
  qx_genl_tac [`route`,`ms`,`v`,`mid`,`Gu`,`tu`,`u`,`marks`,`p`,`ee`,`Gz`,`tz`,`z`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  PairCases_on `key` >> rename1 `target_root bt = TopLevelNameTarget (owner,id)` >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_place_code_intervals_mods >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
          expr_body_pre_mods mods cenv cx env i se` by
    (match_mp_tac (GEN_ALL place_write_index_pre_mods) >>
     qpat_assum `supported_stmt _ _ (Assign _ _)` (irule_at Any) >>
     qhdtm_assum `contract_inv` (irule_at Any) >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qhdtm_assum `qualified_assign_rhs_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  drule_all_then assume_tac assign_reached_write_admissible_mods >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_place_store_frame_mods >>
  `return_buf_sep d cenv ee z` by
    (irule (horizonTypeLib.at_horizon_named "H" return_buf_sep_locals_kept) >>
     qhdtm_assum `return_buf_sep` (irule_at Any) >>
     qexistsl [`sa`,`func`,`cx`,`ctx`,`storage_trace_horizon ee.storage_trace`] >>
     fs[wb_frame_def]) >>
  Cases_on `saved`
  >- suspend "empty" >>
  rename1 `qualified_assign_route_mods route (owner,id) p (SOME vv) dty dst` >>
  suspend "prepare"
QED

Resume qualified_place_assign_full_mods[empty]:
  Cases_on `route` >>
  TRY (qpat_x_assum `qualified_assign_route_mods _ _ _ _ _ _` mp_tac >>
       simp[qualified_assign_route_mods_def] >> NO_TAC)
  >- (irule qualified_assign_slot_empty_landing_mods >>
      qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
      qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
      qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
      qhdtm_assum `qualified_assign_route_mods` (irule_at Any) >>
      rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  irule qualified_assign_imm_empty_landing_mods >>
  qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_route_mods` (irule_at Any) >>
  qhdtm_assum `module_body_inv` (irule_at Any) >>
  qhdtm_assum `contract_inv` (irule_at Any) >>
  qpat_assum `gas_admissible (eval_stmt _ _) _ _` (irule_at Any) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Resume qualified_place_assign_full_mods[prepare]:
  `EVERY (source_body_call_supported cx) (int_calls_target bt)` by
    fs[int_calls_stmt_def, int_calls_atarget_def, EVERY_APPEND] >>
  `EVERY (\k. MEM k (vyperTypeContract$linked_live_functions mods exps))
     (int_calls_target bt)` by fs[int_calls_stmt_def, int_calls_atarget_def, EVERY_APPEND] >>
  `?op su s G tn.
     qualified_assign_operand_cut_mods (DF,lo,d,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv cx st0 (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb)
       (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) /\
     (qualified_assign_route_mods AssignImmCopy (owner,id) p (SOME vv) dty dst ==>
       !sw. eval_operand op s = SOME sw ==> lo <= w2n sw)` by
    (Cases_on `expr_can_mutate cenv (target_to_expr bt)`
     >- (irule qualified_assign_snapshot_cut_mods >>
         qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
         qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
         qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
         rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
     `?op su s G tn. unwrap_value cenv vv st = (op,su) /\
        qualified_assign_operand_cut_mods (DF,lo,d,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          cenv cx st0 (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb)
          (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) /\
        (qualified_assign_route_mods AssignImmCopy (owner,id) p (SOME vv) dty dst ==>
          !sw. eval_operand op s = SOME sw ==> lo <= w2n sw)` by
       (irule qualified_assign_raw_cut_mods >>
        qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
        qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
        qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
        qhdtm_assum `contract_inv` (irule_at Any) >>
        qhdtm_assum `module_body_inv` (irule_at Any) >>
        qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
        rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
     qexistsl [`op`,`su`,`s`,`G`,`tn`] >> rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  rename1 `qualified_assign_operand_cut_mods _ _ _ _ _ (_,op,_,_,_) (_,_,su,_) _ _ (s,G,tn)` >>
  qhdtm_assum `qualified_assign_code_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  Cases_on `route` >>
  TRY (qpat_x_assum `qualified_assign_route_mods _ _ _ (SOME _) _ _` mp_tac >>
       simp[qualified_assign_route_mods_def] >> NO_TAC)
  >- suspend "slot_word"
  >- suspend "slot_copy"
  >- suspend "imm_word"
  >> suspend "imm_copy"
QED

Resume qualified_place_assign_full_mods[slot_word]:
  irule qualified_assign_slot_word_landing_mods >>
  qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_operand_cut_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_route_mods` (irule_at Any) >>
  qhdtm_assum `type_widens_to` (irule_at Any) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Resume qualified_place_assign_full_mods[imm_word]:
  irule qualified_assign_imm_word_landing_mods >>
  qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_operand_cut_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_code_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_route_mods` (irule_at Any) >>
  qhdtm_assum `contract_inv` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods mods cenv cx env ee` (irule_at Any) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Resume qualified_place_assign_full_mods[slot_copy]:
  `?tr sl tv. p = StoragePlace tr sl tv /\
      dst = (FST dst,SOME (slot_loc tr),SOME (ValPT dty)) /\ ~is_word_type dty` by
    (qpat_x_assum `qualified_assign_route_mods AssignSlotCopy _ _ _ _ _` mp_tac >>
     Cases_on `p` >> simp[NoAsms,qualified_assign_route_mods_def] >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `p = StoragePlace _ _ _` SUBST_ALL_TAC >>
  qpat_assum `dst = (FST dst,_,_)`
    (fn eq => rule_assum_tac (ONCE_REWRITE_RULE [eq])) >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE[APPEND_NIL,evaluation_state_component_equality])) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_assign_copy_types >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
    qpat_assum `!tail. eval_target_place _ _ _ = _`
      (qspec_then `[]` (assume_tac o PURE_REWRITE_RULE [APPEND_NIL,eq]))) >>
  irule qualified_assign_slot_copy_landing_mods >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
  >- (qexistsl [`env`,`exps`,`mods`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qhdtm_assum `qualified_assign_operand_cut_mods` (irule_at Any) >>
  qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
  qpat_assum `assign_place_rhs_code_mods cenv _ _ _ = _` (irule_at Any) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Resume qualified_place_assign_full_mods[imm_copy]:
  `!sw. eval_operand op s = SOME sw ==> lo <= w2n sw` by
    (qpat_assum `qualified_assign_route_mods AssignImmCopy _ _ _ _ _ ==> _`
       (drule_then ACCEPT_TAC)) >>
  `~is_word_type dty` by fs[qualified_assign_route_mods_def] >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE[APPEND_NIL,evaluation_state_component_equality])) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_assign_copy_types >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >> drule_all_then (assume_tac o cj 2) qualified_place_store_frame_mods >> simp[]) >>
  irule qualified_assign_imm_copy_landing_mods >>
  qhdtm_assum `qualified_assign_operand_cut_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_route_mods` (irule_at Any) >>
  qhdtm_assum `contract_inv` (irule_at Any) >>
  qhdtm_assum `module_body_inv` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods mods cenv cx env ee` (irule_at Any) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Finalise qualified_place_assign_full_mods
