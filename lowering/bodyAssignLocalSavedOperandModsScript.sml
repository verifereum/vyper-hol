Theory bodyAssignLocalSavedOperandMods
Ancestors
  bodyQualifiedPlaceRawUnwrapMods bodyAssignLocalRawOperandAtStoreMods
  bodySavedTargetSourceMods bodySavedTargetVvPostMods bodyFullPredsMods
  bodyAssignQualifiedStageJoinMods bodyWriteTargetStageMods
  bodyAssignLocalPreStoreMods bodyAssignLocalPlaceRoutesMods
  bodyCallSupport vyperTypeContract bodyQualifiedPlaceRhsPostMods
  bodyPlaceWriteSourceMods bodyPtrPopTargetFragTransport targetPureWalkScopes
  stmtLoweringMono compileEnv context exprLowering bodySavedRhsSlotLiveMods
  bodyFullPostsMods vyperStorageFootprint exprLoweringProps exprBodyPreProps
  exprSimHypsDefs exprReasonOperand vyperStorageTrace vyperEvalExprPreservesScopesDom
  exprSimWordArgs
  vyperState vyperInterpreter
  loweringPosts finite_map list

val here = ``local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
  (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw) ee``;
val rhs = ``qualified_assign_rhs_reached_mods cx st0 e es s0
  (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
     es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0) ms v mid Gu tu u``;
val reached = ``qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
  mid sr st dst u Gu tu marks (MemoryPlace id path) ee Gz tz z``;
val store_guard = ``contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
          expr_body_pre_mods mods cenv cx env i se) /\
  exports_ok cx.layouts cx.txn.target mods exps``;
val store_entry = ``body_const_cells_agree_mods mods cx env es /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H)) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb (SOME vv)
    sr st shadow_sr shadow_st dst /\ ^rhs /\ ^reached /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  ^here st z Gz tz /\ write_place cx (MemoryPlace id path) v ee = (INL (),ff)``;
val reached_saved_packet = ``ee.scopes = mid.scopes /\
  !gs raw H. eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
    read_result cx raw mid = (INL v,mid) /\
    valid_horizon cx st0 H ee.storage_trace /\
    valid_horizon cx st0 H mid.storage_trace /\
    vv_post_mods H ctx func cenv cx e es sa sr s0 mid raw vv u /\
    vv_storage_live H cx vv mid u ==> read_result cx raw ee = (INL v,ee) /\
    vv_post_mods H ctx func cenv cx e ee sa sr z ee raw vv z /\
    vv_storage_live H cx vv ee z``;

Theorem rhs_components[local]:
  ^rhs /\ ~expr_can_mutate cenv (target_to_expr bt) /\
  valid_horizon cx st0 H mid.storage_trace ==>
  compile_expr cenv (expr_type e) e sa = (vv,sr) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sr x) /\
  ?gs raw. eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
    read_result cx raw mid = (INL v,mid) /\
    vv_post_mods H ctx func cenv cx e es sa sr s0 mid raw vv u
Proof
  simp[qualified_assign_rhs_reached_mods_def] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [qualified_place_rhs_post_mods_def])) >>
  qpat_assum `assign_place_rhs_code_mods cenv bt e sa = _`
    (mp_then (Pos hd) strip_assume_tac qualified_assign_rhs_code_view_mods) >> gvs[] >>
  qexistsl [`gs`,`pv`] >> asm_rewrite_tac[] >>
  drule_at (Pat `eval_expr cx e (es with gas_obs := gs) = (INL pv,mid)`)
    saved_rhs_slot_live_mods >> simp[] >> disch_then irule >>
  qhdtm_assum `vv_post_mods` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem assign_local_saved_operand_reached_mods:
  ^store_guard /\ IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  ^store_entry ==> ^reached_saved_packet
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `IS_SOME (check_contract F _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qhdtm_assum `body_const_cells_agree_mods`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  `(?gs raw0. eval_expr cx e (es with gas_obs := gs) = (INL raw0,mid) /\
      read_result cx raw0 mid = (INL v,mid)) /\
   compile_expr cenv (expr_type e) e sa = (vv,sr)` by
    (qhdtm_assum `qualified_assign_rhs_reached_mods`
       (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
     `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then (strip_assume_tac o MATCH_MP qualified_place_rhs_saved_view_mods)) >>
     gvs[] >> rpt (first_assum (irule_at Any))) >>
  pop_assum strip_assume_tac >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `ee.scopes = mid.scopes` by
    (drule_all_then strip_assume_tac saved_checked_target_source_update_mods >>
     qpat_assum `ee = _` (once_rewrite_tac o single) >>
     simp[]) >>
  `!r. read_result cx r mid = (INL v,mid) ==> read_result cx r ee = (INL v,ee)` by
    (rpt strip_tac >> drule_all_then strip_assume_tac saved_checked_target_source_update_mods >>
     first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac saved_checked_target_source_update_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `vv_post_mods H ctx func cenv cx e es sa sr s0 mid raw vv u /\
   vv_storage_live H cx vv mid u` by
    (conj_tac >- first_assum ACCEPT_TAC >>
     qhdtm_assum `qualified_assign_rhs_reached_mods`
       (mp_then (Pos hd) mp_tac rhs_components) >>
     disch_then (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
     rename1 `eval_expr cx e (es with gas_obs := gs') = (INL raw',mid)` >>
     drule_at (Pat `eval_expr cx e (es with gas_obs := gs') = (INL raw',mid)`)
       saved_rhs_slot_live_mods >> simp[] >> disch_then irule >>
     qhdtm_assum `vv_post_mods` (irule_at Any) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` (drule_then assume_tac)) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  drule_then (strip_assume_tac o BETA_RULE) qualified_place_rhs_entry_view_mods >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule_all eval_expr_preserves_scopes_dom >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qspec_then `cx` (qspec_then `e` assume_tac)
       (cj 5 evaluate_storage_trace_frame) >>
     drule_all valid_horizon_frame >> simp[evaluation_state_component_equality]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `wb_frame cenv es ee sa s0 z` by
    (drule_all_then strip_assume_tac wb_frame_trans >>
     first_assum ACCEPT_TAC) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sr x` by
    (qhdtm_assum `qualified_assign_rhs_reached_mods`
       (mp_then (Pos hd) mp_tac rhs_components) >>
     disch_then (qspec_then `H` mp_tac) >> simp[] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `reason_uniform_shape compile_expr cenv (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists `env` >>
     fs[expr_sim_inv_mods_def]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
  `!l. vv_operand vv <> Label l` by
    (qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _`
       (drule_then assume_tac) >>
     Cases_on `vv` >> gvs[reason_result_shape_def, vv_operand_def]) >>
  drule_all_then strip_assume_tac saved_target_vv_post_mods >>
  simp[]
QED
