(* Transport a saved slot using agreement at the suffix exit. *)
Theory bodyExtSavedSlotEndpointMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv loweringPosts bodyPtrDefs
  venomState vyperInterpreter vyperStorageBackend stmtSimAssignStorageCopy
  accountsRelProps exprPtrUnwrapStorageFacts exprSimProps exprSimMemDefs
  vfmState sourceUnitExecution vyperState loweringStateRelDefs ptrDiscipline

Theorem saved_slot_range_frame[local]:
  storage_range_agree st rt w tv /\ storage_read_live H tr st w tv /\
  storage_agree (storage_dead H tr st) st rt' ==>
  storage_range_agree st rt' w tv
Proof
  strip_tac >> irule storage_range_agree_of_live >>
  conj_tac >- fs[storage_range_agree_def] >>
  qexistsl_tac [`H`,`tr`] >> simp[]
QED

Theorem saved_slot_taint_dead_mods[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn u /\ dead_lo_ok_mods H D lo cenv cx /\
  (k,b) IN (if tr then tn.t_trans else tn.t_stor) ==>
  storage_dead H tr (if tr then contract_transient u else contract_storage u)
    (w2n k) b
Proof
  Cases_on `tr` >>
  gvs[ghost_inv_at_mods_def, stor_taint_ok_at_def, dead_lo_ok_mods_def,
      cx_dead_def, pred_setTheory.SUBSET_DEF, contract_storage_def,
      contract_transient_def, vfmStateTheory.lookup_account_def] >>
  rpt strip_tac >> first_x_assum drule >>
  Cases_on `u.vs_call_ctx.cc_address = cx.txn.target` >> simp[]
QED

Theorem saved_slot_read_dead[local]:
  storage_agree (storage_dead H tr st) st rt /\
  storage_range_agree st rt w tv /\ storage_read_live H tr st w tv /\
  storage_dead H tr rt (w2n k) b /\
  w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv ==>
  dead_bytes rt (w2n w) tv (w2n k) b
Proof
  strip_tac >> drule storage_agree_storage_dead >> strip_tac >>
  drule storage_range_agree_dead_bytes >> strip_tac >>
  fs[storage_read_live_def] >> metis_tac[]
QED

Theorem ext_saved_slot_endpoint_mods:
  p.ptr_location = slot_loc tr /\
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds_mods cenv cx ty raw (LocatedValue ty p) mid t /\
    ptr_vv_ok cx ty raw (LocatedValue ty p) mid G1 tn1 t) /\
  vv_storage_live H cx (LocatedValue ty p) mid t /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  u.vs_labels = t.vs_labels /\ get_storage cx ee tr = get_storage cx mid tr /\
  stmt_state_rel H ctx func cenv cx ee u /\
  ghost_inv_at_mods D lo d cenv cx ee G2 tn2 u /\ dead_lo_ok_mods H D lo cenv cx ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods cenv cx ty raw (LocatedValue ty p) ee u /\
    vv_at cenv cx ty sa sb ee raw (LocatedValue ty p) u /\
    ptr_vv_ok cx ty raw (LocatedValue ty p) ee G2 tn2 u /\
    vv_store_bound cx ann ty ee raw (LocatedValue ty p) u) /\
  vv_storage_live H cx (LocatedValue ty p) ee u
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand t = SOME w /\ storage_holds cx tr ty raw w mid t` by
    (Cases_on `tr` >> gvs[vv_holds_mods_def, vv_holds_def, slot_loc_def]) >>
  `eval_operand p.ptr_operand u = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `op_taint tn2 p.ptr_operand = {}` by
    (gvs[ghost_kept_at_def, ptr_vv_ok_def] >> Cases_on `p.ptr_operand` >>
     gvs[op_taint_def] >> metis_tac[]) >>
  `!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     storage_read_live H tr (get_storage cx ee tr) w tv` by
    (Cases_on `tr` >> gvs[vv_storage_live_def, slot_loc_def]) >>
  `storage_agree (storage_dead H tr (get_storage cx ee tr)) (get_storage cx ee tr)
     (if tr then contract_transient u else contract_storage u)` by
    (irule storage_copy_initial_agree >> metis_tac[]) >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
    read_storage_slot cx tr w tv ee = (INL v,ee) /\
    slots_in_range (get_storage cx ee tr) (w2n w) tv /\
    storage_range_agree (get_storage cx ee tr)
      (if tr then contract_transient u else contract_storage u) w tv` by
    (gvs[storage_holds_def] >>
     conj_tac >- gvs[read_storage_slot_eq, AllCaseEqs()] >>
     irule saved_slot_range_frame >> metis_tac[]) >>
  reverse conj_tac >- (Cases_on `tr` >> gvs[slot_loc_def]) >>
  qexists_tac `Value v` >>
  `storage_holds cx tr ty (Value v) w ee u` by
    (simp[storage_holds_def, read_result_def, return_def] >> metis_tac[]) >>
  `!k b. w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv /\
     (k,b) IN (if tr then tn2.t_trans else tn2.t_stor) ==>
     dead_bytes (if tr then contract_transient u else contract_storage u)
       (w2n w) tv (w2n k) b` by
    (rpt strip_tac >>
     drule_all saved_slot_taint_dead_mods >> strip_tac >>
     irule saved_slot_read_dead >> simp[] >>
     qexistsl_tac [`H`,`get_storage cx ee tr`,`tr`] >> simp[]) >>
  Cases_on `tr` >>
  gvs[slot_loc_def, vv_holds_mods_def, vv_holds_def, vv_at_def, vv_store_bound_def,
      ptr_vv_ok_def, read_result_def, return_def, contract_storage_def,
      contract_transient_def, vfmStateTheory.lookup_account_def]
QED
