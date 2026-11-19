Theory bodyFullSubscriptMappingValue
Ancestors
  exprSimSubscriptMap exprSimMemDefs bodyPtrDefs sourceUnitExecution
  loweringPosts context vyperAST pred_set

Theorem subscript_mapping_value_place_post:
  evaluate_type (get_tenv cx) ann = SOME tv /\
  MEM (tr,slot,tv) (FST H) /\ regions_consistent (FST H) /\
  stmt_state_rel H ctx fn ce cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  eval_operand op s = SOME slot /\ op_taint tn op = {} /\
  ghost_inv_at D lo d ce cx ee G tn s /\ dead_lo_ok H D lo ce cx /\
  wb_frame ce es ee sa s0 s /\
  (~expr_has_effect obj /\ ~expr_has_effect idx ==>
    pure_frame ce fn es sa s0 s) ==>
  vv_post H ctx fn ce cx (Subscript ann obj idx) es sa sb s0 ee
    (PlaceR (StoragePlace tr slot tv)) (LocatedValue ann (mk_ptr op (slot_loc tr))) s /\
  vv_store_bound cx ann lt ee
    (PlaceR (StoragePlace tr slot tv)) (LocatedValue ann (mk_ptr op (slot_loc tr))) s /\
  ptr_vv_ok cx ann (PlaceR (StoragePlace tr slot tv))
    (LocatedValue ann (mk_ptr op (slot_loc tr))) ee G tn s
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `vv_holds ce cx ann (PlaceR (StoragePlace tr slot tv))
     (LocatedValue ann (mk_ptr op (slot_loc tr))) ee s` by
    (irule mapping_leaf_vv_holds >> simp[mk_ptr_def] >>
     qexistsl [`H`,`ctx`,`fn`] >> simp[]) >>
  `storage_read_live H tr (get_storage cx ee tr) slot tv` by
    (irule accountsRelPropsTheory.observed_storage_region_read_live >> simp[]) >>
  `stor_taint_ok_at D tn s` by fs[ghost_inv_at_def] >>
  `!st. storage_read_live H tr st slot tv` by
    (gen_tac >> irule accountsRelPropsTheory.observed_storage_region_read_live >> simp[]) >>
  qpat_x_assum `wb_frame _ _ _ _ _ _`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac o REWRITE_RULE [wb_frame_def]) >>
  conj_tac
  >- (Cases_on `tr` >>
      gvs[vv_post_def, vv_at_def, vv_place_ptr_def, slot_loc_def, mk_ptr_def,
          post_value_type_def, expr_type_def, supportedExprTraverseTheory.expr_has_effect_def] >>
      metis_tac[]) >>
  conj_tac
  >- (Cases_on `tr` >> simp[vv_store_bound_def, slot_loc_def, mk_ptr_def]) >>
  Cases_on `tr` >>
  gvs[ptr_vv_ok_def, slot_loc_def, mk_ptr_def] >>
  rpt strip_tac >>
  qpat_x_assum `!st. storage_read_live H _ st slot tv`
    (assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.storage_read_live_def]) >>
  qpat_x_assum `stor_taint_ok_at D tn s` mp_tac >>
  qpat_x_assum `dead_lo_ok H D lo ce cx` mp_tac >>
  simp[stor_taint_ok_at_def, dead_lo_ok_def, cx_dead_def, SUBSET_DEF] >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[] >> rpt strip_tac >>
  TRY (qpat_assum `!x. x NOTIN tn.t_trans` (qspec_then `(k,b)` mp_tac) >> simp[]) >>
  TRY (qpat_assum `!x. x NOTIN tn.t_stor` (qspec_then `(k,b)` mp_tac) >> simp[]) >>
  FIRST
    [qpat_assum `(k,b) IN tn.t_trans` (K ALL_TAC) >>
     qpat_x_assum `!x. x IN tn.t_trans ==> _` (qspec_then `(k,b)` mp_tac),
     qpat_assum `(k,b) IN tn.t_stor` (K ALL_TAC) >>
     qpat_x_assum `!x. x IN tn.t_stor ==> _` (qspec_then `(k,b)` mp_tac)] >>
  simp[] >> strip_tac >>
  FIRST
    [qpat_x_assum `!st j b'. storage_dead H T st j b' ==> _`
       (qspecl_then [`s.vs_transient cx.txn.target`,`w2n k`,`b`] mp_tac),
     qpat_x_assum `!st j b'. storage_dead H F st j b' ==> _`
       (qspecl_then [`(s.vs_accounts cx.txn.target).storage`,`w2n k`,`b`] mp_tac)] >>
  simp[]
QED
