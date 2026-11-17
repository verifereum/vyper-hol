(* Typed storage-array continuations using counted header and bounds tails. *)
Theory targetStorageArraySummaryMemory
Ancestors
  targetStorageArraySuffixMemory targetSubscriptSplit targetSubscriptContinuation
  targetPlaceSimDefs exprReasonOperand exprSimHyps exprSimHypsDefs
  loweringPosts exprSimDefs exprSimProps exprLowering exprLoweringProps
  compileEnv loweringStateRelDefs gasSummary gasOutcome fragGasMode fragExec
  vyperValue vyperTypeSystem vyperInterpreter vyperStorageFootprint vyperState venomState
  list finite_map

Theorem target_storage_array_summary_mem[local]:
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    target_post H ctx func cenv cx es0 sa sn s0 es
      (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
      (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s) /\
  valid_horizon cx st0 H0 es'.storage_trace /\
  extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es = (res,es') /\
  expr_sim_inv cenv cx env es /\
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    storage_read_live H tr (get_storage cx es tr) slot
      (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))) /\
  w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
  value_has_type itv (IntV i) /\ eval_operand ix s = SOME (i2w i) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (extend_place cx
      (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
      (ValueSubscript (IntV i))) (es,s)
    (\res ee u. !H. valid_horizon cx st0 H ee.storage_trace ==> ?pv'. res = INL pv' /\
      target_post H ctx func cenv cx es0 sa sb s0 ee pv' (Type ety) op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  `target_post H0 ctx func cenv cx es0 sa sn s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
   storage_read_live H0 tr (get_storage cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))` by simp[] >>
  drule_all target_subscript_storage_compile >> strip_tac >> gvs[] >>
  `w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256)`
    by decide_tac >>
  `target_post H0 ctx func cenv cx es0 sa sn s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
   storage_read_live H0 tr (get_storage cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))` by simp[] >>
  Cases_on `res`
  >- (drule_all target_storage_array_suffix_mem >> strip_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`INL x`, `es'`, `OK u`] >> conj_tac
      >- (simp[gas_marked_exec_def, target_subscript_extend_gas_obs] >> metis_tac[]) >>
      simp[] >> disj1_tac >> rpt strip_tac >>
      `target_post H ctx func cenv cx es0 sa sb s0 es' x (Type ety)
        (dst,SOME (slot_loc tr),SOME (ValPT ety)) u` by simp[] >>
      `storage_well_formed_on cx (es' with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es' (FST H)` by
        (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
      fs[target_post_def, locals_kept_def, popped_kept_def,
         stmt_state_rel_start_gas_obs] >> metis_tac[]) >>
  drule_all target_storage_array_error_suffix_mem >> strip_tac >> gvs[] >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INR (Error (RuntimeError msg))`, `es`, `Abort Revert_abort u`] >>
  simp[gas_marked_exec_def, target_subscript_extend_gas_obs,
       expr_exit_def, exit_result_def, halt_exit_def] >> metis_tac[]

QED

Theorem target_storage_array_typed_summary_mem:
  subscript_vtype (Type aty) (expr_type e) = SOME vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    target_post H ctx func cenv cx es0 sa sn s0 es
      (PlaceR (StoragePlace tr slot tv)) (Type aty) rb s /\
    expr_post H ctx func cenv cx e ee sm sn t es key ix s) /\
  valid_horizon cx st0 H0 es'.storage_trace /\
  extend_place cx (PlaceR (StoragePlace tr slot tv)) (ValueSubscript key) es = (res,es') /\
  expr_sim_inv cenv cx env es /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    storage_read_live H tr (get_storage cx es tr) slot tv) /\
  w2n slot + type_slot_size tv <= dimword(:256) /\
  (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
    w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sn.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (extend_place cx (PlaceR (StoragePlace tr slot tv)) (ValueSubscript key)) (es,s)
    (\res ee u. !H. valid_horizon cx st0 H ee.storage_trace ==> ?pv'. res = INL pv' /\
      target_post H ctx func cenv cx es0 sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  `target_post H0 ctx func cenv cx es0 sa sn s0 es
    (PlaceR (StoragePlace tr slot tv)) (Type aty) rb s /\
   expr_post H0 ctx func cenv cx e ee sm sn t es key ix s` by simp[] >>
  `!H. valid_horizon cx st0 H es'.storage_trace ==>
    target_post H ctx func cenv cx es0 sa sn s0 es
      (PlaceR (StoragePlace tr slot tv)) (Type aty) rb s` by simp[] >>
  `?w. place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) w (FST (SND rb)) (Type aty)` by
    (fs[target_post_def] >> metis_tac[]) >>
  qpat_x_assum `target_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  gvs[place_ptr_rel_def] >> Cases_on `aty` >>
  gvs[subscript_vtype_def, AllCaseEqs()] >>
  rename1 `evaluate_type _ (ArrayT ety bd) = _` >> Cases_on `bd` >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `expr_post H0 ctx func cenv cx e ee sm sn t es key ix s` by simp[] >>
  drule_all target_subscript_int_index_view >> strip_tac >> gvs[]
  >- (drule (SRULE [] (Q.INST [`dyn` |-> `F`] target_storage_array_summary_mem)) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  drule (SRULE [] (Q.INST [`dyn` |-> `T`] target_storage_array_summary_mem)) >>
  simp[] >> disch_then drule_all >> simp[]
QED
