(* Typed storage-array continuations using counted header and bounds tails. *)
Theory targetStorageArraySummaryMemory
Ancestors
  targetStorageArraySuffixMemory targetSubscriptSplit targetSubscriptContinuation
  targetPlaceSimDefs exprReasonOperand exprSimHyps exprSimHypsDefs
  loweringPosts exprSimDefs exprSimProps exprLowering exprLoweringProps
  compileEnv loweringStateRelDefs gasSummary gasOutcome fragGasMode fragExec
  vyperValue vyperTypeSystem vyperInterpreter vyperState venomState
  list finite_map

Theorem target_storage_array_summary_mem[local]:
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt) /\
  storage_read_live cx tr (get_storage cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
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
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es0 sa sb s0 ee pv' (Type ety) op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all target_subscript_storage_compile >> strip_tac >> gvs[] >>
  `w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256)`
    by decide_tac >>
  Cases_on `extend_place cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es` >>
  rename1 `extend_place _ _ _ _ = (result,es')` >> Cases_on `result`
  >- (drule_all target_storage_array_suffix_mem >> strip_tac >>
      irule target_subscript_extend_summary_normal >>
      goal_assum (drule_at Any) >> simp[] >>
      fs[target_post_def, locals_kept_def, popped_kept_def] >> metis_tac[]) >>
  drule_all target_storage_array_error_suffix_mem >> strip_tac >> gvs[] >>
  irule target_subscript_extend_summary_error >>
  qexistsl [`Error (RuntimeError msg)`, `es`, `Abort Revert_abort u`] >>
  simp[expr_exit_def, exit_result_def]
QED
