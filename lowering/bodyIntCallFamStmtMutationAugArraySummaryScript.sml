(* Observation-free array place extension, including bounds failure. *)
Theory bodyIntCallFamStmtMutationAugArraySummary
Ancestors
  bodyIntCallFamStmtMutationAugTargetArrayCounted targetSubscriptSplit
  targetSubscriptMemory targetSubscriptStorage bodyIntCallJointContract
  gasSummary exprSimDefs exprSimHypsDefs exprLoweringProps
  targetPlaceSimDefs vyperInterpreter vyperState fragGasMode loweringPosts
  vyperPlaceFrames fragExec

Theorem intcall_target_memory_array_extend_summary:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sm s /\ es.gas_obs = [] /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sm s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv fp.jc_cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv fp.jc_cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 32 (type_memory_bytes ce ety)
    (is_signed_type ity)
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb fp.jc_func /\ sa.cs_next_var <= sm.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\
  (!l. idx <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at sb x) ==>
  gas_summary_at F (fp.jc_ctx,fp.jc_func) []
    (extend_place fp.jc_cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i))) (es,s)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 ee pv' (Type ety)
        (dst,SOME LocMemory,SOME (ValPT ety)) u /\
      intcall_expr_cont fp ce env es sm s ee sb u)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `es with gas_obs := [] = es` by simp[evaluation_state_component_equality] >>
  `expr_sim_inv ce fp.jc_cx env es /\ local_ptrs_reserved ce sm` by
    fs[intcall_expr_res_def] >>
  Cases_on `extend_place fp.jc_cx (PlaceR (MemoryPlace id path))
    (ValueSubscript (IntV i)) es` >> rename1 `_ = (res,es')` >>
  Cases_on `res`
  >- (`es' = es` by metis_tac[extend_place_state] >> gvs[] >>
      drule_all intcall_target_memory_array_suffix >> strip_tac >>
      irule target_subscript_extend_summary_normal >>
      goal_assum (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
      simp[evaluation_state_component_equality]) >>
  drule_all target_memory_array_error_suffix >> strip_tac >>
  irule target_subscript_extend_summary_error >>
  goal_assum (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
  qexists_tac `Abort Revert_abort u` >>
  gvs[exit_result_def, expr_exit_def]
QED

Theorem intcall_target_storage_array_extend_summary:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sm s /\ es.gas_obs = [] /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  (dyn ==> w2n (lookup_storage slot (get_storage fp.jc_cx es tr)) <= cnt) /\
  storage_read_live fp.jc_cx tr (get_storage fp.jc_cx es tr) slot
    (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  w2n slot + type_slot_size (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) <= dimword(:256) /\
  evaluate_type (get_tenv fp.jc_cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 1 (type_slot_size etv)
    (is_signed_type ity)
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) sm = (dst,sb) /\
  fn_has_code sm sb fp.jc_func /\ sa.cs_next_var <= sm.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\ (!l. idx <> Label l) /\
  (!l. FST rb <> Label l) /\ (!x. dst = Var x ==> not_fresh_at sb x) ==>
  gas_summary_at F (fp.jc_ctx,fp.jc_func) []
    (extend_place fp.jc_cx
      (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
      (ValueSubscript (IntV i))) (es,s)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 ee pv' (Type ety)
        (dst,SOME (slot_loc tr),SOME (ValPT ety)) u /\
      intcall_expr_cont fp ce env es sm s ee sb u)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `es with gas_obs := [] = es` by simp[evaluation_state_component_equality] >>
  `local_ptrs_reserved ce sm` by fs[intcall_expr_res_def] >>
  Cases_on `extend_place fp.jc_cx
    (PlaceR (StoragePlace tr slot (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))))
    (ValueSubscript (IntV i)) es` >> rename1 `_ = (res,es')` >>
  Cases_on `res`
  >- (`es' = es` by metis_tac[extend_place_state] >>
      qpat_x_assum `es' = es` SUBST_ALL_TAC >>
      drule_all intcall_target_storage_array_suffix >> strip_tac >>
      irule target_subscript_extend_summary_normal >>
      goal_assum (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >> simp[]) >>
  drule_all target_storage_array_error_suffix >> strip_tac >>
  irule target_subscript_extend_summary_error >>
  goal_assum (drule_at (Pat `extend_place _ _ _ _ = _`)) >>
  qexists_tac `Abort Revert_abort u` >>
  gvs[exit_result_def, expr_exit_def]
QED
