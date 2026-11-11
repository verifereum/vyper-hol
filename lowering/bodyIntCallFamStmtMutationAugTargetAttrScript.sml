(* Same-witness resource landing for the attribute address instruction. *)
Theory bodyIntCallFamStmtMutationAugTargetAttr
Ancestors
  bodyIntCallFamStmtMutationAugTargetMappingTail
  targetPlaceSimCasesBase exprSimMapKey emitHelperProps
  bodyIntCallJointContract venomState venomInst

Theorem intcall_target_add_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env ee sm s /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0 ee pv vt rb s /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst,sb) /\
  fn_has_code sm sb fp.jc_func /\
  eval_operand (FST rb) s = SOME w /\
  place_ptr_rel ce fp.jc_cx s pv' (w + n2w off) (FST (SND rb)) vt' /\
  place_readable fp.jc_cx ee pv' /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s0 ee pv' vt'
        (dst,FST (SND rb),SOME (value_type_place vt')) u /\
      intcall_expr_cont fp ce env ee sm s ee sb u
Proof
  strip_tac >> drule_all target_post_add >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) emit_ADD_frame >>
  simp[eval_operand_def] >> disch_then drule >> strip_tac >>
  gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) intcall_readonly_emit_run >>
  simp[is_terminator_def] >> disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) s = OK endpoint` >>
  qexists `endpoint with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[]
QED
