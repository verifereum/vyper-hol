(* Counted landings for straight, non-writing subscript suffixes. *)
Theory bodyIntCallFamAggSubscriptReadOnly
Ancestors
  bodyIntCallJointAggCore bodyIntCallJointContract exprSimHash
  fragGasMode fragExec compileEnv exprLoweringProps venomState venomInst
  freshWrites placeMemoryPrimitiveForward

Theorem intcall_readonly_run_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  sa.cs_next_var <= si.cs_next_var /\ si.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_bb = si.cs_current_bb /\
  sb.cs_current_insts = si.cs_current_insts ++ emitted_insts si sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts si sb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts si sb) /\
  fn_has_code si sb fp.jc_func /\
  run_inst_seq (emitted_insts si sb) s = OK t /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at si x ==> lookup_var x t = lookup_var x s) ==>
  gas_marked_path F fp.jc_ctx fp.jc_func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  intcall_expr_cont fp ce env es0 sa s0 es sb
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `~s.vs_halted /\ s.vs_current_bb = si.cs_current_bb /\
   s.vs_inst_idx = LENGTH si.cs_current_insts /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce si` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  conj_tac
  >- (drule_all straight_line_zero_gas_path >> simp[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    (irule hash_readonly_state_rel >> qexistsl_tac [`s`, `si`] >> simp[]) >>
  `~t.vs_halted /\ t.vs_current_bb = si.cs_current_bb` by
    fs[venom_state_component_equality] >>
  irule intcall_expr_cont_readonly >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  qexistsl_tac [`s`, `si`] >>
  fs[venom_state_component_equality, lookup_var_def]
QED
