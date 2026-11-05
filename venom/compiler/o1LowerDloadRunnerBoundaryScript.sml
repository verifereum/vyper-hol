(* Local semantic projections for the continuation-sensitive runner. *)
Theory o1LowerDloadRunnerBoundary
Ancestors
  venomInstProps venomExecSemantics venomExecProps venomExecProofs contextCodegenRel
  venomState venomInst list o1LowerDloadReadiness o1LowerDloadJointRestore

Theorem ld_step_ok_call_ctx:
  step_inst fuel C inst s = OK s1 ==> s1.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> reverse (Cases_on `is_terminator inst.inst_opcode`)
  >- (drule_all step_preserves_call_ctx >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), jump_to_def] >>
  rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem ld_ret_endpoint:
  inst.inst_opcode = RET /\ step_inst fuel C inst s = IntRet ir se ==>
  se = s
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ld_enters_block_call_ctx:
  enters_block fn s s1 ==> s1.vs_call_ctx = s.vs_call_ctx
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem ld_setup_callee_call_ctx:
  setup_callee fn args s = SOME cs ==> cs.vs_call_ctx = s.vs_call_ctx
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ld_invoke_bind_control:
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state caller se)) = SOME s1 ==>
  s1.vs_current_bb = caller.vs_current_bb /\
  s1.vs_inst_idx = caller.vs_inst_idx /\
  s1.vs_prev_bb = caller.vs_prev_bb
Proof
  strip_tac >> drule ld_bind_outputs_vars_only >>
  simp[adopt_return_fmp_def] >>
  Cases_on `ir.iret_adopt_fmp` >> simp[merge_callee_state_def] >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem ld_invoke_bind_successor:
  wf_function fn /\ active_inst fn callinst caller /\
  callinst.inst_opcode = INVOKE /\
  bind_outputs callinst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state caller se)) = SOME s1 ==>
  ?next. active_inst fn next (s1 with vs_inst_idx := SUC caller.vs_inst_idx)
Proof
  strip_tac >> drule ld_invoke_bind_control >> strip_tac >>
  irule ld_nonterminator_successor >> simp[] >>
  qexists_tac `callinst` >> simp[is_terminator_def]
QED

Theorem ld_terminator_ok_branch:
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK s1 ==>
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ s1.vs_halted = s.vs_halted
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), jump_to_def] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Theorem ld_step_ok_halted:
  step_inst fuel C inst s = OK s1 ==> s1.vs_halted = s.vs_halted
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all ld_terminator_ok_branch >> simp[]) >>
  drule_all step_preserves_halted >> simp[]
QED

Theorem ld_enters_block_halted:
  enters_block fn s s1 ==> s1.vs_halted = s.vs_halted
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED
