(* Local semantic projections for the continuation-sensitive runner. *)
Theory o1LowerDloadRunnerBoundary
Ancestors
  venomInstProps venomExecSemantics venomExecProps venomExecProofs contextCodegenRel
  venomState venomInst list

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
