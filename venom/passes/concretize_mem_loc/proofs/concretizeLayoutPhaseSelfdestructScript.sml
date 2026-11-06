Theory concretizeLayoutPhaseSelfdestruct
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutHaltExit
  concretizeLayoutLocalSelfdestruct concretizeLayoutSupplement
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  frameRelocationLocal frameRelocationEnvironment ptrDiscipline
  venomExecSemantics venomState venomInst list pred_set

(* Storage masks do not move when balances are transferred.  The existing
   account theorem covers both beneficiary=self and beneficiary<>self. *)
Theorem concretize_selfdestruct_supplement:
  inst.inst_opcode = SELFDESTRUCT /\ relocation_env s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  concretize_supplement D tn s t /\
  step_inst_base inst s = Halt post /\ step_inst_base inst t = Halt tpost ==>
  concretize_supplement D (step_taint inst s post tn) post tpost
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = Halt post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[eval_operands_def] >>
  `eval_operand addr_op t = SOME addr` by metis_tac[MEM] >>
  qpat_x_assum `step_inst_base inst t = Halt tpost` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `inst.inst_opcode = SELFDESTRUCT`
    (fn th => pure_rewrite_tac[th, venomInstTheory.opcode_case_def]) >>
  fs[relocation_env_def] >> strip_tac >> gvs[] >>
  gvs[concretize_supplement_def, halt_state_def, set_returndata_def,
    step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  drule accounts_agree_except_selfdestruct >>
  disch_then (qspecl_then [`t.vs_call_ctx.cc_address`, `w2w addr`] mp_tac) >> simp[]
QED


val _ = export_theory();
