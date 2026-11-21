(* Allocation-map extension across successful non-INVOKE sequences. *)
Theory stmtSimLogSuffixFrame
Ancestors
  venomMemProofs venomExecSemantics
  venomState venomInst finite_map list exprLoweringProps

Theorem log_step_old_allocas[local]:
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK t ==>
  !aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[update_var_def, FLOOKUP_UPDATE] >>
      Cases_on `inst.inst_id = aid` >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_preserves_allocas] >> simp[]
QED

Theorem log_run_old_allocas:
  !code s t. run_inst_seq code s = OK t /\
    EVERY (\i. i.inst_opcode <> INVOKE) code ==>
    !aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >>
  rename1 `step_inst_base head s = OK middle` >>
  `FLOOKUP middle.vs_allocas aid = SOME b` by
    metis_tac[log_step_old_allocas] >>
  first_x_assum drule_all >> simp[]
QED
