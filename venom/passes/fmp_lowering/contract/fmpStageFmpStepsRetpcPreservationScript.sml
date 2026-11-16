Theory fmpStageFmpStepsRetpcPreservation
Ancestors
  fmpStageOpBase fmpStageControl fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLedgerProps livenessProofs ptrDiscipline
  codegenRel passSimulationDefs o1PassContract venomExecSemantics venomState venomInst finite_map list

Theorem fmp_retpc_source_step:
  inst.inst_opcode = RETPC_PARAM /\ step_inst k C inst s = r /\
  terminates r ==>
  ?pc idx. inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [pc] /\
    r = OK (update_var pc s.vs_return_pc_token s)
Proof
  strip_tac >>
  `step_inst k C inst s = step_inst_base inst s` by
    (irule step_inst_non_invoke >> simp[]) >>
  gvs[] >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[Once step_inst_base_def] >>
  simp[AllCaseEqs(), terminates_def] >>
  namedCases_on `inst.inst_operands` ["", "arg args"] >> simp[] >>
  Cases_on `arg` >> simp[] >>
  Cases_on `args` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "pc outs"] >> simp[] >>
  Cases_on `outs` >> simp[] >>
  simp[Once step_inst_base_def]
QED
