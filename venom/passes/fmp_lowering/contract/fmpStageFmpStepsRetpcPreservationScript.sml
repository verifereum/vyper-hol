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

Theorem fmp_retpc_taint:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}
Proof
  strip_tac >>
  simp[step_taint_def, out_taint_def, written_taint_def, mem_taint_def,
       update_var_def, new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       imm_taint_def, eval_operand_def, FLOOKUP_DEF, taint_component_equality] >>
  SET_TAC[]
QED

Theorem fmp_retpc_env_write:
  fmp_env_rel sm fn live G tv s t /\ retpc_var fn pc ==>
  fmp_env_rel sm fn live (DRESTRICT G (COMPL {pc}))
    (set_var_taint tv [pc] {}) (update_var pc x s) (update_var pc y t)
Proof
  simp[fmp_env_rel_def, update_var_def, FLOOKUP_UPDATE,
       set_var_taint_def, FLOOKUP_DRESTRICT, op_taint_def] >>
  rpt strip_tac >> Cases_on `v = pc` >> gvs[] >>
  first_x_assum drule >> strip_tac >> qexists_tac `y'` >> simp[]
QED
