Theory regularPlanSim
Ancestors
  stackPlanGen stackPlanTypes stackModel asmIR venomWf venomInst
  venomExecSemantics opcodeClass words list

Theorem regular_named_output_bound:
  inst_wf inst /\ venom_to_evm_name inst.inst_opcode = SOME name ==>
  LENGTH inst.inst_outputs <= 1
Proof
  Cases_on `inst.inst_opcode` >>
  simp[venom_to_evm_name_def, inst_wf_def]
QED

Theorem regular_named_output_shape:
  inst_wf inst /\ venom_to_evm_name inst.inst_opcode = SOME name ==>
  inst.inst_outputs = [] \/ ?out. inst.inst_outputs = [out]
Proof
  strip_tac >> drule_all regular_named_output_bound >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `LENGTH rest` >> Cases_on `rest` >> simp[]
QED

Theorem regular_named_ok_nonterminator:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ~is_terminator inst.inst_opcode
Proof
  strip_tac >> spose_not_then assume_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  gvs[venom_to_evm_name_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()]
QED

Theorem regular_named_ok_families:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ef_pure1 inst.inst_opcode \/ ef_arith1 inst.inst_opcode \/
  ef_arith2 inst.inst_opcode \/ ef_cmp inst.inst_opcode \/
  ef_bits inst.inst_opcode \/ ef_pure3 inst.inst_opcode \/
  ef_read0 inst.inst_opcode \/ ef_read1 inst.inst_opcode \/
  MEM inst.inst_opcode [SHA3; MSTORE; MSTORE8; MCOPY; SSTORE; TSTORE;
    CALLDATACOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
    CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
Proof
  strip_tac >> drule_all regular_named_ok_nonterminator >>
  Cases_on `inst.inst_opcode` >>
  gvs[venom_to_evm_name_def, is_terminator_def, ef_pure1_def,
      ef_arith1_def, ef_arith2_def, ef_cmp_def, ef_bits_def,
      ef_pure3_def, ef_read0_def, ef_read1_def]
QED

