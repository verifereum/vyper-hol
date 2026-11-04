Theory dftLocalOrdinaryClosure
Ancestors
  dftOrdinaryStop venomExecSemantics venomEffects venomInst venomWf list
Libs
  stepInstBaseLib

Theorem dft_shaped_ordinary_outcome:
  inst_wf i /\ ~is_pseudo i.inst_opcode /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> ALLOCA /\
  ~MEM i.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  (?t. step_inst_base i s = OK t) \/
  (?a t. step_inst_base i s = Abort a t)
Proof
  strip_tac >>
  Cases_on `opcode_fail_class i.inst_opcode = NoFail`
  >- (disj1_tac >> irule dft_ordinary_nofail_total >>
      simp[] >> Cases_on `i.inst_opcode` >> gvs[is_alloca_op_def]) >>
  Cases_on `opcode_fail_class i.inst_opcode = CanExHalt`
  >- (drule_all dft_ordinary_canexhalt_defined >> metis_tac[]) >>
  `i.inst_opcode = ASSERT` by
    (Cases_on `i.inst_opcode` >> gvs[opcode_fail_class_def]) >>
  gvs[inst_wf_def] >> with_opcode_clause simp >>
  gvs[LENGTH_EQ_NUM_compute] >>
  `?v. eval_operand h s = SOME v` by metis_tac[] >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem dft_shaped_ordinary_no_error:
  inst_wf i /\ ~is_pseudo i.inst_opcode /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> ALLOCA /\
  ~MEM i.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  !e. step_inst_base i s <> Error e
Proof
  strip_tac >> drule_all dft_shaped_ordinary_outcome >>
  strip_tac >> gvs[]
QED
