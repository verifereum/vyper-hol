Theory createSizeClassificationCounterexample
Ancestors
  venomExecSemantics venomState venomInst vfmConstants
Libs
  wordsLib

Theorem oversized_create_dispatch:
  !s. step_inst_base
    (mk_inst 0 CREATE [Lit 0w; Lit 0w; Lit 49153w] ["out"]) s =
    Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  simp[step_inst_base_def, mk_inst_def, eval_operand_def,
       exec_create_def, max_code_size_def]
QED

Theorem oversized_create_classification:
  ~is_terminator
    (mk_inst 0 CREATE [Lit 0w; Lit 0w; Lit 49153w] ["out"]).inst_opcode /\
  ~((mk_inst 0 CREATE [Lit 0w; Lit 0w; Lit 49153w] ["out"]).inst_opcode = ASSERT \/
    (mk_inst 0 CREATE [Lit 0w; Lit 0w; Lit 49153w] ["out"]).inst_opcode = ASSERT_UNREACHABLE \/
    (mk_inst 0 CREATE [Lit 0w; Lit 0w; Lit 49153w] ["out"]).inst_opcode = RETURNDATACOPY)
Proof
  EVAL_TAC
QED

Theorem frozen_abort_classification_false:
  ~(!inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode ==>
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY)
Proof
  strip_tac >>
  first_x_assum (qspec_then
    `mk_inst 0 CREATE [Lit 0w; Lit 0w; Lit 49153w] ["out"]` mp_tac) >>
  simp[oversized_create_dispatch, mk_inst_def, is_terminator_def]
QED
