Theory dftOrdinaryError
Ancestors
  dftLocalOrdinaryClosure dftOrdinarySwap
  dftOccurrenceOrdinaryObserve venomExecSemantics venomEffects venomInst
  venomState venomWf opcodeClass list pred_set
Libs
  stepInstBaseLib

Theorem dft_ordinary_error_special:
  dft_ordinary_swap_pair x y /\ inst_wf x /\
  (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  step_inst_base x s = Error e ==>
  MEM x.inst_opcode [DELEGATECALL; CREATE; CREATE2]
Proof
  strip_tac >> spose_not_then assume_tac >>
  `~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
   x.inst_opcode <> INVOKE /\ x.inst_opcode <> GAS /\
   x.inst_opcode <> ALLOCA` by
    (fs[dft_ordinary_swap_pair_def] >>
     Cases_on `x.inst_opcode` >> gvs[is_alloca_op_def]) >>
  drule_all dft_shaped_ordinary_no_error >> simp[]
QED

