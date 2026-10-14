(* Additive projections of the ACTUALLY proved core execution simulations.
 * All original premises, results and witnesses remain; no admitted pass used. *)
Theory coreOracleSim
Ancestors
  coreOracleTransport execEquivProps stateEquiv stateEquivProps
  venomExecSemantics venomInst venomState venomWf list

Theorem core_step_observable:
  state_equiv vars s1 s2 /\ inst.inst_opcode <> INVOKE /\
  (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
  result_equiv vars (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2) /\
  observable_result_equiv (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  strip_tac >> drule_all step_inst_result_equiv >> strip_tac >>
  simp[] >> irule result_equiv_implies_observable_result >>
  qexists_tac `vars` >> simp[]
QED

Theorem core_block_observable:
  state_equiv vars s1 s2 /\
  EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
  (!inst. MEM inst bb.bb_instructions ==>
    !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
  result_equiv vars (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2) /\
  observable_result_equiv (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)
Proof
  strip_tac >> drule_all exec_block_result_equiv >> strip_tac >>
  simp[] >> irule result_equiv_implies_observable_result >>
  qexists_tac `vars` >> simp[]
QED

Theorem core_function_observable:
  state_equiv vars s1 s2 /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst x. MEM inst bb.bb_instructions /\
      MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
  result_equiv vars (run_function fuel ctx fn s1) (run_function fuel ctx fn s2) /\
  observable_result_equiv (run_function fuel ctx fn s1) (run_function fuel ctx fn s2)
Proof
  strip_tac >> drule_all run_function_result_equiv >> strip_tac >>
  simp[] >> irule result_equiv_implies_observable_result >>
  qexists_tac `vars` >> simp[]
QED
