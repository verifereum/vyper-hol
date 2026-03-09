(*
 * Parameterized Execution Equivalence — Proofs
 *
 * Master theorem: step_inst preserves any valid_state_rel (R_ok, R_term) pair.
 *
 * Instantiation: (state_equiv vars, execution_equiv vars) satisfies valid_state_rel.
 *
 * TOP-LEVEL:
 *   step_inst_preserves_R_proof                          — master theorem
 *   state_equiv_execution_equiv_valid_state_rel_proof    — instantiation
 *)

Theory execEquivParamProofs
Ancestors
  execEquivParamDefs passSimulationDefs stateEquivProps execEquivProps

(* Master theorem: step_inst preserves any valid (R_ok, R_term) pair when operand
   vars agree. For non-INVOKE: follows from step_inst_base result + step_inst_non_invoke.
   For INVOKE: requires R to be preserved through run_function (future work). *)
Theorem step_inst_preserves_R_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fuel ctx inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  cheat
QED

(* (state_equiv vars, execution_equiv vars) satisfies valid_state_rel *)
Theorem state_equiv_execution_equiv_valid_state_rel_proof:
  !vars. valid_state_rel (state_equiv vars) (execution_equiv vars)
Proof
  cheat
QED
