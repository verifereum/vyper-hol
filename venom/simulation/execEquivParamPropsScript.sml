(*
 * Parameterized Execution Equivalence — Properties (Statements Only)
 *
 * Re-exports from proofs/execEquivParamProofsScript.sml via ACCEPT_TAC.
 *)

Theory execEquivParamProps
Ancestors
  execEquivParamProofs

Theorem step_inst_preserves_R:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  ACCEPT_TAC step_inst_preserves_R_proof
QED

Theorem state_equiv_execution_equiv_valid_state_rel:
  !vars. valid_state_rel (state_equiv vars) (execution_equiv vars)
Proof
  ACCEPT_TAC state_equiv_execution_equiv_valid_state_rel_proof
QED
