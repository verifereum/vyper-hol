(*
 * Parameterized Execution Equivalence — Properties (Statements Only)
 *
 * Re-exports from proofs/execEquivParamProofsScript.sml via ACCEPT_TAC.
 *)

Theory execEquivParamProps
Ancestors
  execEquivParamProofs

Theorem step_inst_preserves_R:
  !(R : venom_state -> venom_state -> bool) inst s1 s2.
    valid_state_rel R /\ R s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R (step_inst inst s1) (step_inst inst s2)
Proof
  ACCEPT_TAC step_inst_preserves_R_proof
QED

Theorem state_equiv_valid_state_rel:
  valid_state_rel state_equiv
Proof
  ACCEPT_TAC state_equiv_valid_state_rel_proof
QED

Theorem state_equiv_except_valid_state_rel:
  !fresh. valid_state_rel (state_equiv_except fresh)
Proof
  ACCEPT_TAC state_equiv_except_valid_state_rel_proof
QED
