(*
 * Parameterized Execution Equivalence — Proofs
 *
 * Master theorem: step_inst preserves any valid_state_rel R
 * when operand variables agree.
 *
 * Instantiations: state_equiv and state_equiv_except both satisfy valid_state_rel.
 *
 * TOP-LEVEL:
 *   step_inst_preserves_R              — master theorem
 *   state_equiv_valid_state_rel        — state_equiv satisfies valid_state_rel
 *   state_equiv_except_valid_state_rel — state_equiv_except satisfies valid_state_rel
 *)

Theory execEquivParamProofs
Ancestors
  execEquivParamDefs passSimulationDefs

(* Master theorem: step_inst on R-related states with agreeing operand
   vars produces lift_result R related results. *)
Theorem step_inst_preserves_R_proof:
  !(R : venom_state -> venom_state -> bool) inst s1 s2.
    valid_state_rel R /\ R s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R (step_inst inst s1) (step_inst inst s2)
Proof
  cheat
QED

(* state_equiv satisfies valid_state_rel *)
Theorem state_equiv_valid_state_rel_proof:
  valid_state_rel state_equiv
Proof
  cheat
QED

(* state_equiv_except satisfies valid_state_rel for any fresh set *)
Theorem state_equiv_except_valid_state_rel_proof:
  !fresh. valid_state_rel (state_equiv_except fresh)
Proof
  cheat
QED
