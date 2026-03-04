(*
 * Execution Equivalence Properties (Statements Only)
 *
 * Re-exports top-level theorems from execEquivProofs via ACCEPT_TAC.
 * Proofs live in proofs/execEquivProofsScript.sml.
 *
 * TOP-LEVEL THEOREMS:
 *   - step_inst_state_equiv      : Single instruction step preserves state_equiv
 *   - step_in_block_state_equiv  : Block step preserves state_equiv
 *   - run_block_state_equiv      : Block execution preserves state_equiv
 *   - step_inst_result_equiv     : Instruction stepping preserves result_equiv
 *   - step_in_block_result_equiv : Block stepping preserves result_equiv
 *   - run_block_result_equiv     : Block execution preserves result_equiv
 *)

Theory execEquivProps
Ancestors
  execEquivProofs

(* ==========================================================================
   Instruction Stepping Preserves Equivalence (success case)
   ========================================================================== *)

Theorem step_inst_state_equiv:
  !inst s1 s2 r1.
    state_equiv s1 s2 /\
    step_inst inst s1 = OK r1
  ==>
    ?r2. step_inst inst s2 = OK r2 /\ state_equiv r1 r2
Proof
  ACCEPT_TAC execEquivProofsTheory.step_inst_state_equiv
QED

Theorem step_in_block_state_equiv:
  !bb s1 s2 r1 is_term.
    state_equiv s1 s2 /\
    step_in_block bb s1 = (OK r1, is_term)
  ==>
    ?r2. step_in_block bb s2 = (OK r2, is_term) /\ state_equiv r1 r2
Proof
  ACCEPT_TAC execEquivProofsTheory.step_in_block_state_equiv
QED

Theorem run_block_state_equiv:
  !bb s1 s2 r1.
    state_equiv s1 s2 /\
    run_block bb s1 = OK r1
  ==>
    ?r2. run_block bb s2 = OK r2 /\ state_equiv r1 r2
Proof
  ACCEPT_TAC execEquivProofsTheory.run_block_state_equiv
QED

(* ==========================================================================
   Instruction Stepping Preserves Result Equivalence (all cases)
   ========================================================================== *)

Theorem step_inst_result_equiv:
  !inst s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (step_inst inst s1) (step_inst inst s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.step_inst_result_equiv
QED

Theorem step_in_block_result_equiv:
  !bb s1 s2.
    state_equiv s1 s2 ==>
      result_equiv (FST (step_in_block bb s1)) (FST (step_in_block bb s2)) /\
      SND (step_in_block bb s1) = SND (step_in_block bb s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.step_in_block_result_equiv
QED

Theorem run_block_result_equiv:
  !bb s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (run_block bb s1) (run_block bb s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.run_block_result_equiv
QED
