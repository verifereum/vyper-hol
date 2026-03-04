(*
 * Execution Equivalence Properties (Statements Only)
 *
 * Re-exports top-level theorems from execEquivProofs via ACCEPT_TAC.
 * Proofs live in proofs/execEquivProofsScript.sml.
 *
 * TOP-LEVEL THEOREMS:
 *   - run_block_state_equiv  : Block execution preserves state_equiv (OK case)
 *   - run_block_result_equiv : Block execution preserves result_equiv (all cases)
 *)

Theory execEquivProps
Ancestors
  execEquivProofs

(* ==========================================================================
   Block Execution Preserves Equivalence
   ========================================================================== *)

(* Running a block on equivalent states produces equivalent OK results *)
Theorem run_block_state_equiv:
  !bb s1 s2 r1.
    state_equiv s1 s2 /\
    run_block bb s1 = OK r1
  ==>
    ?r2. run_block bb s2 = OK r2 /\ state_equiv r1 r2
Proof
  ACCEPT_TAC execEquivProofsTheory.run_block_state_equiv
QED

(* Running a block on equivalent states produces equivalent results (all cases) *)
Theorem run_block_result_equiv:
  !bb s1 s2.
    state_equiv s1 s2 ==>
    result_equiv (run_block bb s1) (run_block bb s2)
Proof
  ACCEPT_TAC execEquivProofsTheory.run_block_result_equiv
QED
