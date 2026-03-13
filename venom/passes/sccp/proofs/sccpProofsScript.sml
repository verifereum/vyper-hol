(*
 * SCCP — Proofs
 *
 * Key properties:
 * 1. sccp_inst with a sound lattice preserves semantics
 * 2. sccp_function preserves execution equivalence
 *
 * Uses the generic dataflow framework (df_analyze) with worklist
 * iteration. Analysis soundness (const_sound holds at each program
 * point during execution) is threaded through the framework's
 * transfer_sound / edge_transfer_sound mechanism.
 *)

Theory sccpProofs
Ancestors
  sccpDefs passSimulationProps venomWf

(* Soundness: every constant in the lattice matches the concrete state.
   Proof predicate — only used in simulation proofs, not in defs. *)
Definition const_sound_def:
  const_sound (st : const_lattice) (s : venom_state) <=>
    !v c. FLOOKUP st v = SOME (CL_Const c) ==>
      FLOOKUP s.vs_vars v = SOME c
End

(* If SCCP succeeds (no static assertion failure), the transform
   preserves execution semantics under SSA.
   If SCCP returns NONE, the program has a provably-failing
   assertion (compile error). *)
Theorem sccp_function_correct_proof:
  !fuel ctx fn fn' s.
    ssa_form fn /\
    sccp_function fn = SOME fn' ==>
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn' s)
Proof
  cheat
QED
