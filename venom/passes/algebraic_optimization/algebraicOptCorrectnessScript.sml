(*
 * Algebraic Optimization Correctness (Statements Only)
 *
 * This file records the intended correctness statements for the algebraic
 * optimization pass (peephole + offset + iszero-chain rewrites).
 * Proofs are intentionally omitted.
 *)

Theory algebraicOptCorrectness
Ancestors
  algebraicOptTransform stateEquiv venomSem venomInst venomState

(* ======================================================================
   Safety Predicates (to rule out undefined-operand errors)
   ====================================================================== *)

Definition algebraic_opt_safe_block_def:
  algebraic_opt_safe_block bb s <=>
    terminates (run_block bb s)
End

Definition algebraic_opt_safe_function_def:
  algebraic_opt_safe_function fn s <=>
    ?fuel. terminates (run_function fuel fn s)
End

(* ======================================================================
   Correctness Statement
   ====================================================================== *)

(* Function-level correctness using pass_correct (no fresh vars). *)
Theorem algebraic_opt_function_correct:
  !fn fn' s.
    algebraic_opt_transform fn fn' /\
    algebraic_opt_safe_function fn s ==>
    pass_correct {}
      (\fuel. run_function fuel fn s)
      (\fuel. run_function fuel fn' s)
Proof
  cheat
QED
