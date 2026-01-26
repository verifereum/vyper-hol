(*
 * Algebraic Optimization Correctness (Statements Only)
 *
 * This file records the intended correctness statements for the algebraic
 * optimization pass (peephole + offset + iszero-chain rewrites).
 * Proofs are intentionally omitted.
 *)

Theory algebraicOptCorrect
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
   Correctness Statements
   ====================================================================== *)

(* Instruction-level equivalence for peephole rewrites.
   Requires operands to be defined to avoid changing Error behavior. *)
Theorem algebraic_opt_step_correct:
  !inst inst' prefer_iszero is_truthy cmp_flip s.
    transform_inst_list prefer_iszero is_truthy cmp_flip inst = [inst'] /\
    eval_operands inst.inst_operands s <> NONE ==>
    step_inst inst' s = step_inst inst s
Proof
  cheat
QED

(* Block-level correctness using pass_correct (no fresh vars). *)
Theorem algebraic_opt_block_correct:
  !bb s prefer_iszero is_truthy cmp_flip.
    algebraic_opt_safe_block bb s ==>
    result_equiv_except {}
      (run_block bb s)
      (run_block (transform_block prefer_iszero is_truthy cmp_flip bb) s)
Proof
  cheat
QED

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
