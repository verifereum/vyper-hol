(*
 * SCCP Correctness
 *
 * Main correctness theorem: SCCP transformation preserves semantics.
 *
 * If the lattice environment is sound for a state, then running the
 * transformed program produces an equivalent result to the original.
 *)

Theory sccpCorrect
Ancestors
  sccpTransform

(* ==========================================================================
   State and Result Equivalence (simplified versions)
   ========================================================================== *)

(* Two states are equivalent if they have the same variable bindings *)
Definition state_equiv_def:
  state_equiv s1 s2 <=>
    s1.vs_vars = s2.vs_vars /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_halted = s2.vs_halted
End

(* Result equivalence *)
Definition result_equiv_def:
  result_equiv (OK s1) (OK s2) = state_equiv s1 s2 /\
  result_equiv (Halt s1) (Halt s2) = state_equiv s1 s2 /\
  result_equiv (Revert s1) (Revert s2) = state_equiv s1 s2 /\
  result_equiv (Error e1) (Error e2) = T /\
  result_equiv _ _ = F
End

(* ==========================================================================
   Well-Formedness Conditions

   Conditions under which SCCP transformation is correct.
   ========================================================================== *)

(* The lattice must be a valid fixpoint of the abstract interpretation *)
Definition sccp_fixpoint_def:
  sccp_fixpoint (lenv: lattice_env) (fn: ir_function) <=>
    (* For every instruction, abstract stepping doesn't change the lattice *)
    !bb inst.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions
    ==>
      abs_step_inst lenv inst = lenv
End

(* ==========================================================================
   Instruction-Level Correctness
   ========================================================================== *)

(* Transformed instruction produces equivalent result *)
Theorem transform_inst_correct:
  !lenv inst s s'.
    env_sound lenv s /\
    step_inst inst s = OK s'
  ==>
    ?s''. step_inst (transform_inst lenv inst) s = OK s'' /\
          state_equiv s' s''
Proof
  cheat
QED

(* Handle all result types *)
Theorem transform_inst_result_equiv:
  !lenv inst s.
    env_sound lenv s
  ==>
    result_equiv (step_inst inst s)
                 (step_inst (transform_inst lenv inst) s)
Proof
  cheat
QED

(* ==========================================================================
   Block-Level Correctness
   ========================================================================== *)

Theorem transform_block_result_equiv:
  !lenv fn bb s.
    env_sound lenv s
  ==>
    result_equiv (run_block fn bb s)
                 (run_block fn (transform_block lenv bb) s)
Proof
  cheat
QED

(* ==========================================================================
   Function-Level Correctness
   ========================================================================== *)

(* Main correctness theorem *)
Theorem sccp_correct:
  !lenv fn s fuel result.
    env_sound lenv s /\
    sccp_fixpoint lenv fn /\
    fn.fn_blocks <> [] /\
    run_function fuel fn s = result
  ==>
    ?result'.
      run_function fuel (transform_function lenv fn) s = result' /\
      result_equiv result result'
Proof
  cheat
QED

