Theory algebraicOptCorrectness
Ancestors
  algebraicOptProof venomWf

(* Algebraic optimization preserves function execution semantics.
   At function entry (vs_vars empty, as guaranteed by setup_callee),
   the original and transformed functions produce equivalent results
   modulo fresh/dead variables introduced by the transform. *)
Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    let fv' = ao_fn_total_fresh_vars fn in
    wf_function fn /\ wf_ssa fn /\ EVERY inst_wf (fn_insts fn) /\
    FDOM s.vs_vars = {} /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv fv') (execution_equiv fv') (execution_equiv fv')
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  ACCEPT_TAC algebraicOptProofTheory.ao_transform_function_correct
QED

(* ===== Structural Preservation ===== *)

Theorem ao_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (ao_transform_function fn)
Proof
  cheat
QED

Theorem ao_preserves_ssa_form:
  !fn. ssa_form fn ==> ssa_form (ao_transform_function fn)
Proof
  cheat
QED
