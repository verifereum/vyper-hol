Theory algebraicOptCorrectness
Ancestors
  algebraicOptProof aoPreservation algebraicOptDefs venomWf

(* Algebraic optimization preserves function execution semantics.
   At function entry (vs_vars empty, as guaranteed by setup_callee),
   the original and transformed functions produce equivalent results
   modulo fresh/dead variables introduced by the transform.

   ao_fresh_names_disjoint fn requires that the input program's outputs do
   not already collide with the ao_<id>_<suffix> namespace the pass inserts
   (mirrors mem2var's m2v_fresh_names_disjoint). *)
Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    let fv' = ao_fn_total_fresh_vars fn in
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    ao_fresh_names_disjoint fn /\
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
  !fn. wf_function fn /\ EVERY inst_wf (fn_insts fn) ==>
    wf_function (ao_transform_function fn)
Proof
  ACCEPT_TAC aoPreservationTheory.ao_preserves_wf_function
QED

Theorem ao_preserves_ssa_form:
  !fn. ssa_form fn /\ wf_function fn /\ ao_fresh_names_disjoint fn ==>
    ssa_form (ao_transform_function fn)
Proof
  rpt strip_tac >> fs[ao_fresh_names_disjoint_def] >>
  irule aoPreservationTheory.ao_preserves_ssa_form >> metis_tac[]
QED
