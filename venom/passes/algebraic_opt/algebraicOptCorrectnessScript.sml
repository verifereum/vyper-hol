Theory algebraicOptCorrectness
Ancestors
  algebraicOptProof aoPreservation algebraicOptDefs venomWf
  venomInst dfgSoundStep

(* Algebraic optimization preserves function execution semantics.
   At function entry (vs_vars empty, as guaranteed by setup_callee),
   the original and transformed functions produce equivalent results
   modulo fresh/dead variables introduced by the transform.

   ao_fresh_names_disjoint fn requires that the input program's outputs do
   not already collide with the ao_<id>_<suffix> namespace the pass inserts
   (mirrors mem2var's m2v_fresh_names_disjoint).

   dfg_block_local fn and the JNZ-distinct-labels condition are non-derivable
   preconditions introduced by the eval_phis block-entry semantics (mirrors
   overflow_elim_function_correct); see algebraicOptProof. *)
Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    let fv' = ao_fn_total_fresh_vars fn in
    wf_function fn /\ wf_ssa fn /\ EVERY inst_wf (fn_insts fn) /\
    ao_fresh_names_disjoint fn /\ dfg_block_local fn /\
    (!b cond true_lbl false_lbl. MEM b fn.fn_blocks /\
       (LAST b.bb_instructions).inst_opcode = JNZ /\
       (LAST b.bb_instructions).inst_operands =
         [cond; Label true_lbl; Label false_lbl] ==>
       true_lbl <> false_lbl) /\
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
