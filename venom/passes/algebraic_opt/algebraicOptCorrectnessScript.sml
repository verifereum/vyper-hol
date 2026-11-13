Theory algebraicOptCorrectness
Ancestors
  algebraicOptProofs algebraicOptWfProofs algebraicOptSsaProofs unitShapeDefs
  venomWf venomFnScheduleRunner

(* Algebraic optimization preserves function execution semantics: running
   a function from its entry before and after the transform gives
   equivalent results unless the original run fails.  Exits are
   compared on the frame only: the truthy-OR and comparator-flip
   rewrites change the values of variables whose only uses are truthy.  The transform names inserted
   instructions from the supply (ao_transform_function_supply). *)
Theorem ao_transform_function_correct:
  !fuel ctx fn s sup fn' sup'.
    wf_function fn /\
    wf_ssa fn /\
    fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
       lookup_var x s = NONE) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result
      (state_equiv (set sup'.irs_used_vars DIFF set sup.irs_used_vars))
      (execution_equiv UNIV)
      (execution_equiv UNIV)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)
Proof
  ACCEPT_TAC ao_transform_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem ao_preserves_ssa_form:
  !sup fn fn' sup'.
    wf_function fn /\
    ssa_form fn /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') ==>
    ssa_form fn'
Proof
  ACCEPT_TAC ao_preserves_ssa_form_proof
QED

Theorem ao_preserves_wf_function:
  !sup fn fn' sup'.
    wf_function fn /\
    fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') ==>
    wf_function fn'
Proof
  ACCEPT_TAC ao_preserves_wf_function_proof
QED
