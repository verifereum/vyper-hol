Theory algebraicOptProofs
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner

(* Algebraic optimization, with inserted instructions named from the
   supply, preserves the result of a run from the function's entry, up to
   the variables it takes from the supply, unless the original run fails. *)
Theorem ao_transform_function_correct_proof:
  !fuel ctx fn s sup fn' sup'.
    wf_ssa fn /\
    fn_inst_wf fn /\
    ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result
      (state_equiv (set sup'.irs_used_vars DIFF set sup.irs_used_vars))
      (execution_equiv (set sup'.irs_used_vars DIFF set sup.irs_used_vars))
      (execution_equiv (set sup'.irs_used_vars DIFF set sup.irs_used_vars))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)
Proof
  cheat
QED
