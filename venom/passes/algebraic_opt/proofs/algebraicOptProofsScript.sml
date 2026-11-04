Theory algebraicOptProofs
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner unitShapeDefs

(* Algebraic optimization, with inserted instructions named from the
   supply, preserves the result of a run from the function's entry, up to
   the variables it takes from the supply, unless the original run fails. *)
Theorem ao_transform_function_correct_proof:
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
  cheat
QED
