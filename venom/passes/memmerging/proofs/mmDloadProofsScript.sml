(* One selected block's DLOAD pairs, rewritten throughout the function. *)
Theory mmDloadProofs
Ancestors
  mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner
  venomWf stateEquiv

Theorem mm_dload_visit_correct:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\
  ir_supply_covers_fn supply fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  fn' = fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks ==>
  fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\
  ir_supply_covers_fn supply fn' /\
  fn_entry_label fn' = fn_entry_label fn /\
  (!fuel ctx eom s.
    fn_entry_state fn s /\ eom < dimword (:256) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn s) /\
    ~(?err. run_function fuel ctx fn s = Error err) ==>
    lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
      (run_function fuel ctx fn s) (run_function fuel ctx fn' s) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn' s))
Proof
  cheat
QED
