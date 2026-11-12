(* The arbitrary frame Return has its own allocation-limit guard.
   This excludes the oversized candidate even when the packaged body has
   no valued Return. No global counterexample is asserted here. *)
Theory extRetCapacityFramePtr
Ancestors
  extRetCapacityAuditPtr bodyExprPreFacts bodyPtrDefs bodySim compileVyper words

Theorem frame_valued_return_capacity_bound:
  stmt_exprs_ok cenv (Return (SOME e)) /\
  cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
  cenv.ce_max_return_size < 2 ** 64
Proof
  simp[stmt_exprs_ok_def, stmt_valued_return_def, return_buffer_ok_def]
QED

Theorem same_frame_valued_return_capacity_bound:
  same_frame cenv c /\ stmt_exprs_ok c (Return (SOME e)) /\
  cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
  cenv.ce_max_return_size < 2 ** 64
Proof
  rpt strip_tac >>
  drule stmt_exprs_ok_same_frame >> strip_tac >>
  gvs[] >> drule_all frame_valued_return_capacity_bound >> simp[]
QED

Theorem huge_capacity_frame_return_excluded:
  cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
  ~stmt_exprs_ok (cenv with ce_max_return_size := dimword(:256))
     (Return (SOME e))
Proof
  simp[stmt_exprs_ok_def, stmt_valued_return_def,
       return_buffer_ok_def, dimword_def]
QED

(* Premise ledger for the rejected candidate:
   - same_frame: stmt_exprs_ok_same_frame transports the complete statement
     guard, including return_buffer_ok, not only expression allocation limits.
   - arbitrary Return SOME e: stmt_valued_return is true for every e. Hence
     external/non-raw frames require ce_max_return_size < 2**64 regardless
     of whether the actual packaged body contains a valued Return.
   - the dimword capacity candidate fails stmt_exprs_ok BEFORE type_stmt,
     expr_sim_inv, call_evaluation_safe or either expression simulation is
     considered. Small source types cannot repair that failure.
   - therefore there is no need (and no justification) to construct code,
     distinct IDs, stmt_state_rel, ghosts, gas_admissible or a counted trace
     for this candidate. ALLOCA 0w is not a reachable frame counterexample.
   - package/lowering success, source typing/storage/deployment, valid call,
     initial state/outcomes and source nonexemption remain uninstantiated;
     this file asserts neither a complete package witness nor global
     falsehood. Those outer premises cannot remove the inner exclusion.
   This probe closes only the oversized non-raw external-return objection.
   Raw returns and any normalizer allocation need their own interfaces. *)
