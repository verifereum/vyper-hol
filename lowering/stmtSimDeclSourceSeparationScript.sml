(* Expression provenance excludes allocation sites outside its code interval. *)
Theory stmtSimDeclSourceSeparation
Ancestors
  externalReturnNormalizeMem loweringPosts exprLoweringProps
  abiCallerAllocation exprSimOperands localPtrsProps finite_map

Theorem expr_val_at_alloca_outside_interval_separate:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty sa sb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  0 < val_footprint tv v /\ eval_operand src s = SOME p /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  (inst.inst_id < sa.cs_next_id \/ sb.cs_next_id <= inst.inst_id) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  w2n p + val_footprint tv v <= b \/ b + sz <= w2n p
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gnvs[]
  >- (`alloca_inv s` by fs[stmt_state_rel_def] >>
      `aid <> inst.inst_id` by decide_tac >>
      drule_all abi_caller_allocation_separate >> decide_tac) >>
  drule_all alloca_clear_of_locals >> decide_tac
QED
