Theory externalReturnSourceWindow
Ancestors
  externalReturnNormalizeMem venomMemDefs

(* Protect only the live expression window, not its declared capacity. *)
Theorem expression_source_window_disjoint:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty sa sb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME p /\ cap <= val_footprint tv v /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\ sb.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (w2n p,cap) (b,sz)
Proof
  strip_tac >>
  Cases_on `cap = 0`
  >- simp[venomMemDefsTheory.regions_disjoint_def] >>
  `0 < val_footprint tv v` by decide_tac >>
  drule_all normalize_alloca_source_separate >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED
