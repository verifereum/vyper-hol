(* Checked obstruction to unconditional label-erasure transport. *)
Theory bodyIntCallLabelEraseProbe
Ancestors
  exprLoweringProps compileEnv finite_map

Theorem ctor_immutable_base_erasure_impossible:
  ce.ce_is_ctor ==> ~immutable_base_zero ce (s with vs_labels := FEMPTY)
Proof
  simp[immutable_base_zero_def]
QED

Theorem erased_stmt_state_rel_nonconstructor:
  stmt_state_rel ctx func ce cx es (s with vs_labels := FEMPTY) ==>
  ~ce.ce_is_ctor
Proof
  simp[stmt_state_rel_def] >>
  metis_tac[ctor_immutable_base_erasure_impossible]
QED
