Theory allocasBelowFmpUpdatesProps
Ancestors
  ptrDiscipline venomState

Theorem allocas_below_fmp_fields:
  t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp /\
  t.vs_fmp = s.vs_fmp ==>
  (allocas_below_fmp t <=> allocas_below_fmp s)
Proof
  strip_tac >> simp[allocas_below_fmp_def]
QED

(* Scratch updates leave the allocation table and both FMPs unchanged. *)
Theorem allocas_below_fmp_updates:
  (allocas_below_fmp (update_var x w s) <=> allocas_below_fmp s) /\
  (allocas_below_fmp (s with vs_inst_idx := k) <=> allocas_below_fmp s) /\
  (allocas_below_fmp (mstore addr v s) <=> allocas_below_fmp s) /\
  (allocas_below_fmp (s with vs_vars := vars) <=> allocas_below_fmp s) /\
  (allocas_below_fmp (s with vs_memory := mem) <=> allocas_below_fmp s) /\
  (allocas_below_fmp (s with <|vs_memory := mem; vs_vars := vars; vs_inst_idx := k|>) <=>
     allocas_below_fmp s)
Proof
  simp[update_var_def, mstore_def, allocas_below_fmp_def]
QED
