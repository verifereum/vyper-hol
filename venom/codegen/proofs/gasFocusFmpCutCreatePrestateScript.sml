(* Shared oracle fields at the creation pre-state. *)
Theory gasFocusFmpCutCreatePrestate
Ancestors
  fmpStageRel o1LowerDloadShared o1LowerDloadConcreteExternal
  ptrDiscipline venomCallOracleDefs venomState venomInst words list pred_set

Theorem focus_fmp_cut_create_prestate:
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_outcomes = t.vs_outcomes /\
  s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions
Proof
  strip_tac >> fs[fmp_stage_rel_def, fmp_frame_rel_def, ld_shared_agree_def]
QED
