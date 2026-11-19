(* Agree on the world and creation request before consuming an outcome. *)
Theory gasFocusFmpCutCreatePrestate
Ancestors
  fmpStageRel o1LowerDloadShared o1LowerDloadConcreteExternal
  ptrDiscipline venomCallOracleDefs venomState venomInst words list pred_set

Theorem focus_fmp_cut_create_prestate:
  MEM inst.inst_opcode [CREATE; CREATE2] /\ taint_ok fn tn inst s /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  tn.t_stor = {} /\ tn.t_trans = {} /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_outcomes = t.vs_outcomes /\
  s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions /\
  (!value off off' sz salt.
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t ==>
    venom_create_request t value off' sz salt =
    venom_create_request s value off sz salt)
Proof
  strip_tac >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by
    (fs[taint_ok_def, MEM] >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  drule_all_then assume_tac ld_shared_clean_accounts >>
  drule_all_then assume_tac ld_shared_clean_transient >>
  fs[ld_shared_agree_def, venom_create_request_def]
QED
