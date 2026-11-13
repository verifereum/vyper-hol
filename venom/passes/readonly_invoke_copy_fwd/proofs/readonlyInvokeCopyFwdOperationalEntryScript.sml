(* Actual PHI execution, rather than ghost-only entry reindexing. *)
Theory readonlyInvokeCopyFwdOperationalEntry
Ancestors
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdCalls readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdOperationalSupport contextCodegenRel
  ptrDiscipline taintAgree venomExecProofs venomExecSemantics venomState
  internalReturnCopyFwdSim finite_map list

Theorem ricf_frame_enters_block:
  ricf_frame_agree D X sites PG G0 tn0 s t /\
  enters_block fn s s1 ==>
  ?t1. enters_block fn t t1 /\
    ricf_frame_agree D X sites PG (entry_prov fn s G0)
      (entry_taint_vars fn s tn0) s1 t1
Proof
  strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by
    (drule ricf_frame_agree_normalized >>
     disch_then (mp_tac o MATCH_MP taint_agree_frame) >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_current_bb`) >> simp[]) >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  drule_all ricf_frame_agree_eval_phis >> strip_tac >>
  qexists_tac `t1 with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  conj_tac
  >- (simp[enters_block_def] >> metis_tac[]) >>
  gvs[entry_prov_def, entry_taint_vars_def] >>
  irule ricf_frame_inst_idx >> simp[]
QED

Theorem ricf_live_support_enters_block:
  ricf_frame_agree D X sites PG G0 tn0 s t /\
  enters_block fn s s1 /\
  ricf_live_stack_agree D ids tn0 maps stk targets s t /\
  ircf_cross tn0 cur s t /\ ricf_cert_crosses tn0 curs stk s t /\
  ricf_support_agree B E tn0 s t ==>
  ?t1. enters_block fn t t1 /\
    ricf_frame_agree D X sites PG (entry_prov fn s G0)
      (entry_taint_vars fn s tn0) s1 t1 /\
    ricf_live_stack_agree D ids (entry_taint_vars fn s tn0)
      maps stk targets s1 t1 /\
    ircf_cross (entry_taint_vars fn s tn0) cur s1 t1 /\
    ricf_cert_crosses (entry_taint_vars fn s tn0) curs stk s1 t1 /\
    ricf_support_agree B E (entry_taint_vars fn s tn0) s1 t1
Proof
  strip_tac >> drule_all ricf_frame_enters_block >> strip_tac >>
  qexists_tac `t1` >> simp[] >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  qpat_x_assum `enters_block fn t t1` mp_tac >>
  simp[enters_block_def] >> rpt strip_tac >>
  qpat_assum `eval_phis s _ = _`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >>
  qpat_assum `eval_phis t _ = _`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >>
  gvs[entry_taint_vars_def] >>
  rpt conj_tac
  >- (fs[ricf_live_stack_agree_def] >> gvs[merge_callee_state_def])
  >- (gvs[ircf_cross_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[])
  >> gvs[ricf_support_agree_def]
QED
