(* Chosen source histories and a monotone, live certificate subset. *)
Theory readonlyInvokeCopyFwdExecutionHistory
Ancestors
  readonlyInvokeCopyFwdLiveCertificates readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdAlignedOrigins readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistorySelected
  readonlyInvokeCopyFwdHistoryInheritedLifecycle
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs finite_map list pred_set

Definition ricf_chosen_ledger_def:
  ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history <=>
    EVERY (\entry.
      ricf_phase_entry vs C
        (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
          (readonly_mem_analyze C) (FST entry).rpe_fn)
        (log_of (FST entry).rpe_fn) stk PG G tn fn s a U B entry) history
End

Definition ricf_chosen_support_def:
  ricf_chosen_support vs C log_of a fn B E <=>
    !id. id IN E /\ FST id = a ==>
      ?p stk0 PG0 G0 tn0.
        p.rpe_dst = id /\ p.rpe_owner = a /\ p.rpe_fn = fn /\ 0 < p.rpe_size /\
        FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
        FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
        ricf_history_origin vs C
          (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
            (readonly_mem_analyze C) fn) (log_of fn) p stk0 PG0 G0 tn0
End

Definition ricf_certificate_live_def:
  ricf_certificate_live s certificates <=>
    EVERY (\entry. ricf_remaining_selected_use (FST entry)
      (ricf_visit_owner_state (SND entry) s)) certificates
End

(* The existing aligned-origin witness retains the exact owner-call anchor,
   both readonly endpoint histories and the actual source cursor. *)
Definition ricf_certificate_readonly_def:
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates <=>
    !p frames. MEM (p,frames) certificates /\ frames <> [] ==>
      ?inner anchor tail atn.
        frames = inner ++ [anchor] /\
        ricf_aligned_origin_at vs C
          (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
            (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
          stk PG G tn fn inst s U B
          (p.rpe_db,p.rpe_size) (p.rpe_db,p.rpe_sb,p.rpe_size)
          p inner anchor tail atn
End

Definition ricf_history_certificates_def:
  ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B
      history certificates <=>
    ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history /\
    ricf_certificate_coverage s history certificates /\
    ricf_certificate_live s certificates /\
    ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates
End

Theorem ricf_history_certificates_empty[simp]:
  ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B [] []
Proof
  simp[ricf_history_certificates_def, ricf_chosen_ledger_def,
    ricf_certificate_live_def, ricf_certificate_readonly_def]
QED

Theorem ricf_chosen_support_empty[simp]:
  ricf_chosen_support vs C log_of a fn B {}
Proof
  simp[ricf_chosen_support_def]
QED

Theorem ricf_chosen_ledger_analyzed:
  ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history ==>
  ricf_analyzed_ledger vs C stk PG G tn fn s a U B history
Proof
  simp[ricf_chosen_ledger_def, ricf_analyzed_ledger_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [
    `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) (FST entry).rpe_fn`,
    `log_of (FST entry).rpe_fn`] >> simp[icf_build_ctx_def]
QED

Theorem ricf_chosen_ledger_subset:
  ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B history /\
  set certificates SUBSET set history ==>
  ricf_chosen_ledger vs C log_of stk PG G tn fn s a U B certificates
Proof
  simp[ricf_chosen_ledger_def, EVERY_MEM, SUBSET_DEF] >> metis_tac[]
QED

Theorem ricf_history_certificates_analyzed:
  ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B
    history certificates ==>
  ricf_analyzed_ledger vs C stk PG G tn fn s a U B certificates
Proof
  simp[ricf_history_certificates_def, ricf_certificate_coverage_def] >>
  metis_tac[ricf_chosen_ledger_subset, ricf_chosen_ledger_analyzed]
QED

Theorem ricf_certificate_readonly_inherited:
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
  MEM (p,frames) certificates /\ frames <> [] ==>
  ricf_history_inherited vs C
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
    p stk PG G tn fn inst s
Proof
  simp[ricf_certificate_readonly_def] >> strip_tac >>
  first_x_assum (qspecl_then [`p`,`frames`] mp_tac) >> simp[] >> strip_tac >>
  simp[ricf_history_inherited_def] >>
  qexistsl_tac [`anchor`,`tail`,`inner`,`atn`] >>
  fs[ricf_aligned_origin_at_def]
QED
