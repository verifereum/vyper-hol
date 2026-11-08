Theory makeSsaCurrentEntryProvenance
Ancestors
  makeSsaCurrentWfSsa makeSsaCurrentSourceCuts makeSsaCurrentTreePaths
  makeSsaCurrentTreeTrace

Theorem current_event_source_cut_zero:
  current_event_trace A H ev ==>
  current_source_cut A ev 0 (current_event_entry_rs ev) (current_event_entry_env ev)
Proof
  PairCases_on `ev` >>
  simp[current_event_trace_def, current_source_cut_start,
    current_event_entry_rs_def, current_event_entry_env_def]
QED

Theorem current_wf_nondefault_entry_output:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_structural_certificate s fn fn' s' A H events /\
  (!dev k j. MEM dev events /\ k < LENGTH (A (current_event_label dev)) /\
    j < LENGTH (EL k (A (current_event_label dev))) ==>
    current_wf_output_at A H dev k
      (FST (EL j (EL k (A (current_event_label dev)))))) /\
  MEM ev events /\ current_event_trace A H ev /\
  current_event_entry_env ev v <> CurrentDefault v ==>
  ?dev k. MEM dev events /\
    current_wf_output_at A H dev k (current_event_entry_env ev v) /\
    current_event_label dev <> current_event_label ev /\
    fn_dominates fn (current_event_label dev) (current_event_label ev)
Proof
  strip_tac >>
  drule current_event_source_cut_zero >> strip_tac >>
  drule_all current_wf_nondefault_cut_output >> simp[]
QED

Theorem current_wf_phi_context_entry_named_output:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  MEM ev events /\ current_event_trace A H ev /\
  current_event_entry_env ev v <> CurrentDefault v /\
  current_token_name H (current_event_entry_env ev v) = SOME n ==>
  ?dev k bb. MEM dev events /\
    current_wf_output_at A H dev k (current_event_entry_env ev v) /\
    current_event_label dev <> current_event_label ev /\
    fn_dominates fn (current_event_label dev) (current_event_label ev) /\
    lookup_block (current_event_label dev) renamed = SOME bb /\
    bb.bb_label = current_event_label dev /\
    k < LENGTH bb.bb_instructions /\
    MEM n (EL k bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_structural >> strip_tac >>
  `!dev k j. MEM dev events /\ k < LENGTH (A (current_event_label dev)) /\
    j < LENGTH (EL k (A (current_event_label dev))) ==>
    current_wf_output_at A H dev k
      (FST (EL j (EL k (A (current_event_label dev)))))` by
    metis_tac[current_wf_precleanup_output_sites] >>
  drule_all current_wf_nondefault_entry_output >> strip_tac >>
  drule_all current_wf_precleanup_output >> strip_tac >>
  metis_tac[]
QED
