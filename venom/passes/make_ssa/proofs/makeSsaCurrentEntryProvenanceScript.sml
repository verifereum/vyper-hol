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
