(* Label-space boundaries for pending generated labels. *)
Theory bodyIntCallLabels
Ancestors
  compileEnv emitHelperProps pred_set list

Theorem label_external_reserved_transport:
  label_external st lbl /\
  st.cs_next_label <= st'.cs_next_label /\
  bound_labels st' SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label) ==>
  label_external st' lbl
Proof
  strip_tac >> drule compiler_labels_future_antimono >>
  gvs[label_external_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem label_external_pending_transport:
  st.cs_next_label <= st'.cs_next_label /\
  bound_labels st' SUBSET
    (bound_labels st UNION compiler_labels_future st.cs_next_label) /\
  EVERY (label_external st) pending ==>
  EVERY (label_external st') pending
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule label_external_reserved_transport >>
  goal_assum (drule_at Any) >> simp[]
QED
