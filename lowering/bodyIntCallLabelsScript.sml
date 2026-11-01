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

Theorem fresh_labels_reverse_binding:
  fresh_label suffix1 st = (lbl1,st1) /\
  fresh_label suffix2 st1 = (lbl2,st2) /\
  new_block lbl2 st2 = (old2,st3) /\
  new_block lbl1 st3 = (old1,st4) /\
  compile_state_ok st ==>
  compile_state_ok st3 /\ label_external st3 lbl1 /\ compile_state_ok st4
Proof
  strip_tac >> drule_all fresh_label_produces_external >> strip_tac >>
  qpat_assum `fresh_label suffix2 _ = _`
    (mp_then Any mp_tac fresh_label_produces_external) >>
  simp[] >> strip_tac >>
  `label_external st2 lbl1` by
    (irule label_external_reserved_transport >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  `lbl1 <> lbl2` by
    (gvs[] >> metis_tac[fresh_label_output_inj, DECIDE ``n <> n + 1``]) >>
  `label_external st3 lbl1` by
    (gvs[label_external_def]) >>
  drule_all compile_state_ok_new_block >> strip_tac >> gvs[]
QED
