Theory concretizePtrEventEmbedding
Ancestors concretizePtrOperationalBytes list rich_list arithmetic

(* Only pre-event sampling. No operational or memory agreement is a field. *)
Definition ptr_event_embedding_def:
  ptr_event_embedding (h:ptr_observation list) (ht:ptr_observation list) es <=>
    LENGTH es = LENGTH ht /\
    EVERY (\i. i < LENGTH h) es /\
    (!i j. i < j /\ j < LENGTH es ==> EL i es < EL j es)
End

Theorem ptr_event_embedding_take:
  ptr_event_embedding h ht es ==>
  ptr_event_embedding h (TAKE n ht) (TAKE n es)
Proof
  simp[ptr_event_embedding_def, LENGTH_TAKE_EQ] >> rpt strip_tac
  >- metis_tac[EVERY_TAKE] >>
  simp[EL_TAKE] >> first_x_assum irule >> decide_tac
QED

Theorem ptr_event_embedding_snoc:
  ptr_event_embedding h ht es /\
  q < LENGTH (h ++ gap) /\ EVERY (\i. i < q) es ==>
  ptr_event_embedding (h ++ gap) (ht ++ [b]) (es ++ [q])
Proof
  simp[ptr_event_embedding_def, EVERY_APPEND, EVERY_MEM] >> rpt strip_tac
  >- (first_x_assum drule >> simp[]) >>
  Cases_on `j < LENGTH es`
  >- (simp[EL_APPEND_EQN] >> first_x_assum irule >> simp[]) >>
  `j = LENGTH es` by decide_tac >> gvs[EL_APPEND_EQN] >>
  first_x_assum irule >> simp[EL_MEM]
QED

Theorem ptr_event_embedding_post_le:
  ptr_event_embedding h ht es /\ SUC j < LENGTH es ==>
  SUC (EL j es) <= EL (SUC j) es
Proof
  simp[ptr_event_embedding_def] >> rpt strip_tac >>
  `EL j es < EL (SUC j) es` by (first_x_assum irule >> simp[]) >>
  decide_tac
QED

Theorem ptr_event_embedding_gap_byte_frame:
  ptr_chrono_history vs0 ctx h a /\ ptr_event_embedding h ht es /\
  SUC j < LENGTH es /\
  (!k. SUC (EL j es) <= k /\ k < EL (SUC j) es ==>
    x NOTIN range_bytes
      (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state)) ==>
  read_byte x (EL (EL (SUC j) es) h).po_state.vs_memory =
    read_byte x (EL (SUC (EL j es)) h).po_state.vs_memory
Proof
  rpt strip_tac >> irule ptr_chrono_history_interval_byte_frame >>
  drule_all ptr_event_embedding_post_le >> strip_tac >>
  gvs[ptr_event_embedding_def, EVERY_EL] >> metis_tac[]
QED
