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

(* Source-indexed induction retains every earlier frontier, including the
   observations skipped between two departed target events. *)
Theorem ptr_event_embedding_source_induction:
  ptr_event_embedding h ht (done ++ [LENGTH h - 1]) /\
  P 0 0 /\
  (!n q. SUC n < LENGTH h /\ q <= LENGTH done /\
    (q = 0 \/ EL (q-1) done < n) /\
    n <= EL q (done ++ [LENGTH h - 1]) /\
    (!j r. j <= n /\ r <= LENGTH done /\
      (r = 0 \/ EL (r-1) done < j) /\
      j <= EL r (done ++ [LENGTH h - 1]) ==> P j r) ==>
    ((q < LENGTH done /\ EL q done = n ==> P (SUC n) (SUC q)) /\
     ((q = LENGTH done \/ n < EL q done) ==> P (SUC n) q))) ==>
  !n q. n < LENGTH h /\ q <= LENGTH done /\
    (q = 0 \/ EL (q-1) done < n) /\
    n <= EL q (done ++ [LENGTH h - 1]) ==> P n q
Proof
  strip_tac >> completeInduct_on `n` >> gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `n = 0`
  >- (`q = 0` by (gvs[] >> decide_tac) >> gvs[]) >>
  `?m. n = SUC m` by (qexists `n-1` >> decide_tac) >>
  pop_assum strip_assume_tac >>
  `!j r. j <= m /\ r <= LENGTH done /\
    (r = 0 \/ EL (r-1) done < j) /\
    j <= EL r (done ++ [LENGTH h - 1]) ==> P j r` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  Cases_on `0 < q /\ EL (q-1) done = m`
  >- (`q-1 < LENGTH done /\ q-1 <= LENGTH done` by decide_tac >>
      `q-1 = 0 \/ EL (q-1-1) done < m` by
        (Cases_on `q-1 = 0` >> simp[] >>
         `EL (q-1-1) (done ++ [LENGTH h - 1]) <
          EL (q-1) (done ++ [LENGTH h - 1])` by
           (fs[ptr_event_embedding_def] >> first_x_assum irule >>
            simp[] >> decide_tac) >>
         `q-1-1 < LENGTH done` by decide_tac >>
         qpat_x_assum `EL (q-1-1) (done ++ [LENGTH h - 1]) < _` mp_tac >>
         simp[EL_APPEND_EQN] >> decide_tac) >>
      `m <= EL (q-1) (done ++ [LENGTH h - 1])` by simp[EL_APPEND_EQN] >>
      qpat_x_assum `!n q. SUC n < LENGTH h /\ _ ==> _`
        (qspecl_then [`m`,`q-1`] mp_tac) >>
      (impl_tac >-
        (rpt conj_tac >- decide_tac >- decide_tac >- decide_tac >- decide_tac >>
         first_assum ACCEPT_TAC)) >> strip_tac >>
      `SUC (q-1) = q` by decide_tac >> metis_tac[]) >>
  `q = 0 \/ EL (q-1) done < m` by decide_tac >>
  `m <= EL q (done ++ [LENGTH h - 1])` by decide_tac >>
  `q = LENGTH done \/ m < EL q done` by
    (Cases_on `q = LENGTH done` >> simp[] >>
     `q < LENGTH done` by decide_tac >>
     qpat_x_assum `n <= EL q (done ++ [LENGTH h - 1])` mp_tac >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  qpat_x_assum `!n q. SUC n < LENGTH h /\ _ ==> _`
    (qspecl_then [`m`,`q`] mp_tac) >>
  (impl_tac >-
    (rpt conj_tac >- decide_tac >- decide_tac >- decide_tac >- decide_tac >>
     first_assum ACCEPT_TAC)) >> metis_tac[]
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
