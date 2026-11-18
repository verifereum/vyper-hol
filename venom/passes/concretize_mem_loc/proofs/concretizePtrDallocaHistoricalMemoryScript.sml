Theory concretizePtrDallocaHistoricalMemory
Ancestors
  concretizePtrDallocaHistoricalDemand concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrEventEmbedding
  list rich_list arithmetic pair

(* No claim about historical saved callers is made here. The endpoint
   q is a recorded departure sample, so its sentinel denotes EL q done. *)
Theorem ptr_dalloca_memory_departure_cut:
  !W.
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H W /\
  q < LENGTH done /\ EL (EL q done) H = (ts,rw,bw,PTw,TGw,sw,ew) ==>
  ptr_paired_memory_prefix R lp positions lo vs C C'
    (TAKE (SUC (EL q done)) h) (EL (EL q done) h)
    (TAKE (SUC q) ht) (EL q ht) (TAKE q done)
    ts rw bw PTw TGw sw ew (TAKE (SUC (EL q done)) H)
    (FILTER (\(n,j,rho). j < q) W)
Proof
  gen_tac >> rewrite_tac[ptr_paired_memory_prefix_def] >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `!i j. i < j /\ j < LENGTH done ==> EL i done < EL j done` by
    (rpt strip_tac >>
     qpat_x_assum `ptr_event_embedding _ _ _` mp_tac >>
     simp[ptr_event_embedding_def] >> strip_tac >>
     first_x_assum (qspecl_then [`i`,`j`] mp_tac) >> simp[EL_APPEND_EQN]) >>
  `ptr_sample_list (\a t snapshot.
    ptr_paired_sample positions a t snapshot /\
    ptr_paired_code R lp positions a.po_fn t.po_fn /\
    ptr_paired_cursor lp a t /\ ptr_paired_params positions a t snapshot)
      h ht done H` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, ptr_paired_alignment_def] >>
  drule_all ptr_sample_list_departure_cut >> strip_tac >>
  drule_all ptr_dalloca_transcript_departure_cut >> strip_tac >>
  drule_all ptr_paired_writes_departure_cut >> strip_tac >>
  simp[] >>
  fs[ptr_paired_samples_def, ptr_sample_list_def, ptr_paired_alignment_def]
QED
