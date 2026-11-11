Theory concretizePtrPairedNextAttach
Ancestors concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrEventEmbedding list

Theorem ptr_paired_prefix_nonwrite_attach:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_structural_transcript R vs C C' (h ++ [b]) b (ht ++ [bt]) bt
    (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) /\
  ptr_paired_sample positions b bt (tokens,registry,births,PT,TG',saved,entries) /\
  ptr_paired_code R lp positions b.po_fn bt.po_fn /\
  ptr_paired_cursor lp b bt /\
  ptr_paired_params positions b bt (tokens,registry,births,PT,TG',saved,entries) /\
  b.po_stack = a.po_stack /\ bt.po_stack = at.po_stack /\
  range_bytes (step_writes a.po_inst a.po_state b.po_state) = {} ==>
  ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [b]) b (ht ++ [bt]) bt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `LAST h = a` by metis_tac[ptr_chrono_history_end] >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_assum `ptr_structural_transcript _ _ _ _ (h ++ _) _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP ptr_structural_transcript_erasure) >>
     drule ptr_structural_trace_embedding >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def] >> decide_tac) >>
  fs[ptr_paired_prefix_def] >>
  conj_tac >- (irule ptr_paired_samples_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_alignment_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_callers_retained >> simp[] >>
               fs[ptr_paired_samples_def, ptr_sample_list_def] >> qexistsl_tac [`a`,`at`] >> simp[]) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM APPEND_NIL))) >>
  irule ptr_paired_writes_pair >> simp[] >> fs[ptr_paired_samples_def, ptr_sample_list_def]
QED
