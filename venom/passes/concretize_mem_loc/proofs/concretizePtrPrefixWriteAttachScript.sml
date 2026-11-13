(* Attaching one paired step that writes at most one ledger entry to a
   paired prefix, shared by the per-opcode family proofs. *)
Theory concretizePtrPrefixWriteAttach
Ancestors
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrEventEmbedding
  ptrDiscipline venomInst list

Theorem ptr_paired_prefix_write_attach:
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
  (extra = [] \/ ?rho. extra = [(LENGTH h - 1,LENGTH done,rho)]) /\
  EVERY (ptr_paired_write lo positions C C' (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)])) extra /\
  (~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
   range_bytes (step_writes a.po_inst a.po_state b.po_state) <> {} ==>
   ?rho. MEM (LENGTH h - 1,LENGTH done,rho) extra) ==>
  ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [b]) b (ht ++ [bt]) bt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls (ws ++ extra)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `LAST h = a` by metis_tac[ptr_chrono_history_end] >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_assum `ptr_structural_transcript _ _ _ _ (h ++ _) _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP ptr_structural_transcript_erasure) >>
     drule ptr_structural_trace_embedding >>
     simp[concretizePtrEventEmbeddingTheory.ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def] >> decide_tac) >>
  gns[ptr_paired_prefix_def] >>
  conj_tac >- (irule ptr_paired_samples_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_alignment_pair >> simp[]) >>
  conj_tac >- (irule concretizePtrPairedFieldsTheory.ptr_paired_callers_retained >> simp[] >>
               fs[ptr_paired_samples_def, ptr_sample_list_def] >> qexistsl_tac [`a`,`at`] >> simp[]) >>
  irule concretizePtrPairedFieldsTheory.ptr_paired_writes_pair >> simp[] >>
  fs[ptr_paired_samples_def, ptr_sample_list_def]
QED
