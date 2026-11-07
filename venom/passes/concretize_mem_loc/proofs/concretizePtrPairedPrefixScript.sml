Theory concretizePtrPairedPrefix
Ancestors
  concretizePtrStructuralTranscript concretizePtrStructuralTrace concretizePtrSharedFields
  concretizePtrValueSelection concretizePtrEventEmbedding concretizePtrPairedFields
  concretizePtrOpaqueRetpc
  concretizePtrChronologicalHistory concretizePtrActivationChronology concretizePtrActivationBirths
  list rich_list arithmetic pair

(* The tuple is the actual source snapshot, not an endpoint witness
   substituted retrospectively into an earlier observation. *)
Definition ptr_paired_sample_def:
  ptr_paired_sample positions a at
      (tokens,registry,births,PT,TG,saved,entries) <=>
    ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
      a.po_state at.po_state /\
    ptr_core_shared a.po_state at.po_state
End

Definition ptr_sample_list_def:
  ptr_sample_list P h ht done H <=>
    LENGTH H = LENGTH h /\ 0 < LENGTH h /\
    LENGTH ht = SUC (LENGTH done) /\
    EVERY (\n. n < LENGTH h) done /\
    (!j. j < LENGTH ht ==>
      P (EL (EL j (done ++ [LENGTH h - 1])) h) (EL j ht)
        (EL (EL j (done ++ [LENGTH h - 1])) H))
End

Definition ptr_paired_samples_def:
  ptr_paired_samples positions h ht done H <=>
    ptr_sample_list (ptr_paired_sample positions) h ht done H
End

Theorem ptr_sample_list_root:
  P a at snapshot ==> ptr_sample_list P [a] [at] [] [snapshot]
Proof
  simp[ptr_sample_list_def]
QED

Theorem ptr_paired_samples_mixed:
  ptr_paired_samples positions h ht done H /\ j < LENGTH ht /\
  EL (EL j (done ++ [LENGTH h - 1])) H =
    (tokens,registry,births,PT,TG,saved,entries) ==>
  ptr_mixed_vars births positions TG
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_taint
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_fn (EL j ht).po_fn
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_state (EL j ht).po_state
Proof
  simp[ptr_paired_samples_def, ptr_sample_list_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[ptr_paired_sample_def]
QED

Theorem ptr_paired_samples_core:
  ptr_paired_samples positions h ht done H /\ j < LENGTH ht ==>
  ptr_core_shared
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_state (EL j ht).po_state
Proof
  simp[ptr_paired_samples_def, ptr_sample_list_def] >> rpt strip_tac >>
  first_x_assum drule >>
  qmatch_goalsub_abbrev_tac `ptr_paired_sample positions a at snapshot` >>
  PairCases_on `snapshot` >> simp[ptr_paired_sample_def]
QED
(* Adjacent source poststates and normalized samples differ only by a NOP
   gap in the fields needed here; no cursor equality is asserted. *)
Theorem ptr_paired_samples_post_returndata:
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries /\
  ptr_paired_samples positions h ht done H /\ q < LENGTH done ==>
  (EL (SUC (EL q done)) h).po_state.vs_returndata =
    (EL (SUC q) ht).po_state.vs_returndata
Proof
  strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule_all ptr_paired_samples_core >>
  simp[ptr_core_shared_def, ptr_shared_fields_def] >> strip_tac >>
  drule ptr_structural_trace_gap_returndata >>
  disch_then (qspec_then `q` mp_tac) >> simp[]
QED

(* Operand transport is available only outside the opaque return-PC class. *)
Theorem ptr_paired_samples_eval_operands:
  ptr_paired_samples positions h ht done H /\ j < LENGTH ht /\
  EL (EL j (done ++ [LENGTH h - 1])) H =
    (tokens,registry,births,PT,TG,saved,entries) /\
  EVERY (ptr_nonopaque_operand
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_fn) ops ==>
  OPTREL (ptr_args_transport births positions
    (MAP (ptrDiscipline$op_prov TG) ops)
    (MAP (ptrDiscipline$op_taint
      (EL (EL j (done ++ [LENGTH h - 1])) h).po_taint) ops))
    (eval_operands ops (EL (EL j (done ++ [LENGTH h - 1])) h).po_state)
    (eval_operands ops (EL j ht).po_state)
Proof
  strip_tac >> drule_all ptr_paired_samples_mixed >> strip_tac >>
  drule_all ptr_paired_samples_core >> strip_tac >>
  irule ptr_mixed_vars_eval_operands >>
  rpt (goal_assum (drule_at Any)) >>
  fs[ptr_core_shared_def, concretizePtrSharedFieldsTheory.ptr_shared_fields_def] >>
  metis_tac[]
QED


(* Departed samples do not move. The final sample does: it must be
   supplied by the eventual NOP-preservation proof, not by list algebra. *)
Theorem ptr_sample_list_gap:
  ptr_sample_list P h ht done H /\
  P b (EL (LENGTH done) ht) snapshot ==>
  ptr_sample_list P (h ++ [b]) ht done (H ++ [snapshot])
Proof
  rewrite_tac[ptr_sample_list_def] >> strip_tac >>
  `EVERY (\n. n < LENGTH (h ++ [b])) done` by
    (gvs[EVERY_EL] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  simp[] >> rpt strip_tac >>
  Cases_on `j < LENGTH done`
  >- (`EL j done < LENGTH h` by gvs[EVERY_EL] >>
      `EL j done < LENGTH H` by simp[] >>
      first_x_assum (qspec_then `j` mp_tac) >>
      simp[EL_APPEND_EQN]) >>
  `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]
QED

(* A paired event freezes the former final sample and adds one new one.
   New-event semantic facts are inputs only to this structural probe. *)
Theorem ptr_sample_list_pair:
  ptr_sample_list P h ht done H /\
  P b bt snapshot ==>
  ptr_sample_list P (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1]) (H ++ [snapshot])
Proof
  rewrite_tac[ptr_sample_list_def] >> strip_tac >>
  `EVERY (\n. n < LENGTH (h ++ [b])) (done ++ [LENGTH h - 1])` by
    (simp[EVERY_APPEND, EVERY_EL] >> rpt strip_tac >>
     gvs[EVERY_EL] >> first_x_assum drule >> simp[]) >>
  simp[] >> rpt strip_tac >>
  Cases_on `j < LENGTH ht`
  >- (`EL j (done ++ [LENGTH h - 1]) < LENGTH h` by
        (Cases_on `j < LENGTH done`
         >- (simp[EL_APPEND_EQN] >> gvs[EVERY_EL]) >>
         `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]) >>
      `EL j (done ++ [LENGTH h - 1]) < LENGTH H` by simp[] >>
      first_x_assum (qspec_then `j` mp_tac) >>
      Cases_on `j < LENGTH done`
      >- (`EL j done < LENGTH h` by gvs[EVERY_EL] >>
          simp[EL_APPEND_EQN]) >>
      `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]) >>
  `j = LENGTH ht` by gvs[] >> simp[EL_APPEND_EQN, ADD1]
QED

Theorem ptr_paired_samples_gap:
  ptr_paired_samples positions h ht done H /\
  ptr_paired_sample positions b (EL (LENGTH done) ht) snapshot ==>
  ptr_paired_samples positions (h ++ [b]) ht done (H ++ [snapshot])
Proof
  rewrite_tac[ptr_paired_samples_def] >> strip_tac >> irule ptr_sample_list_gap >> simp[]
QED

Theorem ptr_paired_samples_pair:
  ptr_paired_samples positions h ht done H /\
  ptr_paired_sample positions b bt snapshot ==>
  ptr_paired_samples positions (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1]) (H ++ [snapshot])
Proof
  rewrite_tac[ptr_paired_samples_def] >> strip_tac >> irule ptr_sample_list_pair >> simp[]
QED

Definition ptr_paired_alignment_def:
  ptr_paired_alignment R local_positions positions h ht done H <=>
    !j. j < LENGTH ht ==>
      ptr_paired_code R local_positions positions
        (EL (EL j (done ++ [LENGTH h - 1])) h).po_fn (EL j ht).po_fn /\
      ptr_paired_cursor local_positions
        (EL (EL j (done ++ [LENGTH h - 1])) h) (EL j ht) /\
      ptr_paired_params positions
        (EL (EL j (done ++ [LENGTH h - 1])) h) (EL j ht)
        (EL (EL j (done ++ [LENGTH h - 1])) H)
End

Theorem ptr_paired_alignment_pair:
  ptr_paired_samples positions h ht done H /\
  ptr_paired_alignment R lp positions h ht done H /\
  ptr_paired_code R lp positions b.po_fn bt.po_fn /\
  ptr_paired_cursor lp b bt /\
  ptr_paired_params positions b bt snapshot ==>
  ptr_paired_alignment R lp positions (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1]) (H ++ [snapshot])
Proof
  rewrite_tac[ptr_paired_samples_def, ptr_sample_list_def, ptr_paired_alignment_def] >>
  strip_tac >> gen_tac >> strip_tac >> Cases_on `j < LENGTH ht`
  >- (`EL j (done ++ [LENGTH h - 1]) < LENGTH h` by
        (Cases_on `j < LENGTH done`
         >- (simp[EL_APPEND_EQN] >> gvs[EVERY_EL]) >>
         `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]) >>
      first_x_assum (qspec_then `j` mp_tac) >>
      Cases_on `j < LENGTH done`
      >- (`EL j done < LENGTH h` by gvs[EVERY_EL] >>
          simp[EL_APPEND_EQN]) >>
      `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]) >>
  `j = LENGTH ht` by gvs[] >> simp[EL_APPEND_EQN, ADD1]
QED

Definition ptr_paired_prefix_def:
  ptr_paired_prefix R local_positions positions lo vs0 C Ct
      h a ht at done tokens registry births PT TG saved entries H calls W <=>
    ptr_structural_transcript R vs0 C Ct h a ht at done
      tokens registry births PT TG saved entries H /\
    ptr_stage_placements Ct positions /\
    ptr_paired_samples positions h ht done H /\
    ptr_paired_alignment R local_positions positions h ht done H /\
    ptr_paired_callers h ht done H a at saved calls /\
    ptr_paired_writes lo positions C Ct h ht done H W
End

Theorem ptr_paired_prefix_transcript:
  !W.
  ptr_paired_prefix R local_positions positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W ==>
  ptr_structural_transcript R vs0 C Ct h a ht at done
    tokens registry births PT TG saved entries H
Proof
  simp[ptr_paired_prefix_def]
QED

Theorem ptr_paired_prefix_samples:
  !W.
  ptr_paired_prefix R local_positions positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W ==>
  ptr_paired_samples positions h ht done H
Proof
  simp[ptr_paired_prefix_def]
QED

Theorem ptr_paired_prefix_placements:
  !W.
  ptr_paired_prefix R local_positions positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W ==>
  ptr_stage_placements Ct positions
Proof
  simp[ptr_paired_prefix_def]
QED

Theorem ptr_paired_prefix_alignment:
  !W.
  ptr_paired_prefix R local_positions positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W /\
  j < LENGTH ht ==>
  ptr_paired_code R local_positions positions
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_fn (EL j ht).po_fn /\
  ptr_paired_cursor local_positions
    (EL (EL j (done ++ [LENGTH h - 1])) h) (EL j ht) /\
  ptr_paired_params positions
    (EL (EL j (done ++ [LENGTH h - 1])) h) (EL j ht)
    (EL (EL j (done ++ [LENGTH h - 1])) H)
Proof
  simp[ptr_paired_prefix_def, ptr_paired_alignment_def]
QED

Theorem ptr_paired_prefix_callers:
  !W.
  ptr_paired_prefix R local_positions positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W ==>
  ptr_paired_callers h ht done H a at saved calls
Proof
  simp[ptr_paired_prefix_def]
QED

Theorem ptr_paired_prefix_writes:
  !W.
  ptr_paired_prefix R local_positions positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W ==>
  ptr_paired_writes lo positions C Ct h ht done H W
Proof
  simp[ptr_paired_prefix_def]
QED

Theorem ptr_paired_alignment_params:
  ptr_paired_alignment R local_positions positions h ht done H /\
  j < LENGTH ht /\
  EL (EL j (done ++ [LENGTH h - 1])) H =
    (tokens,registry,births,PT,TG,saved,entries) ==>
  (PT = [] /\
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_state.vs_params =
    (EL j ht).po_state.vs_params) \/
  ptr_args_transport births positions PT
    (REPLICATE (LENGTH (EL (EL j (done ++ [LENGTH h - 1])) h).po_state.vs_params) {})
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_state.vs_params
    (EL j ht).po_state.vs_params
Proof
  simp[ptr_paired_alignment_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[ptr_paired_params_def]
QED

Theorem ptr_paired_alignment_gap:
  ptr_paired_samples positions h ht done H /\
  ptr_paired_alignment R local_positions positions h ht done H /\
  ptr_paired_code R local_positions positions b.po_fn (EL (LENGTH done) ht).po_fn /\
  ptr_paired_cursor local_positions b (EL (LENGTH done) ht) /\
  ptr_paired_params positions b (EL (LENGTH done) ht) snapshot ==>
  ptr_paired_alignment R local_positions positions (h ++ [b]) ht done (H ++ [snapshot])
Proof
  rewrite_tac[ptr_paired_samples_def, ptr_sample_list_def, ptr_paired_alignment_def] >>
  strip_tac >> gen_tac >> strip_tac >> Cases_on `j < LENGTH done`
  >- (`EL j done < LENGTH h /\ EL j done < LENGTH H` by gvs[EVERY_EL] >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[EL_APPEND_EQN]) >>
  `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]
QED

(* Semantic endpoint facts are separated from the frozen-history bookkeeping. *)
Theorem ptr_paired_prefix_gap:
  !W. ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W /\
  a.po_inst.inst_opcode = NOP /\
  ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved' /\
  b.po_stack = a.po_stack /\ saved' = saved /\
  ptr_paired_sample positions b at
    (ptr_activation_tokens h a b tokens,ptr_activation_registry h a b registry,
     ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births,
     PT',TG',saved',entries) /\
  ptr_paired_code R lp positions b.po_fn at.po_fn /\
  ptr_paired_cursor lp b at /\
  ptr_paired_params positions b at
    (ptr_activation_tokens h a b tokens,ptr_activation_registry h a b registry,
     ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births,
     PT',TG',saved',entries) ==>
  ptr_paired_prefix R lp positions lo vs0 C Ct
    (h ++ [b]) b ht at done
    (ptr_activation_tokens h a b tokens) (ptr_activation_registry h a b registry)
    (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births)
    PT' TG' saved' entries
    (H ++ [(ptr_activation_tokens h a b tokens,ptr_activation_registry h a b registry,
     ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births,
     PT',TG',saved',entries)]) calls W
Proof
  gen_tac >> rewrite_tac[ptr_paired_prefix_def] >> strip_tac >>
  qpat_x_assum `saved' = saved` SUBST_ALL_TAC >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `EL (LENGTH done) ht = at` by
    (gvs[ptr_paired_samples_def, ptr_sample_list_def] >>
     `PRE (LENGTH ht) = LENGTH done` by decide_tac >> gvs[LAST_EL]) >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (drule ptr_structural_trace_embedding >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  conj_tac >- (irule (cj 2 ptr_structural_transcript_rules) >> metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac >- (irule ptr_paired_samples_gap >> simp[]) >>
  conj_tac >- (irule ptr_paired_alignment_gap >> metis_tac[]) >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`ts` |-> `[]`, `ds` |-> `[]`]
        ptr_paired_callers_retained)) >>
      gvs[ptr_paired_samples_def, ptr_sample_list_def] >> qexistsl_tac [`a`,`LAST ht`] >> simp[]) >>
  irule ptr_paired_writes_gap >> gvs[ptr_paired_samples_def, ptr_sample_list_def]
QED

Theorem ptr_paired_prefix_endpoint:
  !W. ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls W ==>
  ptr_paired_sample positions a at (tokens,registry,births,PT,TG,saved,entries) /\
  ptr_paired_code R lp positions a.po_fn at.po_fn /\
  ptr_paired_cursor lp a at /\
  ptr_paired_params positions a at (tokens,registry,births,PT,TG,saved,entries)
Proof
  gen_tac >> rewrite_tac[ptr_paired_prefix_def] >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  imp_res_tac ptr_chrono_history_end >>
  `H <> []` by (Cases_on `H` >> gvs[]) >>
  qpat_x_assum `ptr_paired_samples _ _ _ _ _` mp_tac >>
  simp[ptr_paired_samples_def, ptr_sample_list_def] >> strip_tac >>
  `EL (LENGTH done) ht = at /\ EL (LENGTH h - 1) h = a /\
    EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (qpat_x_assum `LAST ht = at` mp_tac >>
     qpat_x_assum `LAST h = a` mp_tac >>
     qpat_x_assum `LAST H = _` mp_tac >>
     simp[LAST_EL, PRE_SUB1]) >>
  qpat_x_assum `!j. _ ==> ptr_paired_sample _ _ _ _`
    (qspec_then `LENGTH done` mp_tac) >>
  qpat_x_assum `ptr_paired_alignment _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_paired_alignment_def] >>
  disch_then (qspec_then `LENGTH done` mp_tac) >> simp[EL_APPEND_EQN]
QED
