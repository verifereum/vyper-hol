Theory concretizePtrPairedPrefix
Ancestors
  concretizePtrStructuralTranscript concretizePtrSharedFields
  concretizePtrValueSelection concretizePtrEventEmbedding concretizePtrPairedFields
  list rich_list arithmetic pair

(* The tuple is the actual source snapshot, not an endpoint witness
   substituted retrospectively into an earlier observation. *)
Definition ptr_paired_sample_def:
  ptr_paired_sample positions a at
      (tokens,registry,births,PT,TG,saved,entries) <=>
    ptr_vars_transport births positions TG a.po_taint a.po_state at.po_state /\
    ptr_shared_fields a.po_state at.po_state
End

Definition ptr_paired_samples_def:
  ptr_paired_samples positions h ht done H <=>
    LENGTH H = LENGTH h /\ 0 < LENGTH h /\
    LENGTH ht = SUC (LENGTH done) /\
    EVERY (\n. n < LENGTH h) done /\
    (!j. j < LENGTH ht ==>
      ptr_paired_sample positions
        (EL (EL j (done ++ [LENGTH h - 1])) h) (EL j ht)
        (EL (EL j (done ++ [LENGTH h - 1])) H))
End

Theorem ptr_paired_samples_transport:
  ptr_paired_samples positions h ht done H /\ j < LENGTH ht /\
  EL (EL j (done ++ [LENGTH h - 1])) H =
    (tokens,registry,births,PT,TG,saved,entries) ==>
  ptr_vars_transport births positions TG
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_taint
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_state (EL j ht).po_state
Proof
  simp[ptr_paired_samples_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[ptr_paired_sample_def]
QED

Theorem ptr_paired_samples_shared:
  ptr_paired_samples positions h ht done H /\ j < LENGTH ht ==>
  ptr_shared_fields
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_state (EL j ht).po_state
Proof
  simp[ptr_paired_samples_def] >> rpt strip_tac >>
  first_x_assum drule >>
  qmatch_goalsub_abbrev_tac `ptr_paired_sample positions a at snapshot` >>
  PairCases_on `snapshot` >> simp[ptr_paired_sample_def]
QED

(* Departed samples do not move. The final sample does: it must be
   supplied by the eventual NOP-preservation proof, not by list algebra. *)
Theorem ptr_paired_samples_gap:
  ptr_paired_samples positions h ht done H /\
  ptr_paired_sample positions b (EL (LENGTH done) ht) snapshot ==>
  ptr_paired_samples positions (h ++ [b]) ht done (H ++ [snapshot])
Proof
  rewrite_tac[ptr_paired_samples_def] >> strip_tac >>
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
Theorem ptr_paired_samples_pair:
  ptr_paired_samples positions h ht done H /\
  ptr_paired_sample positions b bt snapshot ==>
  ptr_paired_samples positions (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1]) (H ++ [snapshot])
Proof
  rewrite_tac[ptr_paired_samples_def] >> strip_tac >>
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
  ptr_args_transport births positions PT
    (REPLICATE (LENGTH (EL (EL j (done ++ [LENGTH h - 1])) h).po_state.vs_params) {})
    (EL (EL j (done ++ [LENGTH h - 1])) h).po_state.vs_params
    (EL j ht).po_state.vs_params
Proof
  simp[ptr_paired_alignment_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[ptr_paired_params_def]
QED
