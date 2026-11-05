Theory concretizePtrStructuralTranscript
Ancestors
  concretizePtrStructuralTrace concretizePtrSourceOwnership
  concretizePtrEventEmbedding concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrChronologicalHistory
  finite_map list rich_list arithmetic

(* A snapshot retains the exact witnesses of one structural derivation. *)
Inductive ptr_structural_transcript:
[~root:]
  (!R vs0 C Ct a at.
    ptr_chrono_history vs0 C [a] a /\ a.po_stack = [] /\
    ptr_chrono_history vs0 Ct [at] at /\ at.po_stack = [] /\
    R a.po_fn at.po_fn ==>
    ptr_structural_transcript R vs0 C Ct [a] a [at] at [] [0]
      (FEMPTY |+ (0,a.po_fn)) (ptr_birth_lift 0 a.po_state.vs_allocas)
      [] FEMPTY [] (FEMPTY |+ (0,0))
      [([0], FEMPTY |+ (0,a.po_fn), ptr_birth_lift 0 a.po_state.vs_allocas,
        [], FEMPTY, [], FEMPTY |+ (0,0))])
[~gap:]
  (!R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H
      b PT' TG' saved'.
    ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H /\
    a.po_inst.inst_opcode = NOP /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved' ==>
    ptr_structural_transcript R vs0 C Ct (h ++ [b]) b ht at done
      (ptr_activation_tokens h a b tokens) (ptr_activation_registry h a b registry)
      (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births)
      PT' TG' saved' entries
      (H ++ [(ptr_activation_tokens h a b tokens, ptr_activation_registry h a b registry,
        ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births,
        PT', TG', saved', entries)]))
[~pair:]
  (!R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H
      b bt PT' TG' saved'.
    ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved' /\
    ptr_chrono_step Ct at bt /\
    a.po_inst.inst_id = at.po_inst.inst_id /\
    ((LENGTH b.po_stack = LENGTH a.po_stack /\ LENGTH bt.po_stack = LENGTH at.po_stack) \/
     (LENGTH b.po_stack = SUC (LENGTH a.po_stack) /\
      LENGTH bt.po_stack = SUC (LENGTH at.po_stack) /\ R b.po_fn bt.po_fn) \/
     (LENGTH a.po_stack = SUC (LENGTH b.po_stack) /\
      LENGTH at.po_stack = SUC (LENGTH bt.po_stack))) ==>
    ptr_structural_transcript R vs0 C Ct (h ++ [b]) b (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1])
      (ptr_activation_tokens h a b tokens) (ptr_activation_registry h a b registry)
      (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births)
      PT' TG' saved'
      (if LENGTH b.po_stack = SUC (LENGTH a.po_stack)
       then entries |+ (LENGTH h,LENGTH ht) else entries)
      (H ++ [(ptr_activation_tokens h a b tokens, ptr_activation_registry h a b registry,
        ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births,
        PT', TG', saved',
        if LENGTH b.po_stack = SUC (LENGTH a.po_stack)
        then entries |+ (LENGTH h,LENGTH ht) else entries)]))
End

Theorem ptr_structural_transcript_erasure:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H.
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H ==>
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries
Proof
  ho_match_mp_tac ptr_structural_transcript_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[ptr_structural_trace_rules]
QED

Theorem ptr_structural_trace_transcript:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  ?H. ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[ptr_structural_transcript_rules]
QED

Theorem ptr_structural_transcript_endpoint:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H.
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H ==>
  LENGTH H = LENGTH h /\ 0 < LENGTH H /\
  LAST H = (tokens,registry,births,PT,TG,saved,entries)
Proof
  ho_match_mp_tac ptr_structural_transcript_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> simp[]
QED

Definition ptr_snapshot_ownership_def:
  ptr_snapshot_ownership vs0 C h a (tokens,registry,births,PT,TG,saved,entries) <=>
    ptr_source_ownership vs0 C h a tokens registry births PT TG saved
End

Theorem ptr_structural_transcript_ownership:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H.
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H ==>
  !n. n < LENGTH h ==>
    ptr_snapshot_ownership vs0 C (TAKE (SUC n) h) (EL n h) (EL n H)
Proof
  ho_match_mp_tac ptr_structural_transcript_strongind >> rpt conj_tac
  >- (rpt strip_tac >> `n = 0` by gvs[] >>
      gvs[ptr_snapshot_ownership_def] >> metis_tac[ptr_source_ownership_rules]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  (Cases_on `n < LENGTH h`
  >- (drule ptr_structural_transcript_endpoint >> strip_tac >>
      `SUC n - LENGTH h = 0` by decide_tac >>
      simp[TAKE_APPEND, EL_APPEND_EQN]) >>
  `n = LENGTH h` by gvs[] >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  gvs[TAKE_LENGTH_TOO_LONG, EL_APPEND_EQN, ptr_snapshot_ownership_def] >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  metis_tac[ptr_source_ownership_rules])
QED

(* Source-indexed coherence: the transition and all source activation
   updates use the witnesses stored in the two adjacent snapshots. *)
Definition ptr_snapshot_step_def:
  ptr_snapshot_step C h a b
      (tokens,registry,births,PT,TG,saved,entries)
      (tokens',registry',births',PT',TG',saved',entries') <=>
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved' /\
    tokens' = ptr_activation_tokens h a b tokens /\
    registry' = ptr_activation_registry h a b registry /\
    births' = ptr_birth_overlay (HD tokens') b.po_state.vs_allocas births
End

Theorem ptr_structural_transcript_adjacent:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H.
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H ==>
  !n. SUC n < LENGTH h ==>
    ptr_snapshot_step C (TAKE (SUC n) h) (EL n h) (EL (SUC n) h)
      (EL n H) (EL (SUC n) H)
Proof
  ho_match_mp_tac ptr_structural_transcript_strongind >> rpt conj_tac
  >- (simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  (drule ptr_structural_transcript_endpoint >> strip_tac >>
   Cases_on `SUC n < LENGTH h`
   >- (`SUC n - LENGTH h = 0` by decide_tac >>
       simp[TAKE_APPEND, EL_APPEND_EQN]) >>
   `SUC n = LENGTH h /\ n < LENGTH h` by gvs[] >>
   drule ptr_structural_transcript_erasure >> strip_tac >>
   drule ptr_structural_trace_source >> strip_tac >>
   drule ptr_chrono_history_end >> strip_tac >>
   `EL n h = a /\ EL n H = (tokens,registry,births,PT,TG,saved,entries)` by
     (`H <> []` by (Cases_on `H` >> gvs[]) >>
      `n = PRE (LENGTH h)` by decide_tac >> gvs[LAST_EL]) >>
   simp[TAKE_APPEND, EL_APPEND_EQN, ptr_snapshot_step_def])
QED

(* Both constructors above append exactly one snapshot. Express retention
   using the source-history index, so consumers need no length conversion. *)
Theorem ptr_structural_transcript_append_prefix:
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H ==>
  TAKE (LENGTH h) (H ++ [snapshot]) = H /\
  EL (LENGTH h) (H ++ [snapshot]) = snapshot /\
  (!n. n < LENGTH h ==> EL n (H ++ [snapshot]) = EL n H)
Proof
  strip_tac >> drule ptr_structural_transcript_endpoint >> strip_tac >>
  simp[TAKE_APPEND, EL_APPEND_EQN]
QED

Theorem ptr_structural_transcript_sample_ownership:
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H /\
  j < LENGTH ht ==>
  ptr_snapshot_ownership vs0 C
    (TAKE (SUC (EL j (done ++ [LENGTH h - 1]))) h)
    (EL (EL j (done ++ [LENGTH h - 1])) h)
    (EL (EL j (done ++ [LENGTH h - 1])) H)
Proof
  strip_tac >> drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `EL j (done ++ [LENGTH h - 1]) < LENGTH h` by
    (gvs[ptr_event_embedding_def, EVERY_EL] >> Cases_on `j < LENGTH done`
     >- (simp[EL_APPEND_EQN] >> first_x_assum irule >> simp[]) >>
     `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]) >>
  drule ptr_structural_transcript_ownership >> simp[]
QED
