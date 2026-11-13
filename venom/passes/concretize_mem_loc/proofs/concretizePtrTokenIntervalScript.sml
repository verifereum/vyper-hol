Theory concretizePtrTokenInterval
Ancestors
  concretizePtrStructuralTranscript concretizePtrActivationChronology
  concretizePtrActivationBirths concretizePtrSourceOwnership
  list rich_list arithmetic

Theorem ptr_bottom_token_step[local]:
  ptr_chrono_step C a b /\ LENGTH tokens = SUC (LENGTH a.po_stack) /\
  d <= LENGTH a.po_stack /\ d <= LENGTH b.po_stack ==>
  EL (LENGTH b.po_stack - d) (ptr_activation_tokens h a b tokens) =
  EL (LENGTH a.po_stack - d) tokens
Proof
  strip_tac >> drule ptr_activation_step_lengths >> strip_tac
  >- simp[ptr_activation_tokens_def] 
  >- (`SUC (LENGTH a.po_stack) - d = SUC (LENGTH a.po_stack - d)` by decide_tac >>
      simp[ptr_activation_tokens_def]) >>
  `LENGTH a.po_stack - d = SUC (LENGTH b.po_stack - d)` by decide_tac >>
  Cases_on `tokens` >> gvs[ptr_activation_tokens_def]
QED

Theorem ptr_transcript_token_length[local]:
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births
    PT TG saved entries H /\ n < LENGTH h ==>
  LENGTH (FST (EL n H)) = SUC (LENGTH (EL n h).po_stack)
Proof
  strip_tac >> drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >>
  qabbrev_tac `snap = EL n H` >> PairCases_on `snap` >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> simp[]
QED

Theorem ptr_transcript_bottom_token_adjacent[local]:
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births
    PT TG saved entries H /\ SUC n < LENGTH h /\
  d <= LENGTH (EL n h).po_stack /\ d <= LENGTH (EL (SUC n) h).po_stack ==>
  EL (LENGTH (EL n h).po_stack - d) (FST (EL n H)) =
  EL (LENGTH (EL (SUC n) h).po_stack - d) (FST (EL (SUC n) H))
Proof
  strip_tac >>
  `LENGTH (FST (EL n H)) = SUC (LENGTH (EL n h).po_stack)` by
    (irule ptr_transcript_token_length >>
     `n < LENGTH h` by decide_tac >> metis_tac[]) >>
  drule ptr_structural_transcript_adjacent >> disch_then (qspec_then `n` mp_tac) >>
  simp[] >> qabbrev_tac `snap = EL n H` >>
  qabbrev_tac `snap' = EL (SUC n) H` >>
  PairCases_on `snap` >> PairCases_on `snap'` >>
  simp[ptr_snapshot_step_def] >> strip_tac >> gvs[] >>
  drule ptr_tagged_chrono_step_projection >> strip_tac >>
  sym_tac >> irule ptr_bottom_token_step >> metis_tac[]
QED

Theorem ptr_index_interval[local]:
  !j i f:num->num. i <= j /\
    (!n. i <= n /\ n < j ==> f n = f (SUC n)) ==>
    !k. i <= k /\ k <= j ==> f k = f j
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (rpt strip_tac >> `k = 0` by decide_tac >> simp[]) >>
  rpt strip_tac >> Cases_on `k = SUC j` >- simp[] >>
  `i <= j /\ k <= j` by decide_tac >>
  `f k = f j` by
    (first_x_assum (qspecl_then [`i`,`f`] mp_tac) >>
     (impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac)) >>
     disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  `f j = f (SUC j)` by (first_x_assum irule >> simp[]) >> simp[]
QED

Theorem ptr_transcript_bottom_token_interval:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H
   i j d tsj rj bj PTj TGj sj ej token.
  ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births
    PT TG saved entries H /\
  i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  EL (LENGTH (EL j h).po_stack - d) tsj = token ==>
  !k. i <= k /\ k <= j ==>
  ?tsk rk bk PTk TGk sk ek.
    EL k H = (tsk,rk,bk,PTk,TGk,sk,ek) /\
    EL (LENGTH (EL k h).po_stack - d) tsk = token
Proof
  rpt gen_tac >> strip_tac >>
  `!k. i <= k /\ k <= j ==>
    EL (LENGTH (EL k h).po_stack - d) (FST (EL k H)) =
    EL (LENGTH (EL j h).po_stack - d) (FST (EL j H))` by
    (ho_match_mp_tac ptr_index_interval >> simp[] >> rpt strip_tac >>
     `SUC n < LENGTH h` by decide_tac >>
     `d <= LENGTH (EL n h).po_stack` by (first_x_assum irule >> decide_tac) >>
     `d <= LENGTH (EL (SUC n) h).po_stack` by (first_x_assum irule >> decide_tac) >>
     irule ptr_transcript_bottom_token_adjacent >> simp[] >>
     goal_assum (drule_at Any)) >>
  rpt strip_tac >> qabbrev_tac `snap = EL k H` >>
  PairCases_on `snap` >> gvs[] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED
