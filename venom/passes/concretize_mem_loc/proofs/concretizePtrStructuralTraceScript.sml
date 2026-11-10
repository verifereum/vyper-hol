Theory concretizePtrStructuralTrace
Ancestors
  concretizePtrEventEmbedding concretizePtrSourceOwnership
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrOwnerPath concretizePtrChronologicalHistory
  venomExecSemantics venomInst opcodeClass
  finite_map list rich_list arithmetic

(* done commits only departed target observations.  The current source
   sample moves across NOP gaps; activation entry indices do not. *)
Inductive ptr_structural_trace:
[~root:]
  (!R vs0 C Ct a at.
    ptr_chrono_history vs0 C [a] a /\ a.po_stack = [] /\
    ptr_chrono_history vs0 Ct [at] at /\ at.po_stack = [] /\
    R a.po_fn at.po_fn ==>
    ptr_structural_trace R vs0 C Ct [a] a [at] at [] [0]
      (FEMPTY |+ (0,a.po_fn)) (ptr_birth_lift 0 a.po_state.vs_allocas)
      [] FEMPTY [] (FEMPTY |+ (0,0)))
[~gap:]
  (!R vs0 C Ct h a ht at done tokens registry births PT TG saved entries
      b PT' TG' saved'.
    ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries /\
    a.po_inst.inst_opcode = NOP /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved' ==>
    ptr_structural_trace R vs0 C Ct (h ++ [b]) b ht at done
      (ptr_activation_tokens h a b tokens) (ptr_activation_registry h a b registry)
      (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births)
      PT' TG' saved' entries)
[~pair:]
  (!R vs0 C Ct h a ht at done tokens registry births PT TG saved entries
      b bt PT' TG' saved'.
    ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved' /\
    ptr_chrono_step Ct at bt /\
    a.po_inst.inst_id = at.po_inst.inst_id /\
    ((LENGTH b.po_stack = LENGTH a.po_stack /\ LENGTH bt.po_stack = LENGTH at.po_stack) \/
     (LENGTH b.po_stack = SUC (LENGTH a.po_stack) /\
      LENGTH bt.po_stack = SUC (LENGTH at.po_stack) /\ R b.po_fn bt.po_fn) \/
     (LENGTH a.po_stack = SUC (LENGTH b.po_stack) /\
      LENGTH at.po_stack = SUC (LENGTH bt.po_stack))) ==>
    ptr_structural_trace R vs0 C Ct (h ++ [b]) b (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1])
      (ptr_activation_tokens h a b tokens) (ptr_activation_registry h a b registry)
      (ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens)) b.po_state.vs_allocas births)
      PT' TG' saved'
      (if LENGTH b.po_stack = SUC (LENGTH a.po_stack)
       then entries |+ (LENGTH h,LENGTH ht) else entries))
End

Theorem ptr_structural_trace_source:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  ptr_chrono_history vs0 C h a
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[ptr_tagged_chrono_step_projection, ptr_chrono_history_rules]
QED

Theorem ptr_structural_trace_target:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  ptr_chrono_history vs0 Ct ht at
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[ptr_chrono_history_rules]
QED

Theorem ptr_structural_trace_ownership:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[ptr_source_ownership_rules]
QED

Theorem ptr_chrono_nop_stack[local]:
  !C a b. ptr_chrono_step C a b ==> a.po_inst.inst_opcode = NOP ==>
  b.po_stack = a.po_stack
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> simp[ptr_observe_def] >>
  rpt strip_tac >> gvs[is_terminator_def, step_inst_non_invoke, step_inst_base_def]
QED

Theorem ptr_structural_trace_samples[local]:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  0 < LENGTH h /\ LENGTH done + 1 = LENGTH ht /\
  EVERY (\i. i < LENGTH h - 1) done /\
  (!i j. i < j /\ j < LENGTH done ==> EL i done < EL j done)
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- simp[]
  >- (simp[EVERY_MEM] >> gvs[EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum `!i. MEM i done ==> _` drule >> decide_tac) >>
  (simp[EVERY_APPEND] >> conj_tac
   >- (gvs[EVERY_MEM] >> rpt strip_tac >> qpat_x_assum `!i. MEM i done ==> _` drule >> decide_tac) >>
   rpt strip_tac >> Cases_on `j < LENGTH done`
   >- (simp[EL_APPEND_EQN] >> first_x_assum irule >> simp[]) >>
   `j = LENGTH done` by decide_tac >> gvs[EL_APPEND_EQN, EVERY_EL] >>
   first_x_assum irule >> decide_tac)
QED

Theorem ptr_structural_trace_embedding:
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  LENGTH done + 1 = LENGTH ht /\ ptr_event_embedding h ht (done ++ [LENGTH h - 1])
Proof
  strip_tac >> drule ptr_structural_trace_samples >> strip_tac >>
  simp[ptr_event_embedding_def, EVERY_APPEND] >> conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> qpat_x_assum `!i. MEM i done ==> _` drule >> decide_tac) >>
  rpt strip_tac >> Cases_on `j < LENGTH done`
  >- (simp[EL_APPEND_EQN] >> first_x_assum irule >> simp[]) >>
  `j = LENGTH done` by decide_tac >> gvs[EL_APPEND_EQN, EVERY_EL] >>
  first_x_assum irule >> decide_tac
QED

Theorem ptr_paired_owner_step[local]:
  ptr_chrono_step C a b /\ ptr_chrono_step Ct at bt /\
  LENGTH a.po_stack = LENGTH at.po_stack /\
  (!d. d <= LENGTH a.po_stack ==>
    R (ptr_owner_view d a).cf_fn (ptr_owner_view d at).cf_fn) /\
  ((LENGTH b.po_stack = LENGTH a.po_stack /\ LENGTH bt.po_stack = LENGTH at.po_stack) \/
   (LENGTH b.po_stack = SUC (LENGTH a.po_stack) /\
    LENGTH bt.po_stack = SUC (LENGTH at.po_stack) /\ R b.po_fn bt.po_fn) \/
   (LENGTH a.po_stack = SUC (LENGTH b.po_stack) /\
    LENGTH at.po_stack = SUC (LENGTH bt.po_stack))) ==>
  !d. d <= LENGTH b.po_stack ==>
    R (ptr_owner_view d b).cf_fn (ptr_owner_view d bt).cf_fn
Proof
  strip_tac >> rpt strip_tac
  >- metis_tac[ptr_owner_view_step_function]
  >- (Cases_on `d = LENGTH b.po_stack`
      >- simp[ptr_owner_view_def] >>
      `d <= LENGTH a.po_stack /\ d <= LENGTH at.po_stack /\ d <= LENGTH bt.po_stack`
        by decide_tac >> metis_tac[ptr_owner_view_step_function]) >>
  `d <= LENGTH a.po_stack /\ d <= LENGTH at.po_stack /\ d <= LENGTH bt.po_stack`
    by decide_tac >> metis_tac[ptr_owner_view_step_function]
QED

Theorem ptr_structural_trace_owner_alignment:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  LENGTH a.po_stack = LENGTH at.po_stack /\
  (!d. d <= LENGTH a.po_stack ==>
    R (ptr_owner_view d a).cf_fn (ptr_owner_view d at).cf_fn)
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- simp[ptr_owner_view_def] 
  >- (drule ptr_tagged_chrono_step_projection >> strip_tac >>
      rename1 `ptr_chrono_step C a b` >>
      `b.po_stack = a.po_stack` by metis_tac[ptr_chrono_nop_stack] >>
      simp[] >> metis_tac[ptr_owner_view_step_function]) >>
  (conj_tac >- decide_tac >> rpt strip_tac >> irule ptr_paired_owner_step >>
   metis_tac[ptr_tagged_chrono_step_projection])
QED

Theorem ptr_structural_trace_entry_domain:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  FDOM entries = FDOM registry
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- simp[]
  >- (drule ptr_tagged_chrono_step_projection >> strip_tac >>
      drule_all ptr_chrono_nop_stack >> strip_tac >>
      simp[ptr_activation_registry_def]) >>
  simp[ptr_activation_registry_def]
QED

Theorem ptr_structural_trace_entry_sound:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  !t j. FLOOKUP entries t = SOME j ==>
    t < LENGTH h /\ j < LENGTH ht /\
    ?fn. FLOOKUP registry t = SOME fn /\ R fn (EL j ht).po_fn
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- simp[FLOOKUP_UPDATE] 
  >- (drule ptr_tagged_chrono_step_projection >> strip_tac >>
      drule_all ptr_chrono_nop_stack >> strip_tac >>
      simp[ptr_activation_registry_def] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> simp[] >> decide_tac) >>
  (simp[ptr_activation_registry_def, FLOOKUP_UPDATE] >> rpt gen_tac >> strip_tac >>
   gvs[AllCaseEqs()] >> simp[EL_APPEND_EQN] >>
   qpat_x_assum `!t j. _` (qspecl_then [`t`,`j`] mp_tac) >>
   simp[] >> strip_tac >> simp[] >> decide_tac)
QED

Theorem ptr_structural_trace_root_entry:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  0 < LENGTH h /\ FLOOKUP entries 0 = SOME 0
Proof
  ho_match_mp_tac ptr_structural_trace_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[FLOOKUP_UPDATE] >> Cases_on `h` >> gvs[]
QED

Theorem ptr_structural_trace_entry_retained:
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries /\
  FLOOKUP entries t = SOME j ==>
  FLOOKUP (if LENGTH b.po_stack = SUC (LENGTH a.po_stack)
           then entries |+ (LENGTH h,LENGTH ht) else entries) t = SOME j
Proof
  strip_tac >> drule_all ptr_structural_trace_entry_sound >> strip_tac >>
  `t <> LENGTH h` by decide_tac >>
  Cases_on `LENGTH b.po_stack = SUC (LENGTH a.po_stack)` >> simp[FLOOKUP_UPDATE]
QED

Theorem ptr_chrono_history_prefix:
  !vs0 C h a. ptr_chrono_history vs0 C h a ==>
  !n. n < LENGTH h ==>
    ptr_chrono_history vs0 C (TAKE (SUC n) h) (EL n h)
Proof
  ho_match_mp_tac ptr_chrono_history_strongind >> conj_tac
  >- (rpt strip_tac >> `n = 0` by gvs[] >>
      gvs[] >> metis_tac[ptr_chrono_history_rules]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `n < LENGTH h`
  >- (`SUC n - LENGTH h = 0` by decide_tac >>
      simp[TAKE_APPEND, EL_APPEND_EQN] >> first_x_assum irule >> simp[]) >>
  `n = LENGTH h` by gvs[] >> gvs[TAKE_LENGTH_TOO_LONG, EL_APPEND_EQN] >>
  metis_tac[ptr_chrono_history_rules]
QED

Theorem ptr_structural_trace_sample_ownership:
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries /\
  j < LENGTH ht ==>
  ?tokensj registryj birthsj PTj TGj savedj.
    ptr_source_ownership vs0 C
      (TAKE (SUC (EL j (done ++ [LENGTH h - 1]))) h)
      (EL (EL j (done ++ [LENGTH h - 1])) h)
      tokensj registryj birthsj PTj TGj savedj
Proof
  strip_tac >> drule ptr_structural_trace_embedding >> strip_tac >>
  `EL j (done ++ [LENGTH h - 1]) < LENGTH h` by
    (gvs[ptr_event_embedding_def, EVERY_EL] >> Cases_on `j < LENGTH done`
     >- (simp[EL_APPEND_EQN] >> first_x_assum irule >> simp[]) >>
     `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]) >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule_all ptr_chrono_history_prefix >> strip_tac >>
  metis_tac[ptr_source_activations_total, ptr_source_birth_caches_total,
    ptr_source_ownership_total]
QED

Theorem ptr_structural_trace_depth:
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  LENGTH tokens = SUC (LENGTH a.po_stack) /\
  LENGTH a.po_stack = LENGTH at.po_stack
Proof
  strip_tac >> drule ptr_structural_trace_owner_alignment >> strip_tac >> simp[] >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> simp[]
QED

Theorem ptr_structural_trace_nop_interval:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries ==>
  !q. q < LENGTH done ==>
    SUC (EL q done) <= EL (SUC q) (done ++ [LENGTH h - 1]) /\
    EL (SUC q) (done ++ [LENGTH h - 1]) < LENGTH h /\
    !k. SUC (EL q done) <= k /\
      k < EL (SUC q) (done ++ [LENGTH h - 1]) ==>
      (EL k h).po_inst.inst_opcode = NOP
Proof
  ho_match_mp_tac ptr_structural_trace_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- simp[]
  >- (drule ptr_structural_trace_samples >> strip_tac >>
      drule ptr_structural_trace_source >>
      disch_then (mp_tac o MATCH_MP ptr_chrono_history_end) >> strip_tac >>
      qx_gen_tac `q` >> strip_tac >>
      qpat_x_assum `!q. q < LENGTH done ==> SUC _ <= _ /\ _`
        (qspec_then `q` mp_tac) >> simp[] >> strip_tac >>
      Cases_on `SUC q < LENGTH done`
      >- (gvs[EL_APPEND_EQN] >> rpt strip_tac >>
          first_x_assum irule >> simp[]) >>
      `SUC q = LENGTH done` by decide_tac >>
      gvs[EL_APPEND_EQN] >>
      rpt strip_tac >>
      Cases_on `k < LENGTH h - 1`
      >- (first_x_assum irule >> simp[]) >>
      `k = LENGTH h - 1` by decide_tac >>
      gvs[LAST_EL, PRE_SUB1]) >>
  (drule ptr_structural_trace_samples >> strip_tac >>
  qx_gen_tac `q` >> strip_tac >>
  Cases_on `q < LENGTH done`
  >- (qpat_x_assum `!q. q < LENGTH done ==> SUC _ <= _ /\ _`
        (qspec_then `q` mp_tac) >> simp[] >> strip_tac >>
      Cases_on `SUC q < LENGTH done`
      >- (gvs[EL_APPEND_EQN] >> rpt strip_tac >>
          first_x_assum irule >> simp[]) >>
      `SUC q = LENGTH done` by decide_tac >>
      gvs[EL_APPEND_EQN] >> rpt strip_tac >>
      first_x_assum irule >> simp[]) >>
  `q = LENGTH done` by gvs[] >>
  `SUC (LENGTH done) = LENGTH ht` by decide_tac >>
  simp[EL_APPEND_EQN])
QED

Theorem ptr_chrono_nop_memory_fields[local]:
  !C a b. ptr_chrono_step C a b ==> a.po_inst.inst_opcode = NOP ==>
    a.po_state.vs_memory = b.po_state.vs_memory /\
    a.po_state.vs_returndata = b.po_state.vs_returndata
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> simp[ptr_observe_def] >>
  rpt strip_tac >> gvs[is_terminator_def, step_inst_non_invoke, step_inst_base_def]
QED

Theorem ptr_chrono_nop_interval_fields[local]:
  !hi lo. ptr_chrono_history vs0 C h a /\ lo <= hi /\ hi < LENGTH h /\
    (!k. lo <= k /\ k < hi ==> (EL k h).po_inst.inst_opcode = NOP) ==>
    (EL lo h).po_state.vs_memory = (EL hi h).po_state.vs_memory /\
    (EL lo h).po_state.vs_returndata = (EL hi h).po_state.vs_returndata
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`lo = 0` by decide_tac >> simp[]) >>
  Cases_on `lo = SUC hi` >- simp[] >>
  `lo <= hi /\ hi < LENGTH h` by decide_tac >>
  `ptr_chrono_step C (EL hi h) (EL (SUC hi) h)` by
    metis_tac[concretizePtrLifetimeTheory.ptr_chrono_history_adjacent] >>
  `(EL hi h).po_inst.inst_opcode = NOP` by
    (first_x_assum irule >> decide_tac) >>
  drule_all ptr_chrono_nop_memory_fields >> strip_tac >>
  `((EL lo h).po_state.vs_memory = (EL hi h).po_state.vs_memory) /\
   ((EL lo h).po_state.vs_returndata = (EL hi h).po_state.vs_returndata)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Theorem ptr_structural_trace_gap_memory:
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries /\
  q < LENGTH done /\ n = EL q done /\ m = EL (SUC q) (done ++ [LENGTH h - 1]) ==>
  (EL (SUC n) h).po_state.vs_memory = (EL m h).po_state.vs_memory
Proof
  strip_tac >> drule_all ptr_structural_trace_nop_interval >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  metis_tac[ptr_chrono_nop_interval_fields]
QED

Theorem ptr_structural_trace_gap_returndata:
  ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG saved entries /\
  q < LENGTH done /\ n = EL q done /\ m = EL (SUC q) (done ++ [LENGTH h - 1]) ==>
  (EL (SUC n) h).po_state.vs_returndata = (EL m h).po_state.vs_returndata
Proof
  strip_tac >> drule_all ptr_structural_trace_nop_interval >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  metis_tac[ptr_chrono_nop_interval_fields]
QED
