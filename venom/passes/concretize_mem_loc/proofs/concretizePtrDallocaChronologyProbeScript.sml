Theory concretizePtrDallocaChronologyProbe
Ancestors
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrDallocaGhostInterface
  concretizePtrEventEmbedding concretizePtrOwnedAssignPrefix
  ptrDiscipline venomExecSemantics venomState venomInst
  list rich_list arithmetic

(* Retrospective restriction at a matched event retains the former final
   sample.  In contrast, a source-only gap replaces that sample. *)
Theorem ptr_dalloca_samples_pair_predecessor:
  ptr_sample_list P (h ++ [b]) (ht ++ [bt])
    (done ++ [LENGTH h - 1]) (H ++ [snapshot]) /\
  LENGTH H = LENGTH h /\ 0 < LENGTH h /\
  LENGTH ht = SUC (LENGTH done) /\ EVERY (\n. n < LENGTH h) done ==>
  ptr_sample_list P h ht done H
Proof
  rewrite_tac[ptr_sample_list_def] >> strip_tac >> simp[] >>
  rpt strip_tac >>
  `EL j (done ++ [LENGTH h - 1]) < LENGTH h` by
    (Cases_on `j < LENGTH done`
     >- (simp[EL_APPEND_EQN] >> gvs[EVERY_EL]) >>
     `j = LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]) >>
  first_x_assum (qspec_then `j` mp_tac) >>
  Cases_on `j < LENGTH done`
  >- (gvs[EL_APPEND_EQN, EVERY_EL]) >>
  `j = LENGTH done` by decide_tac >> gvs[EL_APPEND_EQN]
QED

(* A gap does not retain its old final sample. This exact reverse interface
   requires that one point explicitly; all departed points are retained. *)
Theorem ptr_dalloca_samples_gap_predecessor:
  ptr_sample_list P (h ++ [b]) ht done (H ++ [snapshot]) /\
  LENGTH H = LENGTH h /\ 0 < LENGTH h /\
  EVERY (\n. n < LENGTH h) done /\
  P (LAST h) (LAST ht) (LAST H) ==>
  ptr_sample_list P h ht done H
Proof
  rewrite_tac[ptr_sample_list_def] >> strip_tac >> simp[] >>
  rpt strip_tac >> Cases_on `j < LENGTH done`
  >- (`EL j done < LENGTH h` by gvs[EVERY_EL] >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[EL_APPEND_EQN]) >>
  `j = LENGTH done` by decide_tac >>
  `h <> [] /\ ht <> [] /\ H <> []` by
    (Cases_on `h` >> Cases_on `ht` >> Cases_on `H` >> gvs[]) >>
  gvs[LAST_EL, EL_APPEND_EQN, PRE_SUB1]
QED

(* A checked list-level obstruction, not a counterexample to a stage
   theorem: the gap successor alone contains no old final P fact. *)
Theorem ptr_dalloca_gap_moves_final:
  ptr_sample_list (\a at snapshot. a = (1:num)) [0;1] [0:num] [] [0:num;0] /\
  ~ptr_sample_list (\a at snapshot. a = (1:num)) [0] [0:num] [] [0:num]
Proof
  simp[ptr_sample_list_def]
QED

(* The boundary needed by retrospective proofs is source-indexed.
   In particular the snapshot at SUC n is not an endpoint ownership map.
   P can conjoin ghost, alignment and other pointwise sample invariants. *)
Theorem ptr_dalloca_transcript_boundary:
  ptr_structural_transcript R vs0 C Ct h a ht at done
    tokens registry births PT TG saved entries H /\
  ptr_sample_list P h ht done H ==>
  !j. j < LENGTH done ==>
    P (EL (EL j done) h) (EL j ht) (EL (EL j done) H) /\
    ptr_snapshot_step C (TAKE (SUC (EL j done)) h)
      (EL (EL j done) h) (EL (SUC (EL j done)) h)
      (EL (EL j done) H) (EL (SUC (EL j done)) H)
Proof
  strip_tac >> drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  rpt strip_tac
  >- (gvs[ptr_sample_list_def] >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[EL_APPEND_EQN]) >>
  irule ptr_structural_transcript_adjacent >> conj_tac
  >- (gvs[ptr_event_embedding_def] >>
      first_x_assum (qspecl_then [`j`,`LENGTH done`] mp_tac) >>
      simp[EL_APPEND_EQN]) >>
  metis_tac[]
QED

(* Actual NOP semantics, not a relation postulated on arbitrary endpoints. *)
Theorem ptr_dalloca_nop_observation:
  !C a b. ptr_chrono_step C a b ==>
  a.po_inst.inst_opcode = NOP /\ a.po_inst.inst_outputs = [] ==>
  b.po_params = a.po_params /\ b.po_prov = a.po_prov /\
  b.po_taint = a.po_taint /\ b.po_stack = a.po_stack /\
  b.po_fn = a.po_fn /\
  b.po_state = (a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx)
Proof
  ho_match_mp_tac ptr_chrono_step_ind >>
  simp[ptr_observe_def] >> rpt strip_tac >>
  gvs[is_terminator_def, step_inst_non_invoke, step_inst_base_def] >>
  metis_tac[ptr_assign_prefix_nop_ghosts]
QED

Theorem ptr_dalloca_saved_call_sample:
  ptr_sample_list P h ht done H /\
  ptr_paired_call h ht done H frame framet tags (n,j) ==>
  P (EL n h) (EL j ht) (EL n H)
Proof
  simp[ptr_sample_list_def, ptr_paired_call_def] >> strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[EL_APPEND_EQN]
QED

Theorem ptr_dalloca_nop_ghost_sample:
  ptr_chrono_step C a b /\ a.po_inst.inst_opcode = NOP /\
  a.po_inst.inst_outputs = [] ==>
  (ptr_dalloca_ghost_sample lo dyn registry births live a at <=>
   ptr_dalloca_ghost_sample lo dyn registry births live b at)
Proof
  strip_tac >> drule_all ptr_dalloca_nop_observation >> strip_tac >>
  simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def,
       ptr_dalloca_ghost_vars_def, lookup_var_def]
QED

(* This lifting principle quantifies over P, rather than reconstructing a
   paired_prefix at each predecessor. Its premises are semantic closure
   obligations; it does not assert that the content sample has ghost fields. *)
Theorem ptr_dalloca_transcript_sample_induction:
  !R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H.
  ptr_structural_transcript R vs0 C Ct h a ht at done
    tokens registry births PT TG saved entries H ==>
  !P.
  (!x xt. ptr_chrono_history vs0 C [x] x /\ x.po_stack = [] /\
     ptr_chrono_history vs0 Ct [xt] xt /\ xt.po_stack = [] /\
     R x.po_fn xt.po_fn ==>
     P x xt ([0], FEMPTY |+ (0,x.po_fn),
       ptr_birth_lift 0 x.po_state.vs_allocas, [], FEMPTY, [], FEMPTY |+ (0,0))) /\
  (!(hs:ptr_observation list) x xt snap y snap'. P x xt snap /\ x.po_inst.inst_opcode = NOP /\
     ptr_snapshot_step C hs x y snap snap' ==> P y xt snap') /\
  (!(hs:ptr_observation list) x xt snap y yt snap'. P x xt snap /\
     ptr_snapshot_step C hs x y snap snap' /\ ptr_chrono_step Ct xt yt /\
     x.po_inst.inst_id = xt.po_inst.inst_id ==> P y yt snap') ==>
  P a at (tokens,registry,births,PT,TG,saved,entries) /\
  ptr_sample_list P h ht done H
Proof
  ho_match_mp_tac ptr_structural_transcript_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac
  >- (simp[ptr_sample_list_def] >> metis_tac[]) >>
  first_x_assum (qspec_then `P` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac
  >- (conj_asm1_tac
      >- (qpat_x_assum `!hs x xt snap y snap'.
            P x xt snap /\ x.po_inst.inst_opcode = NOP /\ _ ==> _` irule >>
          goal_assum (drule_at Any) >>
          simp[ptr_snapshot_step_def] >> qexists_tac `h` >> simp[]) >>
      drule ptr_structural_transcript_erasure >> strip_tac >>
      drule ptr_structural_trace_target >> strip_tac >>
      drule ptr_chrono_history_end >> strip_tac >>
      irule ptr_sample_list_gap >> simp[] >>
      `EL (LENGTH done) ht = at` by
        (gvs[ptr_sample_list_def, LAST_EL, PRE_SUB1]) >> simp[]) >>
  (conj_asm1_tac
   >- (qpat_x_assum `!hs x xt snap y yt snap'. _` irule >>
       goal_assum (drule_at Any) >>
       simp[ptr_snapshot_step_def] >> qexists_tac `h` >> simp[]) >>
   irule ptr_sample_list_pair >> simp[])
QED

(* Audit of the retrospective route.

   The theorem above is a conditional induction principle, not preservation
   of any proposed ghost invariant.  Its IH supplies both the old endpoint
   P and all departed P samples.  The gap branch uses the old endpoint and
   semantic gap closure to replace the moving final sample; the pair branch
   freezes that endpoint and appends the new sample.  Neither branch assumes
   a predecessor paired_prefix.

   Existing root facts should be reused: ptr_chrono_root_inversion in
   concretizePtrPairedRoot plus ptr_dalloca_ghost_root supply the actual
   entry observation, with empty runtime provenance, parameters and stack.
   ptr_dalloca_nop_observation handles actual source NOP steps; its empty
   outputs premise follows from source instruction well-formedness, not
   from the opcode alone. It preserves all runtime fields relevant to the
   parent's classification clauses (lookup_var ignores vs_inst_idx).

   ptr_paired_prefix_def has six conjuncts. Structural predecessors come
   from strong induction; placements do not depend on history. Samples can
   be restricted at pair by samples_pair_predecessor, but gap needs the old
   final fact (samples_gap_predecessor and gap_moves_final). Alignment has
   the same moving-final issue because cursor refers to the current source
   instruction. The indexed boundary avoids claiming its old final cursor.

   Current paired_callers is an endpoint-only list: a RET removes a saved
   frame, and an INVOKE adds one. It therefore cannot simply be restricted
   by shortening h/ht; one must recover the predecessor caller witnesses
   from historical INVOKE points, or carry their indexed certificates.
   saved_call_sample exports P at such a historical point without falsely
   identifying current caller stacks with predecessor stacks.

   Finally ptr_paired_writes is EVERY of departed write witnesses plus
   completeness and distinctness; these witnesses are not runtime ghosts.
   A reverse proof would filter W by the earlier event index, prove its
   old ledger_write_pair and ownership facts by EL restrictions, and prove
   completeness separately. No such reverse prefix theorem is asserted
   here, and no ghost field is inferred from the write witnesses.
*)
