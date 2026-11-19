Theory gasFocusConcretizeGhostCutHistory
Ancestors
  gasFocusConcretizeGhostCutDemand gasFocusConcretizeGhostCutPoints
  gasFocusConcretizeGhostCutEffect gasFocusConcretizeGhostCutNext
  gasFocusConcretizeGhostCutControl concretizePtrDallocaRuntimeControl
  venomPassDispatcher concretizeStageShape concretizeStepShape concretizeMemLocDefs
  concretizePtrPairedRoot concretizePtrPairedFields concretizePtrParamShape concretizePtrOwnershipErasure
  concretizePtrSourceOwnership concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrEventEmbedding
  concretizePtrPairedPrefix concretizePtrChronologicalHistory concretizePtrLifetime
  concretizePtrDallocaGhostInterface concretizePtrDallocaChronologyProbe
  concretizePtrHistoricalWriteExclusion concretizePtrDallocaActualFresh concretizeStepStructure
  ptrDiscipline venomState venomInst
  frameAllocationOwnership venomExecSemantics venomWf o1PassContract contextCodegenRel
  list rich_list finite_map pred_set arithmetic

Theorem focus_concretize_cut_ghost_history:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  alloca_frontier_upto n C vs /\ fixed_region_reserved lo C /\
  o1_safe_upto D lo n C vs /\ gas_cut n vs at.po_state /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done ==>
  !i q.
    i < LENGTH h /\ q <= LENGTH done /\
    (q = 0 \/ EL (q-1) done < i) /\
    i <= EL q (done ++ [LENGTH h - 1]) ==>
    !tsj rj bj PTj TGj sj ej. EL i H = (tsj,rj,bj,PTj,TGj,sj,ej) ==>
    ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY bj
      (\token aid. F) (EL i h) (EL q ht) /\
    (!v site. FLOOKUP (EL q ht).po_prov v = SOME site ==>
      FLOOKUP TGj v = NONE) /\
    (!v site. FLOOKUP TGj v = NONE /\
      FLOOKUP (EL i h).po_prov v = SOME site ==>
      FLOOKUP (EL q ht).po_prov v = SOME site) /\
    LENGTH PTj = LENGTH (EL i h).po_params /\
    LENGTH (EL i h).po_params = LENGTH (EL q ht).po_params /\
    (!k site. k < LENGTH (EL i h).po_params ==>
      (EL k (EL q ht).po_params = SOME site ==>
        EL k (EL i h).po_params = SOME site /\ EL k PTj = NONE /\
        EL k (EL i h).po_state.vs_params =
          EL k (EL q ht).po_state.vs_params) /\
      (EL k PTj = NONE /\ EL k (EL i h).po_params = SOME site ==>
        EL k (EL q ht).po_params = SOME site)) /\
    LENGTH sj = LENGTH (EL i h).po_stack /\
    LIST_REL (\((pt,tg),f) ft.
      ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
        ft.cf_prov ft.cf_tvar ft.cf_state /\
      (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP tg v = NONE) /\
      (!v site. FLOOKUP tg v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
        FLOOKUP ft.cf_prov v = SOME site) /\
      f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs /\
      LENGTH pt = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
      (!k site. k < LENGTH f.cf_params ==>
        (EL k ft.cf_params = SOME site ==>
          EL k f.cf_params = SOME site /\ EL k pt = NONE /\
          EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
        (EL k pt = NONE /\ EL k f.cf_params = SOME site ==>
          EL k ft.cf_params = SOME site)))
      (ZIP (sj,(EL i h).po_stack)) (EL q ht).po_stack /\
    (!v token aid base size pos ix.
      ~in_revert_forward (EL i h).po_fn (EL i h).po_state /\
      (EL i h).po_inst.inst_opcode <> ASSIGN /\
      MEM (Var v) (EL i h).po_inst.inst_operands /\
      (inst_read_op (EL i h).po_inst = SOME (Var v) \/
        (EL i h).po_inst.inst_opcode = INVOKE) /\
      FLOOKUP TGj v = SOME (token,aid) /\
      FLOOKUP (EL i h).po_prov v = SOME (base,size) /\
      FLOOKUP bj (token,aid) = SOME (base,size) /\
      FLOOKUP positions (Allocation aid) = SOME (pos,size) /\ ix < size ==>
      pos+ix IN (EL q ht).po_taint.t_mem ==>
        base+ix IN (EL i h).po_taint.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  ho_match_mp_tac ptr_event_embedding_source_induction >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `ptr_chrono_history vs C [EL 0 h] (EL 0 h)` by
        (qpat_assum `ptr_chrono_history vs C h endpoint`
           (qspec_then `0` mp_tac o MATCH_MP ptr_chrono_history_prefix) >>
         Cases_on `h` >> fs[ptr_paired_samples_def, ptr_sample_list_def]) >>
      `ptr_chrono_history vs C' [EL 0 ht] (EL 0 ht)` by
        (qpat_assum `ptr_chrono_history vs C' ht at`
           (qspec_then `0` mp_tac o MATCH_MP ptr_chrono_history_prefix) >>
         Cases_on `ht` >> fs[ptr_paired_samples_def, ptr_sample_list_def]) >>
      `ptr_source_ownership vs C [EL 0 h] (EL 0 h) tsj rj bj PTj TGj sj` by
        (drule_then (qspec_then `0` mp_tac) ptr_structural_transcript_ownership >>
         Cases_on `h` >> fs[ptr_paired_samples_def, ptr_sample_list_def,
                            ptr_snapshot_ownership_def]) >>
      qpat_x_assum `ptr_source_ownership vs C [_] _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [Once ptr_source_ownership_cases]) >>
      simp[] >> strip_tac >>
      qpat_assum `ptr_chrono_history vs C [EL 0 h] (EL 0 h)`
        (strip_assume_tac o MATCH_MP ptr_chrono_root_inversion) >>
      qpat_assum `ptr_chrono_history vs C' [EL 0 ht] (EL 0 ht)`
        (strip_assume_tac o MATCH_MP ptr_chrono_root_inversion) >>
      gvs[ptr_observe_def, ptr_observation_component_equality, ptr_params_erases_def,
          ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def,
          ptr_dalloca_ghost_vars_def, entry_taint_def, op_taint_def] >>
      drule_then (mp_tac o MATCH_MP ptr_source_birth_caches_activations)
        ptr_source_ownership_caches >>
      simp[Once ptr_ledger_source_activations_cases]) >>
  map_every qx_gen_tac [`i`,`q`] >>
  disch_then (fn th =>
    let val cs = CONJUNCTS th in
      map_every assume_tac (List.take (cs, 4)) >> mk_asm "earlier" (List.last cs)
    end) >>
  `!j r. j <= i /\ r < LENGTH done /\ EL r done = j ==>
     r <= LENGTH done /\ (r = 0 \/ EL (r-1) done < j) /\
     j <= EL r (done ++ [LENGTH h - 1])` by
    (rpt gen_tac >> strip_tac >>
     `r <= LENGTH done` by decide_tac >>
     `EL r (done ++ [LENGTH h - 1]) = EL r done` by simp[EL_APPEND_EQN] >>
     simp[] >> Cases_on `r = 0` >> simp[] >>
     `r-1 < r` by decide_tac >>
     qpat_assum `ptr_event_embedding _ _ _`
       (qspecl_then [`r-1`,`r`] mp_tac o cj 3 o REWRITE_RULE [ptr_event_embedding_def]) >>
     `r-1 < LENGTH done` by decide_tac >>
     simp[EL_APPEND_EQN]) >>
  `!j r. j < SUC i /\ r < LENGTH done /\ EL r done = j ==>
     ?bj. ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY bj
       (\token aid. F) (EL j h) (EL r ht)` by
    (rpt gen_tac >> strip_tac >>
     `j <= i` by decide_tac >>
     qpat_assum `!j r. j <= i /\ _ ==> _`
       (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qabbrev_tac `row = EL j H` >> PairCases_on `row` >>
     qpat_assum `Abbrev (_ = EL j H)`
       (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     asm "earlier" (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qspecl_then [`row0`,`row1`,`row2`,`row3`,`row4`,`row5`,`row6`] mp_tac) >>
     simp[] >> strip_tac >> qexists `row2` >> first_assum ACCEPT_TAC) >>
  `!j r op. j < SUC i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!j r. j < SUC i /\ _ ==> ?bj. ptr_dalloca_ghost_sample _ _ _ _ _ _ _`
       (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `bj` (strip_assume_tac o
       REWRITE_RULE [ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def])) >>
     Cases_on `op` >> simp[op_taint_def] >>
     qpat_x_assum `ptr_dalloca_ghost_vars _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ptr_dalloca_ghost_vars_def]) >>
     simp[op_taint_def, entry_taint_def] >>
     disch_then (MATCH_ACCEPT_TAC o SPEC_ALL)) >>
  `!j r x. j < SUC i /\ r < LENGTH done /\ EL r done = j /\
     (x < lo \/ dyn_floor C vs <= x) ==>
     x IN (EL r ht).po_taint.t_mem ==> x IN (EL j h).po_taint.t_mem` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!j r. j < SUC i /\ _ ==> ?bj. ptr_dalloca_ghost_sample _ _ _ _ _ _ _`
       (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `bj` (mp_tac o Q.SPEC `x` o cj 5 o
       CONJUNCT1 o REWRITE_RULE [ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def])) >>
     simp[]) >>
  `!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < SUC i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem` by
    (map_every qx_gen_tac [`j`,`r`,`u`,`tok`,`id`,`byte_base`,`byte_size`,`byte_pos`,`ix`,
       `ts`,`rw`,`bw`,`PTw`,`TGw`,`sw`,`ew`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `j <= i` by decide_tac >>
     qpat_assum `!j r. j <= i /\ _ ==> _` (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
     asm "earlier" (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qspecl_then [`ts`,`rw`,`bw`,`PTw`,`TGw`,`sw`,`ew`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qspecl_then [`u`,`tok`,`id`,`byte_base`,`byte_size`,`byte_pos`,`ix`] mp_tac o
       List.last o CONJUNCTS) >> simp[]) >>
  `!r. r <= LENGTH done /\ (r = 0 \/ EL (r-1) done < SUC i) /\
       SUC i <= EL r (done ++ [LENGTH h-1]) ==>
    !ts rw bw PTw TGw sw ew. EL (SUC i) H = (ts,rw,bw,PTw,TGw,sw,ew) ==>
    !u tok id rb sz p ix.
      ~in_revert_forward (EL (SUC i) h).po_fn (EL (SUC i) h).po_state /\
      (EL (SUC i) h).po_inst.inst_opcode <> ASSIGN /\
      MEM (Var u) (EL (SUC i) h).po_inst.inst_operands /\
      (inst_read_op (EL (SUC i) h).po_inst = SOME (Var u) \/
       (EL (SUC i) h).po_inst.inst_opcode = INVOKE) /\
      FLOOKUP TGw u = SOME (tok,id) /\
      FLOOKUP (EL (SUC i) h).po_prov u = SOME (rb,sz) /\
      FLOOKUP bw (tok,id) = SOME (rb,sz) /\
      FLOOKUP positions (Allocation id) = SOME (p,sz) /\ ix < sz ==>
      p+ix IN (EL r ht).po_taint.t_mem ==> rb+ix IN (EL (SUC i) h).po_taint.t_mem` by
    (qx_gen_tac `r` >> disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt gen_tac >> disch_tac >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
     irule focus_cut_frontier_demanded_reflection >>
     qhdtm_assum `ptr_paired_prefix` (irule_at Any) >>
     qpat_assum `EL (SUC i) H = _` (irule_at Any) >>
     qpat_assum `FLOOKUP TGw u = SOME (tok,id)` (irule_at Any) >>
     qpat_assum `p + ix IN (EL r ht).po_taint.t_mem` (irule_at Any) >>
     qpat_assum `o1_safe_upto D lo n C vs` (irule_at Any) >>
     qpat_assum `max_live_eom C' = SOME eom` (irule_at Any) >>
     qpat_assum `callee_first names C.ctx_functions` (irule_at Any) >>
     qpat_assum `ctx_pass_stage rpolicy _ _ C C'` (irule_at Any) >>
     qexists `sz` >> asm_rewrite_tac[] >> conj_tac >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!j r x. j < SUC i /\ _ ==> x IN _ ==> x IN _`
       (qspecl_then [`j`,`r'`,`a`] mp_tac) >> simp[]) >>
  qabbrev_tac `before_row = EL i H` >> PairCases_on `before_row` >>
  qabbrev_tac `after_row = EL (SUC i) H` >> PairCases_on `after_row` >>
  qpat_assum `Abbrev (_ = EL i H)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (_ = EL (SUC i) H)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_x "earlier" (qspecl_then [`i`,`q`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[LESS_EQ_REFL]) >>
  disch_then (qspecl_then [`before_row0`,`before_row1`,`before_row2`,
    `before_row3`,`before_row4`,`before_row5`,`before_row6`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qspec_then `i` mp_tac) ptr_structural_transcript_adjacent >>
  asm_rewrite_tac[ptr_snapshot_step_def] >> strip_tac >>
  `ptr_chrono_step C (EL i h) (EL (SUC i) h)` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  `!r s. r < s /\ s < LENGTH done ==> EL r done < EL s done` by
    (rpt gen_tac >> strip_tac >>
     qhdtm_assum `ptr_event_embedding`
       (qspecl_then [`r`,`s`] mp_tac o cj 3 o REWRITE_RULE [ptr_event_embedding_def]) >>
     `r < LENGTH done` by decide_tac >> simp[EL_APPEND_EQN]) >>
  reverse conj_tac
  >- (disch_tac >>
      `~MEM i done` by
        (strip_tac >>
         qpat_x_assum `MEM i done` (mp_tac o REWRITE_RULE [MEM_EL]) >>
         disch_then (qx_choose_then `r` strip_assume_tac) >> Cases_on `r < q`
         >- (`r <= q-1 /\ q-1 < LENGTH done /\ EL (q-1) done < i` by decide_tac >>
             Cases_on `r = q-1` >- gvs[] >>
             `EL r done < EL (q-1) done` by
               (first_x_assum irule >> decide_tac) >> decide_tac) >>
         `q < LENGTH done /\ i < EL q done` by decide_tac >>
         Cases_on `r = q` >- gvs[] >>
         `EL q done < EL r done` by (first_x_assum irule >> decide_tac) >> decide_tac) >>
      `(EL i h).po_inst.inst_opcode = NOP` by
        (drule_then (qspec_then `i` mp_tac) ptr_structural_trace_unmatched_nop >>
         simp[] >> decide_tac) >>
      `active_inst (EL i h).po_fn (EL i h).po_inst (EL i h).po_state` by
        (qpat_assum `ptr_chrono_step C (EL i h) (EL (SUC i) h)` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[Once ptr_chrono_step_cases] >> rpt strip_tac >> gvs[ptr_observe_def]) >>
      `MEM (EL i h).po_fn C.ctx_functions /\
       MEM (EL i h).po_inst (fn_insts (EL i h).po_fn)` by
        (conj_tac
         >- (qpat_assum `ptr_chrono_history vs C h endpoint`
               (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
             simp[EVERY_EL] >> strip_tac >>
             `ptr_observation_reachable vs C (EL i h)` by
               (first_x_assum irule >> decide_tac) >>
             fs[ptr_observation_reachable_def] >>
             drule frame_reachable_functions_member >> simp[]) >>
         fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
      `(EL i h).po_inst.inst_outputs = []` by
        (drule o1_ctx_shape_instructions_wf >>
         simp[EVERY_MEM] >> strip_tac >>
         `inst_wf (EL i h).po_inst` by metis_tac[] >>
         qpat_x_assum `inst_wf (EL i h).po_inst` mp_tac >>
         qpat_assum `(EL i h).po_inst.inst_opcode = NOP`
           (fn th => simp[inst_wf_def, th])) >>
      drule_all ptr_tagged_chrono_step_nop >> strip_tac >>
      drule_all ptr_dalloca_nop_observation >> strip_tac >>
      `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY before_row2
         (\token aid. F) (EL (SUC i) h) (EL q ht)` by
        (drule_all ptr_dalloca_nop_ghost_sample >>
         disch_then (irule o iffLR) >> first_assum ACCEPT_TAC) >>
      `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY after_row2
         (\token aid. F) (EL (SUC i) h) (EL q ht)` by
        (qpat_assum `ptr_dalloca_ghost_sample _ _ _ before_row2 _ (EL (SUC i) h) _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      `q = 0 \/ EL (q-1) done < SUC i` by decide_tac >>
      `SUC i <= EL q (done ++ [LENGTH h-1])` by
        (qpat_assum `SUC i < LENGTH h` mp_tac >>
         qpat_assum `q <= LENGTH done` mp_tac >>
         qpat_assum `q = LENGTH done \/ i < EL q done` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         Cases_on `q = LENGTH done` >> fs[EL_APPEND_EQN] >> decide_tac) >>
      qpat_assum `!r. r <= LENGTH done /\ _ ==> _`
        (qspec_then `q` mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (qspecl_then [`after_row0`,`after_row1`,`after_row2`,
        `after_row3`,`after_row4`,`after_row5`,`after_row6`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (mk_asm "nop_demand") >>
      pure_rewrite_tac[pairTheory.PAIR_EQ] >> rpt gen_tac >>
      disch_then (map_every (SUBST1_TAC o SYM) o CONJUNCTS) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `((EL (SUC i) h).po_state).vs_params = ((EL i h).po_state).vs_params` by simp[] >>
      asm_x "nop_demand" assume_tac >>
      rpt conj_tac >>
      map_every (fn pat => qpat_assum pat (SUBST_ALL_TAC))
        [`((EL (SUC i) h).po_state).vs_params = _`,
         `after_row3 = before_row3`, `after_row4 = before_row4`,
         `after_row5 = before_row5`, `(EL (SUC i) h).po_params = _`,
         `(EL (SUC i) h).po_prov = _`, `(EL (SUC i) h).po_stack = _`] >>
      first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `SUC q < LENGTH ht` by decide_tac >>
  `ptr_chrono_step C' (EL q ht) (EL (SUC q) ht)` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (qspec_then `q` mp_tac o MATCH_MP ptr_chrono_history_adjacent) >> simp[]) >>
  `SUC i <= EL (SUC q) (done ++ [LENGTH h-1])` by
    (drule_then (qspec_then `q` mp_tac) ptr_structural_trace_nop_interval >> simp[]) >>
  qpat_assum `!r. r <= LENGTH done /\ _ ==> _`
    (qspec_then `SUC q` mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (qspecl_then [`after_row0`,`after_row1`,`after_row2`,
    `after_row3`,`after_row4`,`after_row5`,`after_row6`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (mk_asm "match_demand") >>
  drule_all focus_concretize_ghost_cut_points >>
  disch_then (qspec_then `i` mp_tac o cj 2) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  `MEM (EL i h).po_fn C.ctx_functions` by
    (qpat_assum `ptr_observation_reachable vs C (EL i h)`
       (mp_tac o REWRITE_RULE [ptr_observation_reachable_def]) >>
     strip_tac >> drule frame_reachable_functions_member >> simp[]) >>
  `fn_inst_ids_distinct (EL i h).po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `q < LENGTH ht` by decide_tac >>
  `ptr_paired_cursor lp (EL i h) (EL q ht)` by
    (drule (cj 2 ptr_paired_prefix_alignment) >>
     disch_then (qspec_then `q` mp_tac) >> simp[EL_APPEND_EQN]) >>
  `(EL i h).po_inst.inst_id = (EL q ht).po_inst.inst_id` by
    (drule ptr_trace_departed_inst_ids >> disch_then (qspec_then `q` mp_tac) >> simp[]) >>
  `(EL q ht).po_inst = concretize_inst_with_positions (lp (EL i h).po_fn) (EL i h).po_inst` by
    (drule_all ptr_departed_cursor_instruction >> simp[]) >>
  qpat_assum `ptr_dalloca_ghost_sample _ _ _ _ _ (EL i h) (EL q ht)`
    (strip_assume_tac o REWRITE_RULE [ptr_dalloca_ghost_sample_def,
                                    ptr_dalloca_ghost_compare_def]) >>
  `!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL i h).po_taint op` by
    (first_x_assum irule >> decide_tac) >>
  `!op. op_taint (EL q ht).po_taint op SUBSET {k | k < 32}` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[EVERY_EL] >> strip_tac >>
     first_x_assum (qspec_then `q` mp_tac) >>
     simp[ptr_observation_reachable_def] >> rpt strip_tac >>
     drule lowerDloadPtrTaintBoundsTheory.dload_reachable_op_taint_bound >> simp[]) >>
  `EL q (done ++ [LENGTH h-1]) = i` by simp[EL_APPEND_EQN] >>
  `ptr_paired_sample positions (EL i h) (EL q ht)
     (before_row0,before_row1,before_row2,before_row3,before_row4,before_row5,before_row6)` by
    (qhdtm_assum `ptr_paired_samples`
       (qspec_then `q` mp_tac o cj 5 o REWRITE_RULE [ptr_paired_samples_def, ptr_sample_list_def]) >> simp[]) >>
  `ptr_mixed_vars before_row2 positions before_row4 (EL i h).po_taint
     (EL i h).po_fn (EL q ht).po_fn (EL i h).po_state (EL q ht).po_state` by
    fs[ptr_paired_sample_def] >>
  `ptr_history_content (EL i h).po_taint (EL i h).po_state (EL q ht).po_state` by
    fs[ptr_paired_sample_def] >>
  drule concretizePtrRequestHistoryTheory.ptr_history_content_labels >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    metis_tac[o1_ctx_shape_instructions_wf] >>
  `ptr_source_ownership vs C (TAKE (SUC i) h) (EL i h)
     before_row0 before_row1 before_row2 before_row3 before_row4 before_row5` by
    (drule ptr_structural_transcript_ownership >> disch_then (qspec_then `i` mp_tac) >>
     simp[ptr_snapshot_ownership_def] >> decide_tac) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[o1SafeUptoTheory.o1_safe_upto_def, o1SafeUptoTheory.o1_ptr_safe_upto_def,
        o1SafeUptoTheory.ptr_discipline_upto_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all gasFocusConcretizeTaggedSupportTheory.ptr_focus_source_tagged_support >> strip_tac >>
  `fn_ptr_ok P (EL i h).po_fn` by fs[EVERY_MEM] >>
  `opaque_use_ok (EL i h).po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM (EL i h).po_inst (fn_insts (EL i h).po_fn)` by
    (qpat_assum `ptr_chrono_step C (EL i h) _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[Once ptr_chrono_step_cases, ptr_observe_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[allocaFrontierBoundTheory.active_inst_mem_fn_insts]) >>
  `inst_wf (EL i h).po_inst` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `~in_revert_forward (EL i h).po_fn (EL i h).po_state` by
    (qpat_assum `EVERY (\j. ~in_revert_forward _ _) done`
       (qspec_then `q` mp_tac o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
  `ptr_ledger_erases (dyn_floor C vs) before_row2 before_row4 (EL i h).po_prov` by
    (qpat_assum `!ts r b pt tg sv en. EL i H = _ ==> _` mp_tac >> simp[]) >>
  drule ptr_paired_prefix_placements >> strip_tac >>
  `!id p sz. FLOOKUP positions (Allocation id) = SOME (p,sz) ==>
    p + sz < dimword(:256)` by
    (rpt strip_tac >> drule_all concretizePtrPlacementBoundsTheory.ptr_stage_placements_strict_bound >> simp[]) >>
  mp_tac (Q.INST [`a` |-> `EL i h`, `at` |-> `EL q ht`,
                  `z` |-> `EL (SUC i) h`, `zt` |-> `EL (SUC q) ht`,
                  `q` |-> `q`, `done` |-> `done`, `Ct` |-> `C'`,
                  `p` |-> `lp (EL i h).po_fn`] focus_cut_ghost_memory_next) >>
  (impl_tac >- (
     simp[IgnAsm `(EL q ht).po_inst = _`] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     strip_tac >>
     `~is_terminator (EL q ht).po_inst.inst_opcode /\ (EL q ht).po_inst.inst_opcode <> INVOKE` by
       metis_tac[concretize_positions_nonterminator, concretize_positions_not_invoke] >>
     conj_tac
     >- (irule ptr_dalloca_actual_fresh_bytes >>
         qhdtm_assum `ptr_paired_prefix` (irule_at Any) >> qexists `q` >> simp[]) >>
     conj_tac >- (
       `ptr_discipline_upto lo n C vs` by
         fs[o1SafeUptoTheory.o1_safe_upto_def, o1SafeUptoTheory.o1_ptr_safe_upto_def] >>
       `~in_revert_forward (EL (EL q done) h).po_fn (EL (EL q done) h).po_state` by
         (qpat_assum `EVERY _ done` (qspec_then `q` mp_tac o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
       qpat_assum `done❲q❳ = i` (SUBST_ALL_TAC o SYM) >>
       MATCH_MP_TAC gasFocusConcretizeCutActualWriteTheory.focus_cut_paired_actual_write_identity >>
       qhdtm_assum `ptr_paired_prefix` (irule_at Any) >> metis_tac[]) >>
     reverse conj_tac
     >- (conj_tac
         >- (rpt strip_tac >>
             `MEM (EL i h).po_inst.inst_opcode [SSTORE;TSTORE;ISTORE]` by simp[] >>
             qpat_assum `ptr_static_support P _ before_row4`
               (assume_tac o REWRITE_RULE [concretizePtrParamSupportTheory.ptr_static_support_def]) >>
             drule_all concretizePtrDallocaPersistentChannelsTheory.ptr_dalloca_store_selector_equal >> simp[]) >>
         (strip_tac >>
          rewrite_tac[GSYM concretizePtrRequestCompletionProbeTheory.ptr_call_adopted_def] >>
          ` (EL q ht).po_inst = (EL i h).po_inst` by
            (qpat_assum `(EL q ht).po_inst = concretize_inst_with_positions _ _`
               (fn th => simp[th, concretize_positions_unchanged])) >>
          qpat_assum `ptr_chrono_step C (EL i h) (EL (SUC i) h)`
            (mp_then Any mp_tac concretizePtrDallocaWriterGeometryTheory.ptr_dalloca_chrono_ordinary_update) >>
          simp[] >> disch_then strip_assume_tac >>
          qpat_assum `ptr_chrono_step C' (EL q ht) (EL (SUC q) ht)`
            (mp_then Any mp_tac concretizePtrDallocaWriterGeometryTheory.ptr_dalloca_chrono_ordinary_update) >>
          simp[] >> disch_then strip_assume_tac >>
          qpat_assum `ptr_static_support P _ before_row4`
            (assume_tac o REWRITE_RULE [concretizePtrParamSupportTheory.ptr_static_support_def]) >>
          drule_all concretizePtrDallocaPersistentChannelsTheory.ptr_dalloca_call_adoption >>
          simp[concretizePtrRequestCompletionProbeTheory.ptr_call_adopted_def])) >>
     strip_tac >>
     `(EL q ht).po_inst = (EL i h).po_inst` by
       (qpat_assum `(EL q ht).po_inst = concretize_inst_with_positions _ _`
          (fn th => simp[th, concretize_positions_unchanged])) >>
     `?dop sop nop dv x w. (EL i h).po_inst.inst_operands = [dop;sop;nop] /\
       eval_operand dop (EL i h).po_state = SOME dv /\
       eval_operand sop (EL i h).po_state = SOME x /\
       eval_operand nop (EL i h).po_state = SOME w` by
       (qpat_assum `ptr_chrono_step C (EL i h) (EL (SUC i) h)`
          (mp_then Any mp_tac ptr_chrono_ordinary_step_success) >>
        simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
        metis_tac[]) >>
     `?y z. eval_operand sop (EL q ht).po_state = SOME y /\
            eval_operand nop (EL q ht).po_state = SOME z` by
       (qpat_assum `ptr_chrono_step C' (EL q ht) (EL (SUC q) ht)`
          (mp_then Any mp_tac ptr_chrono_ordinary_step_success) >>
        simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
        metis_tac[]) >>
     `w = z` by
       (`!v. v IN FDOM before_row4 ==> v IN fn_pv P (EL i h).po_fn` by
          (fs[concretizePtrParamSupportTheory.ptr_static_support_def] >> metis_tac[flookup_thm]) >>
        `mem_write_ops (EL i h).po_inst = SOME
           <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>` by
          simp[memLocDefsTheory.mem_write_ops_def] >>
        `op_prov before_row4 nop = NONE` by
          (irule concretizePtrWritePurityTheory.ptr_write_max_size_no_provenance >>
           rpt (goal_assum drule) >> simp[]) >>
        `EVERY (ptr_nonopaque_operand (EL i h).po_fn) (EL i h).po_inst.inst_operands` by
          (irule concretizePtrOpaqueRetpcTheory.ptr_nonopaque_instruction_operands >> simp[]) >>
        `ptr_nonopaque_operand (EL i h).po_fn nop` by
          (qpat_assum `EVERY (ptr_nonopaque_operand _) _` mp_tac >> gvs[]) >>
        `op_taint (EL i h).po_taint nop = {}` by
          (fs[taint_ok_def] >> metis_tac[]) >>
        drule_all concretizePtrOpaqueRetpcTheory.ptr_mixed_vars_eval >>
        simp[concretizePtrValueTransportTheory.ptr_lookup_transport_def,
             concretizePtrValueTransportTheory.ptr_value_transport_scalar_empty]) >>
     qexistsl [`dop`,`sop`,`nop`,`x`,`y`,`w`] >> simp[] >> rpt strip_tac >>
     `~in_revert_forward (EL i h).po_fn (EL i h).po_state` by
       (qpat_assum `EVERY (\j. ~in_revert_forward _ _) done`
          (mp_tac o REWRITE_RULE [EVERY_EL]) >>
        disch_then (qspec_then `q` mp_tac) >> simp[]) >>
     `ptr_ledger_erases (dyn_floor C vs) before_row2 before_row4 (EL i h).po_prov` by
       (qpat_assum `!ts r b pt tg sv en. EL i H = _ ==> _` mp_tac >> simp[]) >>
     drule ptr_paired_prefix_placements >> strip_tac >>
     `!id p sz. FLOOKUP positions (Allocation id) = SOME (p,sz) ==>
       p + sz < dimword(:256)` by
       (rpt strip_tac >> drule_all concretizePtrPlacementBoundsTheory.ptr_stage_placements_strict_bound >> simp[]) >>
     drule_all concretizePtrDallocaEarlierReadTheory.ptr_dalloca_copy_read_transport >> strip_tac >>
     `mem_read_ops (EL i h).po_inst = SOME
        <|iao_ofst := sop; iao_size := SOME nop; iao_max_size := SOME nop|> /\
      MEM (w2n x,w2n z) (source_memory_read_ranges (EL i h).po_inst (EL i h).po_state)` by
       simp[memLocDefsTheory.mem_read_ops_def, source_memory_read_ranges_def] >>
     drule_all (SPEC_ALL concretizePtrDallocaEarlierReadTheory.ptr_dalloca_read_byte_classification
       |> Q.INST [`ops` |-> `<|iao_ofst := cp_src; iao_size := SOME cp_n; iao_max_size := SOME cp_n|>`]
       |> SIMP_RULE (srw_ss()) []) >>
     disch_then (DISJ_CASES_THEN2 strip_assume_tac
       (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac))
     >- (qpat_assum `!j. (_ < lo \/ dyn_floor C vs <= _) /\ _ ==> _`
           (qspec_then `k + w2n x` mp_tac) >> simp[] >>
         metis_tac[arithmeticTheory.ADD_COMM])
     >- (qpat_assum `!j. (_ < lo \/ dyn_floor C vs <= _) /\ _ ==> _`
           (qspec_then `k + w2n x` mp_tac) >> simp[] >>
         metis_tac[arithmeticTheory.ADD_COMM]) >>
     `inst_read_op (EL i h).po_inst = SOME (Var v)` by
       simp[concretizeMemLocDefsTheory.inst_read_op_def] >>
     `MEM (Var v) (EL i h).po_inst.inst_operands` by simp[] >>
     `pa + k' IN (EL q ht).po_taint.t_mem` by
       metis_tac[arithmeticTheory.ADD_COMM] >>
     `b + k' IN (EL i h).po_taint.t_mem` by
       (qpat_assum `!v tok id rb sz p ix. ~in_revert_forward (EL i h).po_fn _ /\ _ ==> _`
          (qspecl_then [`v`,`token`,`aid`,`b`,`sz`,`pa`,`k'`] mp_tac) >> simp[]) >>
     metis_tac[arithmeticTheory.ADD_COMM])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[pairTheory.PAIR_EQ] >> rpt gen_tac >>
  disch_then (map_every (SUBST1_TAC o SYM) o CONJUNCTS) >>
  Cases_on `~is_terminator (EL i h).po_inst.inst_opcode /\ (EL i h).po_inst.inst_opcode <> INVOKE`
  >- (
    qpat_x_assum `~is_terminator (EL i h).po_inst.inst_opcode /\ _` strip_assume_tac >>
    `ptr_snapshot_step C (TAKE (SUC i) h) (EL i h) (EL (SUC i) h)
       (before_row0,before_row1,before_row2,before_row3,before_row4,before_row5,before_row6)
       (after_row0,after_row1,after_row2,after_row3,after_row4,after_row5,after_row6)` by
      simp[ptr_snapshot_step_def] >>
    `(EL q ht).po_inst.inst_opcode <> NOP` by
      (`ptr_paired_code R lp positions (EL i h).po_fn (EL q ht).po_fn` by
         (drule (cj 1 ptr_paired_prefix_alignment) >>
          disch_then (qspec_then `q` mp_tac) >> simp[EL_APPEND_EQN]) >>
       `active_inst (EL q ht).po_fn (EL q ht).po_inst (EL q ht).po_state` by
         (qpat_assum `ptr_chrono_step C' (EL q ht) _` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          simp[Once ptr_chrono_step_cases, ptr_observe_def] >> rpt strip_tac >> gvs[]) >>
       fs[active_inst_def, ptr_paired_code_def] >>
       metis_tac[concretize_positions_inst_preimage, MEM_EL]) >>
    `!v tag. FLOOKUP before_row4 v = SOME tag ==> v IN fn_pv P (EL i h).po_fn` by
      fs[concretizePtrParamSupportTheory.ptr_static_support_def] >>
    `!j. j < lo ==> j IN (EL q ht).po_taint.t_mem ==> j IN (EL i h).po_taint.t_mem` by
      (rpt strip_tac >> first_x_assum irule >> simp[]) >>
    `!op w wt k. (EL i h).po_inst.inst_opcode = MLOAD /\ (EL i h).po_inst.inst_operands = [op] /\
       eval_operand op (EL i h).po_state = SOME w /\ eval_operand op (EL q ht).po_state = SOME wt /\ k < 32 ==>
       w2n wt + k IN (EL q ht).po_taint.t_mem ==> w2n w + k IN (EL i h).po_taint.t_mem` by
      (rpt gen_tac >> strip_tac >> strip_tac >>
       `EVERY (ptr_nonopaque_operand (EL i h).po_fn) (EL i h).po_inst.inst_operands` by
         (irule concretizePtrOpaqueRetpcTheory.ptr_nonopaque_instruction_operands >> simp[]) >>
       `ptr_nonopaque_operand (EL i h).po_fn op` by
         (qpat_x_assum `EVERY (ptr_nonopaque_operand _) _` mp_tac >> simp[listTheory.EVERY_DEF]) >>
       `op_taint (EL i h).po_taint op = {}` by fs[taint_ok_def] >>
       drule_all concretizePtrOpaqueRetpcTheory.ptr_mixed_vars_eval >>
       simp[] >> strip_tac >>
       `mem_read_ops (EL i h).po_inst = SOME
          <|iao_ofst := op; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|> /\
        MEM (w2n w,32) (source_memory_read_ranges (EL i h).po_inst (EL i h).po_state)` by
         simp[memLocDefsTheory.mem_read_ops_def, source_memory_read_ranges_def] >>
       drule_all (SPEC_ALL concretizePtrDallocaEarlierReadTheory.ptr_dalloca_read_byte_classification
         |> Q.INST [`ops` |-> `<|iao_ofst := load_op; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>`]
         |> SIMP_RULE (srw_ss()) []) >>
       disch_then (DISJ_CASES_THEN2 strip_assume_tac
         (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac))
       >- (qpat_assum `!j. (_ < lo \/ dyn_floor C vs <= _) /\ _ ==> _`
             (qspec_then `w2n w + k` mp_tac) >>
           gvs[arithmeticTheory.ADD_COMM])
       >- (qpat_assum `!j. (_ < lo \/ dyn_floor C vs <= _) /\ _ ==> _`
             (qspec_then `w2n w + k` mp_tac) >>
           gvs[arithmeticTheory.ADD_COMM]) >>
       `inst_read_op (EL i h).po_inst = SOME (Var v)` by
         gvs[concretizeMemLocDefsTheory.inst_read_op_def] >>
       `MEM (Var v) (EL i h).po_inst.inst_operands` by simp[] >>
       `pa + k' IN (EL q ht).po_taint.t_mem` by metis_tac[] >>
       `b + k' IN (EL i h).po_taint.t_mem` by
         (qpat_assum `!v tok id rb sz p ix. ~in_revert_forward (EL i h).po_fn _ /\ _ ==> _`
            (qspecl_then [`v`,`token`,`aid`,`b`,`sz`,`pa`,`k'`] mp_tac) >> simp[]) >>
       qpat_assum `w2n w + k = b + k'`
         (fn th => CONV_TAC (LAND_CONV (REWR_CONV arithmeticTheory.ADD_COMM THENC REWR_CONV th))) >>
       simp[]) >>
    `FDOM (EL i h).po_prov SUBSET fn_pv P (EL i h).po_fn` by
      (qpat_assum `ptr_observation_reachable vs C (EL i h)`
         (assume_tac o REWRITE_RULE [ptr_observation_reachable_def]) >>
       drule lowerDloadPtrSupportTheory.frame_reachable_prov_supported >>
       disch_then (qspec_then `P` (mp_tac o cj 2)) >>
       simp[GSYM EVERY_MEM] >> metis_tac[]) >>
    drule_all focus_cut_ghost_runtime_next >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
    conj_tac
    >- (qpat_assum `EL q done = i` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
        simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
    markerLib.asm_x "match_demand" mp_tac >> simp[] >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  Q.SUBGOAL_THEN `(EL i h).po_inst.inst_opcode = JMP \/ (EL i h).po_inst.inst_opcode = JNZ \/
     (EL i h).po_inst.inst_opcode = DJMP \/ (EL i h).po_inst.inst_opcode = INVOKE \/
     is_raw_return_opcode (EL i h).po_inst.inst_opcode` assume_tac
  >- (qpat_assum `ptr_chrono_step C (EL i h) (EL (SUC i) h)` mp_tac >>
     qpat_assum `~(~is_terminator (EL i h).po_inst.inst_opcode /\ _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     simp[Once ptr_chrono_step_cases] >> strip_tac >>
     gvs[ptr_observe_def] >>
     metis_tac[venomExecProofsTheory.step_inst_ok_terminator_jump,
               venomRetPropsTheory.step_inst_IntRet_opcode]) >>
  Cases_on `(EL i h).po_inst.inst_opcode = INVOKE`
  >- (
    `!name fn. lookup_function name C.ctx_functions = SOME fn ==>
       first_block_no_phi fn` by
      (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
       metis_tac[lookup_function_MEM]) >>
    `!name fn. lookup_function name C'.ctx_functions = SOME fn ==>
       first_block_no_phi fn` by
      (qpat_assum `ctx_pass_stage _ _ _ C C'` mp_tac >>
       qpat_assum `o1_ctx_shape C` mp_tac >>
       qpat_assum `EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
       `MEM fn C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
       qpat_x_assum `MEM fn C'.ctx_functions` mp_tac >>
       simp[MEM_EL] >> disch_then (qx_choose_then `j` strip_assume_tac) >>
       qpat_x_assum `ctx_pass_stage _ _ _ C C'` mp_tac >>
       simp[ctx_pass_stage_def, LIST_REL_EL_EQN] >> strip_tac >>
       qpat_x_assum `!n. n < _ ==> ?observed s out. _`
         (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
       `MEM (EL j C.ctx_functions) C.ctx_functions` by metis_tac[EL_MEM] >>
       `(EL j C.ctx_functions).fn_eom = NONE /\
        wf_function (EL j C.ctx_functions) /\
        first_block_no_preds (EL j C.ctx_functions) /\
        first_block_no_phi (EL j C.ctx_functions)` by
         fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
       gvs[fn_pass_step_def, execute_configured_fn_pass_concretize, AllCaseEqs()] >>
       drule_all concretize_function_fresh_positions >> strip_tac >>
       `first_block_no_phi (concretize_function_with_positions layout.cl_positions
                              (EL j C.ctx_functions))` by
         (irule (cj 2 concretize_positions_first_block) >> simp[]) >>
       fs[first_block_no_phi_def, apply_context_concretize_layout_def,
          apply_concretize_layout_def]) >>
    `(EL q ht).po_inst = (EL i h).po_inst` by
      simp[concretize_positions_unchanged] >>
    drule_all ptr_dalloca_runtime_chrono_call >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    qpat_assum `EL q done = i` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
    `!j. (j < lo \/ dyn_floor C vs <= j) /\
         j IN (EL (SUC q) ht).po_taint.t_mem ==>
         j IN (EL (SUC i) h).po_taint.t_mem` by
      (qpat_assum `!j. (j < lo \/ dyn_floor C vs <= j) ==> j IN _ ==> j IN _`
         mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
    `LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site)
       (EL (SUC i) h).po_params (EL (SUC q) ht).po_params` by
      (simp[NoAsms, LIST_REL_EL_EQN] >> (conj_tac >- first_assum ACCEPT_TAC) >>
       qpat_assum `!k site. k < LENGTH (EL (SUC i) h).po_params ==> _`
         mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
    `LIST_REL (\f ft.
       ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
         ft.cf_prov ft.cf_tvar ft.cf_state /\
       LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site) f.cf_params ft.cf_params)
       (EL (SUC i) h).po_stack (EL (SUC q) ht).po_stack` by
      (qpat_assum `(EL (SUC i) h).po_stack = _` SUBST1_TAC >>
       qpat_assum `(EL (SUC q) ht).po_stack = _` SUBST1_TAC >>
       simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
    conj_tac
    >- (simp[NoAsms, ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
    `LENGTH after_row5 = LENGTH (EL (SUC i) h).po_stack` by
      (qpat_assum `after_row5 = _` SUBST1_TAC >>
       qpat_assum `(EL (SUC i) h).po_stack = _` SUBST1_TAC >>
       simp[NoAsms] >> first_assum ACCEPT_TAC) >>
    `LIST_REL (\((pt,tg),f) ft.
       ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
         ft.cf_prov ft.cf_tvar ft.cf_state /\
       (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP tg v = NONE) /\
       (!v site. FLOOKUP tg v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
         FLOOKUP ft.cf_prov v = SOME site) /\
       f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs /\
       LENGTH pt = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
       (!k site. k < LENGTH f.cf_params ==>
         (EL k ft.cf_params = SOME site ==>
           EL k f.cf_params = SOME site /\ EL k pt = NONE /\
           EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
         (EL k pt = NONE /\ EL k f.cf_params = SOME site ==>
           EL k ft.cf_params = SOME site)))
       (ZIP (after_row5,(EL (SUC i) h).po_stack)) (EL (SUC q) ht).po_stack` by
      (qpat_assum `after_row5 = _` SUBST1_TAC >>
       qpat_assum `(EL (SUC i) h).po_stack = _` SUBST1_TAC >>
       qpat_assum `(EL (SUC q) ht).po_stack = _` SUBST1_TAC >>
       qpat_assum `(EL q ht).po_inst = (EL i h).po_inst`
         (fn th => simp[NoAsms, ZIP, th]) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    markerLib.asm_x "match_demand" mp_tac >> simp[] >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `i = EL q done` by (sym_tac >> first_assum ACCEPT_TAC) >>
  `((EL i h).po_inst.inst_opcode = INVOKE ==>
     LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
     (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name))` by simp[] >>
  drule_all (SRULE [] (Q.INST [`n` |-> `i`, `a` |-> `EL i h`,
    `at` |-> `EL q ht`, `b` |-> `EL (SUC i) h`, `bt` |-> `EL (SUC q) ht`]
    focus_cut_ghost_runtime_control)) >>
  qpat_assum `EL q done = i` (fn th =>
    disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [th])) >>
  qpat_assum `EL q done = i` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  `!j. (j < lo \/ dyn_floor C vs <= j) /\
       j IN (EL (SUC q) ht).po_taint.t_mem ==>
       j IN (EL (SUC i) h).po_taint.t_mem` by
    (qpat_assum `!j. (j < lo \/ dyn_floor C vs <= j) ==> j IN _ ==> j IN _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site)
     (EL (SUC i) h).po_params (EL (SUC q) ht).po_params` by
    (simp[NoAsms, LIST_REL_EL_EQN] >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `!k site. k < LENGTH (EL (SUC i) h).po_params ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `LIST_REL (\f ft.
     ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
       ft.cf_prov ft.cf_tvar ft.cf_state /\
     LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site) f.cf_params ft.cf_params)
     (EL (SUC i) h).po_stack (EL (SUC q) ht).po_stack` by
    (qpat_assum `LIST_REL _ (ZIP (after_row5,_)) _` mp_tac >>
     qpat_assum `LENGTH after_row5 = _` (fn th =>
       simp[NoAsms, LIST_REL_EL_EQN, th, LENGTH_ZIP, EL_ZIP]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> qx_gen_tac `k` >> strip_tac >>
     qpat_x_assum `!n. _` (qspec_then `k` mp_tac) >>
     impl_tac >- simp[] >>
     Cases_on `EL k after_row5` >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (simp[NoAsms, ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  markerLib.asm_x "match_demand" mp_tac >> simp[] >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem focus_concretize_cut_ghost_endpoint:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  alloca_frontier_upto n C vs /\ fixed_region_reserved lo C /\
  o1_safe_upto D lo n C vs /\ gas_cut n vs at.po_state /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done ==>
  ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY births
    (\token aid. F) endpoint at /\
  (!v site. FLOOKUP at.po_prov v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP endpoint.po_prov v = SOME site ==>
    FLOOKUP at.po_prov v = SOME site) /\
  LENGTH PT = LENGTH endpoint.po_params /\
  LENGTH endpoint.po_params = LENGTH at.po_params /\
  (!k site. k < LENGTH endpoint.po_params ==>
    (EL k at.po_params = SOME site ==>
      EL k endpoint.po_params = SOME site /\ EL k PT = NONE /\
      EL k endpoint.po_state.vs_params = EL k at.po_state.vs_params) /\
    (EL k PT = NONE /\ EL k endpoint.po_params = SOME site ==>
      EL k at.po_params = SOME site)) /\
  LENGTH saved = LENGTH endpoint.po_stack /\
  LIST_REL (\((pt,tg),f) ft.
    ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
      ft.cf_prov ft.cf_tvar ft.cf_state /\
    (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP tg v = NONE) /\
    (!v site. FLOOKUP tg v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
      FLOOKUP ft.cf_prov v = SOME site) /\
    f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs /\
    LENGTH pt = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
    (!k site. k < LENGTH f.cf_params ==>
      (EL k ft.cf_params = SOME site ==>
        EL k f.cf_params = SOME site /\ EL k pt = NONE /\
        EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
      (EL k pt = NONE /\ EL k f.cf_params = SOME site ==>
        EL k ft.cf_params = SOME site)))
    (ZIP (saved,endpoint.po_stack)) at.po_stack /\
  (!v token aid base size pos ix.
    ~in_revert_forward endpoint.po_fn endpoint.po_state /\
    endpoint.po_inst.inst_opcode <> ASSIGN /\
    MEM (Var v) endpoint.po_inst.inst_operands /\
    (inst_read_op endpoint.po_inst = SOME (Var v) \/
      endpoint.po_inst.inst_opcode = INVOKE) /\
    FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP endpoint.po_prov v = SOME (base,size) /\
    FLOOKUP births (token,aid) = SOME (base,size) /\
    FLOOKUP positions (Allocation aid) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN at.po_taint.t_mem ==> base+ix IN endpoint.po_taint.t_mem)
Proof
  disch_then (fn th =>
    mp_tac (MATCH_MP focus_concretize_cut_ghost_history th) >>
    map_every assume_tac (CONJUNCTS th)) >>
  disch_then (qspecl_then [`LENGTH h - 1`,`LENGTH done`] assume_tac) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_source >> disch_then (strip_assume_tac o MATCH_MP ptr_chrono_history_end) >>
  drule ptr_structural_trace_target >> disch_then (strip_assume_tac o MATCH_MP ptr_chrono_history_end) >>
  `done <> [] ==> EL (LENGTH done - 1) done < LENGTH h - 1` by
    (strip_tac >> `LENGTH done - 1 < LENGTH done` by simp[LENGTH_NON_NIL] >>
     qpat_assum `ptr_event_embedding h ht _`
       (qspecl_then [`LENGTH done - 1`,`LENGTH done`] mp_tac o
        cj 3 o REWRITE_RULE [ptr_event_embedding_def]) >>
     simp[EL_APPEND_EQN]) >>
  `LENGTH h - 1 < LENGTH h /\ PRE (LENGTH ht) = LENGTH done` by decide_tac >>
  `H <> []` by (strip_tac >> gvs[]) >>
  `EL (LENGTH h - 1) h = endpoint` by
    (qspec_then `h` mp_tac LAST_EL >> simp[PRE_SUB1]) >>
  `EL (LENGTH done) ht = at` by
    (qspec_then `ht` mp_tac LAST_EL >> simp[]) >>
  `EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (qspec_then `H` mp_tac LAST_EL >> simp[PRE_SUB1]) >>
  qpat_x_assum `_ ==> !tsj rj bj PTj TGj sj ej. _` mp_tac >>
  Cases_on `done = []` >> simp[EL_APPEND_EQN] >>
  disch_then (ACCEPT_TAC o List.last o CONJUNCTS)
QED
