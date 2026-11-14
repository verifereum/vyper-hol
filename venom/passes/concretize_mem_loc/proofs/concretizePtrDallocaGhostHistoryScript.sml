Theory concretizePtrDallocaGhostHistory
Ancestors
  concretizePtrDallocaRuntimeHistory concretizePtrDallocaMemorySteps
  concretizePtrDallocaActualWrites concretizeStepStructure
  opcodeClass callLayoutDefs venomExecProofs
  concretizePtrDallocaRuntimeBlockHistory concretizePtrDallocaRuntimeControl
  concretizePtrDallocaChronologyProbe concretizePtrDallocaHistoricalRead
  concretizePtrPairedRoot concretizePtrParamShape concretizePtrOwnershipErasure
  concretizePtrSourceOwnership concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrEventEmbedding
  concretizePtrPairedPrefix concretizePtrChronologicalHistory
  concretizePtrDallocaGhostInterface ptrDiscipline venomState venomInst
  frameAllocationOwnership venomExecSemantics venomWf o1PassContract contextCodegenRel
  list rich_list finite_map pred_set arithmetic

Theorem ptr_dalloca_ghost_history:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  EVERY (\n. ~in_revert_forward (EL n h).po_fn (EL n h).po_state) done ==>
  !n q.
    n < LENGTH h /\ q <= LENGTH done /\
    (q = 0 \/ EL (q-1) done < n) /\
    n <= EL q (done ++ [LENGTH h - 1]) ==>
    !tsj rj bj PTj TGj sj ej. EL n H = (tsj,rj,bj,PTj,TGj,sj,ej) ==>
    ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY bj
      (\token aid. F) (EL n h) (EL q ht) /\
    (!v site. FLOOKUP (EL q ht).po_prov v = SOME site ==>
      FLOOKUP TGj v = NONE) /\
    (!v site. FLOOKUP TGj v = NONE /\
      FLOOKUP (EL n h).po_prov v = SOME site ==>
      FLOOKUP (EL q ht).po_prov v = SOME site) /\
    LENGTH PTj = LENGTH (EL n h).po_params /\
    LENGTH (EL n h).po_params = LENGTH (EL q ht).po_params /\
    (!k site. k < LENGTH (EL n h).po_params ==>
      (EL k (EL q ht).po_params = SOME site ==>
        EL k (EL n h).po_params = SOME site /\ EL k PTj = NONE /\
        EL k (EL n h).po_state.vs_params =
          EL k (EL q ht).po_state.vs_params) /\
      (EL k PTj = NONE /\ EL k (EL n h).po_params = SOME site ==>
        EL k (EL q ht).po_params = SOME site)) /\
    LENGTH sj = LENGTH (EL n h).po_stack /\
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
      (ZIP (sj,(EL n h).po_stack)) (EL q ht).po_stack /\
    (!v token aid base size pos ix.
      ~in_revert_forward (EL n h).po_fn (EL n h).po_state /\
      (EL n h).po_inst.inst_opcode <> ASSIGN /\
      MEM (Var v) (EL n h).po_inst.inst_operands /\
      (inst_read_op (EL n h).po_inst = SOME (Var v) \/
        (EL n h).po_inst.inst_opcode = INVOKE) /\
      FLOOKUP TGj v = SOME (token,aid) /\
      FLOOKUP (EL n h).po_prov v = SOME (base,size) /\
      FLOOKUP bj (token,aid) = SOME (base,size) /\
      FLOOKUP positions (Allocation aid) = SOME (pos,size) /\ ix < size ==>
      pos+ix IN (EL q ht).po_taint.t_mem ==>
        base+ix IN (EL n h).po_taint.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  (fn g =>
    let
      val (n,body) = dest_forall (snd g)
      val (q,body) = dest_forall body
      val (_,invariant) = dest_imp body
      val predicate = mk_abs (n,mk_abs (q,invariant))
      val rule = INST [``P:num -> num -> bool`` |-> predicate,
        ``ht:ptr_observation list`` |-> ``ht:ptr_observation list``]
        ptr_event_embedding_source_induction
    in MATCH_MP_TAC (BETA_RULE rule) g end) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `ptr_chrono_history vs C [EL 0 h] (EL 0 h)` by
        (qpat_x_assum `ptr_chrono_history vs C h endpoint`
           (mp_tac o MATCH_MP ptr_chrono_history_prefix) >>
         disch_then (qspec_then `0` mp_tac) >> Cases_on `h` >>
         fs[ptr_paired_samples_def, ptr_sample_list_def]) >>
      `ptr_chrono_history vs C' [EL 0 ht] (EL 0 ht)` by
        (qpat_x_assum `ptr_chrono_history vs C' ht at`
           (mp_tac o MATCH_MP ptr_chrono_history_prefix) >>
         disch_then (qspec_then `0` mp_tac) >> Cases_on `ht` >>
         fs[ptr_paired_samples_def, ptr_sample_list_def]) >>
      `ptr_source_ownership vs C [EL 0 h] (EL 0 h) tsj rj bj PTj TGj sj` by
        (qpat_x_assum `ptr_structural_transcript R vs C C' h endpoint ht at done
           tokens registry births PT TG saved entries H`
           (mp_tac o MATCH_MP ptr_structural_transcript_ownership) >>
         disch_then (qspec_then `0` mp_tac) >>
         Cases_on `h` >> fs[ptr_paired_samples_def, ptr_sample_list_def,
                           ptr_snapshot_ownership_def]) >>
      drule o1_ctx_shape_instructions_wf >> strip_tac >>
      drule_all ptr_source_ownership_params_erases >> strip_tac >>
      drule ptr_source_ownership_stack_length >> strip_tac >>
      qpat_x_assum `ptr_chrono_history vs C [EL 0 h] (EL 0 h)`
        (strip_assume_tac o MATCH_MP ptr_chrono_root_inversion) >>
      qpat_x_assum `ptr_chrono_history vs C' [EL 0 ht] (EL 0 ht)`
        (strip_assume_tac o MATCH_MP ptr_chrono_root_inversion) >>
      gvs[ptr_observe_def, ptr_observation_component_equality, ptr_params_erases_def,
          ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def,
          ptr_dalloca_ghost_vars_def, entry_taint_def, op_taint_def]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `snapshot = EL n H` >> PairCases_on `snapshot` >>
  qpat_assum `!j r. j <= n /\ _ ==> _`
    (qspecl_then [`n`,`q`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then
    [`snapshot0`,`snapshot1`,`snapshot2`,`snapshot3`,
     `snapshot4`,`snapshot5`,`snapshot6`] mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!j r. j < SUC n /\ r < LENGTH done /\ EL r done = j ==>
    j <= n /\ r <= LENGTH done /\
    (r = 0 \/ EL (r-1) done < j) /\
    j <= EL r (done ++ [LENGTH h - 1])` by
    (rpt gen_tac >> strip_tac >> rpt conj_tac
     >- decide_tac
     >- decide_tac
     >- (Cases_on `r = 0` >> simp[] >>
         qpat_assum `ptr_event_embedding h ht (done ++ [LENGTH h - 1])`
           (mp_tac o REWRITE_RULE [ptr_event_embedding_def]) >>
         disch_then (mp_tac o List.last o CONJUNCTS) >>
         disch_then (qspecl_then [`r-1`,`r`] mp_tac) >>
         simp[EL_APPEND_EQN] >> decide_tac) >>
     simp[EL_APPEND_EQN]) >>

  `!j r. j < SUC n /\ r < LENGTH done /\ EL r done = j ==>
    ptr_dalloca_ghost_vars
      (EL j h).po_prov (EL j h).po_taint.t_var (EL j h).po_state
      (EL r ht).po_prov (EL r ht).po_taint.t_var (EL r ht).po_state /\
    (!a. (a < lo \/ dyn_floor C vs <= a) /\
      a IN (EL r ht).po_taint.t_mem ==>
      a IN (EL j h).po_taint.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `j <= n /\ r <= LENGTH done /\
      (r = 0 \/ EL (r-1) done < j) /\
      j <= EL r (done ++ [LENGTH h - 1])` by
       (qpat_assum `!j r. j < SUC n /\ _ ==> j <= n /\ _`
          (qspecl_then [`j`,`r`] mp_tac) >> simp[]) >>
     qabbrev_tac `hist = EL j H` >> PairCases_on `hist` >>
     qpat_assum `!j r. j <= n /\ _ ==> _`
       (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qspecl_then
       [`hist0`,`hist1`,`hist2`,`hist3`,`hist4`,`hist5`,`hist6`] mp_tac) >>
     (impl_tac >- fs[]) >>
     disch_then (fn th =>
       let
         val sample = CONJUNCT1 th
         val compare = CONJUNCT1
           (REWRITE_RULE [ptr_dalloca_ghost_sample_def] sample)
         val fields = CONJUNCTS
           (REWRITE_RULE [ptr_dalloca_ghost_compare_def] compare)
       in
         ACCEPT_TAC (CONJ (hd fields) (List.nth (fields,4)))
       end)) >>

  `!j r op. j < SUC n /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET
      op_taint (EL j h).po_taint op` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!j r. j < SUC n /\ _ ==> ptr_dalloca_ghost_vars _ _ _ _ _ _ /\ _`
       (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (assume_tac o CONJUNCT1) >>
     Cases_on `op` >> simp[op_taint_def] >>
     qpat_x_assum `ptr_dalloca_ghost_vars _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [ptr_dalloca_ghost_vars_def]) >>
     simp[op_taint_def, entry_taint_def] >>
     disch_then (MATCH_ACCEPT_TAC o SPEC_ALL)) >>

  `!j r a. j < SUC n /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!j r. j < SUC n /\ _ ==> ptr_dalloca_ghost_vars _ _ _ _ _ _ /\ _`
       (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_tac o Q.SPEC `a` o CONJUNCT2) >> simp[]) >>

  `!j r a. j < SUC n /\ r < LENGTH done /\ EL r done = j /\
    dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!j r. j < SUC n /\ _ ==> ptr_dalloca_ghost_vars _ _ _ _ _ _ /\ _`
       (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_tac o Q.SPEC `a` o CONJUNCT2) >> simp[]) >>

  `!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < SUC n /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/
      (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==>
      base+ix IN (EL j h).po_taint.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `j <= n /\ r <= LENGTH done /\
      (r = 0 \/ EL (r-1) done < j) /\
      j <= EL r (done ++ [LENGTH h - 1])` by
       (qpat_assum `!j r. j < SUC n /\ _ ==> j <= n /\ _`
          (qspecl_then [`j`,`r`] mp_tac) >> simp[]) >>
     qpat_assum `!j r. j <= n /\ _ ==> _`
       (qspecl_then [`j`,`r`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qspecl_then [`ts`,`rw`,`bw`,`PTw`,`TGw`,`sw`,`ew`] mp_tac) >>
     (impl_tac >- simp[]) >>
     rename1 `FLOOKUP bw (tok,id) = SOME (owned_base,owned_size)` >>
     disch_then (fn th =>
       mp_tac (Q.SPECL [`u`,`tok`,`id`,`owned_base`,`owned_size`,`pos`,`ix`]
         (List.last (CONJUNCTS th)))) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     simp[]) >>

  qpat_x_assum `!j r. j <= n /\ _ ==> _` (K ALL_TAC) >>
  drule ptr_structural_transcript_adjacent >>
  disch_then (qspec_then `n` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qabbrev_tac `nextsnapshot = EL (SUC n) H` >> PairCases_on `nextsnapshot` >>
  qpat_assum `Abbrev (_ = EL n H)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (_ = EL (SUC n) H)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `ptr_snapshot_step _ _ _ _ _ _` mp_tac >>
  asm_rewrite_tac[ptr_snapshot_step_def] >> strip_tac >>
  `!r. r <= LENGTH done /\
    (r = 0 \/ EL (r-1) done < SUC n) /\
    SUC n <= EL r (done ++ [LENGTH h - 1]) ==>
    !ts rw bw PTw TGw sw ew. EL (SUC n) H = (ts,rw,bw,PTw,TGw,sw,ew) ==>
    !u tok id rb sz pos ix.
      ~in_revert_forward (EL (SUC n) h).po_fn (EL (SUC n) h).po_state /\
      (EL (SUC n) h).po_inst.inst_opcode <> ASSIGN /\
      MEM (Var u) (EL (SUC n) h).po_inst.inst_operands /\
      (inst_read_op (EL (SUC n) h).po_inst = SOME (Var u) \/
       (EL (SUC n) h).po_inst.inst_opcode = INVOKE) /\
      FLOOKUP TGw u = SOME (tok,id) /\
      FLOOKUP (EL (SUC n) h).po_prov u = SOME (rb,sz) /\
      FLOOKUP bw (tok,id) = SOME (rb,sz) /\
      FLOOKUP positions (Allocation id) = SOME (pos,sz) /\ ix < sz ==>
      pos+ix IN (EL r ht).po_taint.t_mem ==>
        rb+ix IN (EL (SUC n) h).po_taint.t_mem` by
    (qx_gen_tac `front_r` >> disch_then (map_every assume_tac o CONJUNCTS) >>
     map_every qx_gen_tac [`front_ts`,`front_rw`,`front_bw`,`front_PT`,
       `front_TG`,`front_saved`,`front_entries`] >> disch_tac >>
     map_every qx_gen_tac [`read_u`,`read_token`,`read_id`,`read_base`,
       `read_size`,`read_pos`,`read_ix`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`i` |-> `SUC n`, `q` |-> `front_r`,
       `ts0` |-> `front_ts`, `rw0` |-> `front_rw`, `bw0` |-> `front_bw`,
       `PT0` |-> `front_PT`, `TG0` |-> `front_TG`, `sv0` |-> `front_saved`,
       `en0` |-> `front_entries`, `v` |-> `read_u`, `token` |-> `read_token`,
       `aid` |-> `read_id`, `b` |-> `read_base`, `sz` |-> `read_size`,
       `pa` |-> `read_pos`, `k` |-> `read_ix`]
       ptr_dalloca_frontier_demanded_reflection) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `ptr_chrono_step C (EL n h) (EL (SUC n) h)` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  `!r s. r < s /\ s < LENGTH done ==> EL r done < EL s done` by
    (rpt strip_tac >>
     qpat_assum `ptr_event_embedding h ht (done ++ [LENGTH h - 1])`
       (mp_tac o REWRITE_RULE [ptr_event_embedding_def]) >>
     disch_then (mp_tac o List.last o CONJUNCTS) >>
     disch_then (qspecl_then [`r`,`s`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  reverse conj_tac
  >~ [`q = LENGTH done \/ n < EL q done`]
  >- (disch_tac >>
    `~MEM n done` by
      (CCONTR_TAC >>
       `?r. r < LENGTH done /\ EL r done = n` by metis_tac[MEM_EL] >>
       pop_assum strip_assume_tac >> Cases_on `r < q`
       >- (`0 < q /\ r <= q-1` by decide_tac >>
           Cases_on `r = q-1` >- gvs[] >>
           `r < q-1 /\ q-1 < LENGTH done` by decide_tac >>
           `EL r done < EL (q-1) done` by metis_tac[] >>
           gvs[] >> decide_tac) >>
       `q <= r /\ q < LENGTH done` by decide_tac >>
       `n < EL q done` by metis_tac[] >>
       Cases_on `r = q` >- gvs[] >>
       `q < r` by decide_tac >>
       `EL q done < EL r done` by metis_tac[] >> decide_tac) >>
    `(EL n h).po_inst.inst_opcode = NOP` by
      (drule ptr_structural_trace_unmatched_nop >>
       disch_then (qspec_then `n` mp_tac) >> simp[] >> decide_tac) >>
    `active_inst (EL n h).po_fn (EL n h).po_inst (EL n h).po_state` by
      (qpat_assum `ptr_chrono_step C (EL n h) (EL (SUC n) h)` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >>
       simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
       gvs[ptr_observe_def]) >>
    `MEM (EL n h).po_fn C.ctx_functions /\
     MEM (EL n h).po_inst (fn_insts (EL n h).po_fn)` by
      (conj_tac
       >- (qpat_assum `ptr_chrono_history vs C h endpoint`
             (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
           simp[EVERY_EL] >> strip_tac >>
           `ptr_observation_reachable vs C (EL n h)` by
             (first_x_assum irule >> decide_tac) >>
           fs[ptr_observation_reachable_def] >>
           drule frame_reachable_functions_member >> simp[]) >>
       fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
       metis_tac[MEM_EL]) >>
    `(EL n h).po_inst.inst_outputs = []` by
      (drule o1_ctx_shape_instructions_wf >>
       simp[EVERY_MEM] >> strip_tac >>
       `inst_wf (EL n h).po_inst` by metis_tac[] >>
       qpat_x_assum `inst_wf (EL n h).po_inst` mp_tac >>
       qpat_assum `(EL n h).po_inst.inst_opcode = NOP`
         (fn th => simp[inst_wf_def, th])) >>
    drule_all ptr_tagged_chrono_step_nop >> strip_tac >>
    drule_all ptr_dalloca_nop_observation >> strip_tac >>
    `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY snapshot2
      (\token aid. F) (EL (SUC n) h) (EL q ht)` by
      (mp_tac (Q.INST [`a` |-> `EL n h`, `b` |-> `EL (SUC n) h`,
        `at` |-> `EL q ht`, `births` |-> `snapshot2`,
        `registry` |-> `FEMPTY : (num,ptr_ledger_activation) fmap`,
        `live` |-> `\token aid. F`, `dyn` |-> `dyn_floor C vs`]
        ptr_dalloca_nop_ghost_sample) >>
       (impl_tac >- asm_rewrite_tac[]) >>
       disch_then (fn th => MATCH_MP_TAC (iffLR th)) >>
       first_assum ACCEPT_TAC) >>
    `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
      (\token aid. F) (EL (SUC n) h) (EL q ht)` by
      (qpat_assum `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY snapshot2
         (\token aid. F) (EL (SUC n) h) (EL q ht)` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >>
       simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
       strip_tac >> first_assum ACCEPT_TAC) >>
    `q = 0 \/ EL (q-1) done < SUC n` by decide_tac >>
    `SUC n <= EL q (done ++ [LENGTH h - 1])` by
      (qpat_assum `SUC n < LENGTH h` mp_tac >>
       qpat_assum `q <= LENGTH done` mp_tac >>
       qpat_assum `q = LENGTH done \/ n < EL q done` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
       Cases_on `q = LENGTH done` >> fs[EL_APPEND_EQN] >> decide_tac) >>
    qpat_assum `!r. r <= LENGTH done /\ _ ==> _`
      (qspec_then `q` mp_tac) >>
    (impl_tac >- asm_rewrite_tac[]) >>
    disch_then (qspecl_then [`nextsnapshot0`,`nextsnapshot1`,`nextsnapshot2`,
      `nextsnapshot3`,`nextsnapshot4`,`nextsnapshot5`,`nextsnapshot6`] mp_tac) >>
    (impl_tac >- fs[]) >> disch_tac >>
    map_every qx_gen_tac [`post_ts`,`post_rw`,`post_births`,`post_PT`,
      `post_TG`,`post_saved`,`post_entries`] >>
    qpat_assum `EL (SUC n) H = (nextsnapshot0,nextsnapshot1,nextsnapshot2,
      nextsnapshot3,nextsnapshot4,nextsnapshot5,nextsnapshot6)`
      (fn th => rewrite_tac[th, pairTheory.PAIR_EQ]) >>
    disch_then (map_every SUBST_ALL_TAC o map SYM o CONJUNCTS) >>
    qpat_assum `LIST_REL _ (ZIP (snapshot5,(EL n h).po_stack))
      (EL q ht).po_stack` mp_tac >>
    qpat_assum `!u tok id rb sz pos ix.
      ~in_revert_forward (EL (SUC n) h).po_fn (EL (SUC n) h).po_state /\ _ ==> _`
      mp_tac >>
    qpat_assum `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
      (\token aid. F) (EL (SUC n) h) (EL q ht)` mp_tac >>
    qpat_assum `!v site. FLOOKUP (EL q ht).po_prov v = SOME site ==> _` mp_tac >>
    qpat_assum `!v site. FLOOKUP snapshot4 v = NONE /\ _ ==> _` mp_tac >>
    qpat_assum `!k site. k < LENGTH (EL n h).po_params ==> _` mp_tac >>
    qpat_assum `LENGTH snapshot3 = LENGTH (EL n h).po_params` mp_tac >>
    qpat_assum `LENGTH (EL n h).po_params = LENGTH (EL q ht).po_params` mp_tac >>
    qpat_assum `LENGTH snapshot5 = LENGTH (EL n h).po_stack` mp_tac >>
    qpat_assum `nextsnapshot3 = snapshot3` mp_tac >>
    qpat_assum `nextsnapshot4 = snapshot4` mp_tac >>
    qpat_assum `nextsnapshot5 = snapshot5` mp_tac >>
    qpat_assum `(EL (SUC n) h).po_params = (EL n h).po_params` mp_tac >>
    qpat_assum `(EL (SUC n) h).po_prov = (EL n h).po_prov` mp_tac >>
    qpat_assum `(EL (SUC n) h).po_taint = (EL n h).po_taint` mp_tac >>
    qpat_assum `(EL (SUC n) h).po_stack = (EL n h).po_stack` mp_tac >>
    qpat_assum `(EL (SUC n) h).po_state = _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[] >>
    map_every qx_gen_tac [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
      `owned_size`,`owned_pos`,`owned_ix`] >>
    qpat_assum `!u tok id rb sz pos ix. _`
      (qspecl_then [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
        `owned_size`,`owned_pos`,`owned_ix`] mp_tac) >> simp[ADD_COMM])
  >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  `ptr_chrono_step C' (EL q ht) (EL (SUC q) ht)` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (mp_tac o MATCH_MP concretizePtrLifetimeTheory.ptr_chrono_history_adjacent) >>
     disch_then (qspec_then `q` mp_tac) >> simp[]) >>
  `~in_revert_forward (EL n h).po_fn (EL n h).po_state` by
    (qpat_assum `EVERY (\j. ~in_revert_forward _ _) done`
       (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `q` mp_tac) >> BETA_TAC >> asm_rewrite_tac[]) >>
  `SUC q <= LENGTH done` by decide_tac >>
  `EL q done < SUC n` by simp[] >>
  `SUC n <= EL (SUC q) (done ++ [LENGTH h - 1])` by
    (drule ptr_structural_trace_nop_interval >>
     disch_then (qspec_then `q` mp_tac) >> simp[]) >>
  qpat_assum `!r. r <= LENGTH done /\ _ ==> _`
    (qspec_then `SUC q` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`nextsnapshot0`,`nextsnapshot1`,`nextsnapshot2`,
    `nextsnapshot3`,`nextsnapshot4`,`nextsnapshot5`,`nextsnapshot6`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  qpat_assum `ptr_dalloca_ghost_sample _ _ _ _ _ (EL n h) (EL q ht)`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def]) >>
  `!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL n h).po_taint op` by
    (gen_tac >> Cases_on `op` >> simp[op_taint_def] >>
     qpat_assum `ptr_dalloca_ghost_vars _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE[ptr_dalloca_ghost_vars_def]) >>
     simp[op_taint_def, entry_taint_def] >>
     disch_then (MATCH_ACCEPT_TAC o SPEC_ALL)) >>
  `!i. i < lo ==> i IN (EL q ht).po_taint.t_mem ==>
    i IN (EL n h).po_taint.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!i. (i < lo \/ _) /\ _ ==> _` irule >> simp[]) >>
  `!i. dyn_floor C vs <= i ==> i IN (EL q ht).po_taint.t_mem ==>
    i IN (EL n h).po_taint.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!i. (i < lo \/ _) /\ _ ==> _` irule >> simp[]) >>
  `!j r op. j < n /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET
      op_taint (EL j h).po_taint op` by
    (map_every qx_gen_tac [`prior_j`,`prior_r`,`prior_op`] >>
     strip_tac >>
     qpat_assum `!j r op. j < SUC n /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET
      op_taint (EL j h).po_taint op`
       (qspecl_then [`prior_j`,`prior_r`,`prior_op`] mp_tac) >>
     (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>

  `!j r a. j < n /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem` by
    (map_every qx_gen_tac [`prior_j`,`prior_r`,`prior_a`] >>
     strip_tac >>
     qpat_assum `!j r a. j < SUC n /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem`
       (qspecl_then [`prior_j`,`prior_r`,`prior_a`] mp_tac) >>
     (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>

  `!j r a. j < n /\ r < LENGTH done /\ EL r done = j /\
    dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem` by
    (map_every qx_gen_tac [`prior_j`,`prior_r`,`prior_a`] >>
     strip_tac >>
     qpat_assum `!j r a. j < SUC n /\ r < LENGTH done /\ EL r done = j /\
    dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem`
       (qspecl_then [`prior_j`,`prior_r`,`prior_a`] mp_tac) >>
     (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>

  `!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < n /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/
      (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==>
      base+ix IN (EL j h).po_taint.t_mem` by
    (map_every qx_gen_tac [`prior_j`,`prior_r`,`prior_u`,`prior_tok`,`prior_id`,`prior_base`,`prior_size`,`prior_pos`,`prior_ix`,`prior_ts`,`prior_rw`,`prior_bw`,`prior_PTw`,`prior_TGw`,`prior_sw`,`prior_ew`] >>
     strip_tac >>
     qpat_assum `!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < SUC n /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/
      (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==>
      base+ix IN (EL j h).po_taint.t_mem`
       (qspecl_then [`prior_j`,`prior_r`,`prior_u`,`prior_tok`,`prior_id`,`prior_base`,`prior_size`,`prior_pos`,`prior_ix`,`prior_ts`,`prior_rw`,`prior_bw`,`prior_PTw`,`prior_TGw`,`prior_sw`,`prior_ew`] mp_tac) >>
     (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`n0` |-> `n`] ptr_dalloca_memory_steps) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. (i < lo \/ dyn_floor C vs <= i) /\
    i IN (EL (SUC q) ht).po_taint.t_mem ==>
    i IN (EL (SUC n) h).po_taint.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!i. i < lo \/ dyn_floor C vs <= i ==> _ ==> _` irule >>
     asm_rewrite_tac[]) >>
  Cases_on `~is_terminator (EL n h).po_inst.inst_opcode /\
    (EL n h).po_inst.inst_opcode <> INVOKE`
  >- (qpat_x_assum `~is_terminator (EL n h).po_inst.inst_opcode /\ _`
        strip_assume_tac >>
      mp_tac (Q.INST [`n0` |-> `n`, `a` |-> `EL n h`, `t` |-> `EL q ht`,
        `token` |-> `HD snapshot0`, `tsj` |-> `snapshot0`, `rj` |-> `snapshot1`,
        `bj` |-> `snapshot2`, `PTj` |-> `snapshot3`, `TGj` |-> `snapshot4`,
        `sj` |-> `snapshot5`, `ej` |-> `snapshot6`,
        `PTnext` |-> `nextsnapshot3`, `TGnext` |-> `nextsnapshot4`,
        `savednext` |-> `nextsnapshot5`] ptr_dalloca_historical_runtime_next) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
        (\token aid. F) (EL (SUC n) h) (EL (SUC q) ht)` by
        (simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
         first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`post_ts`,`post_rw`,`post_births`,`post_PT`,
        `post_TG`,`post_saved`,`post_entries`] >>
      qpat_assum `EL (SUC n) H = (nextsnapshot0,nextsnapshot1,nextsnapshot2,
        nextsnapshot3,nextsnapshot4,nextsnapshot5,nextsnapshot6)`
        (fn th => rewrite_tac[th, pairTheory.PAIR_EQ]) >>
      disch_then (map_every SUBST_ALL_TAC o map SYM o CONJUNCTS) >>
      qpat_assum `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
        (\token aid. F) (EL (SUC n) h) (EL (SUC q) ht)` mp_tac >>
      qpat_assum `!v site. FLOOKUP (EL (SUC q) ht).po_prov v = SOME site ==> _` mp_tac >>
      qpat_assum `!v site. FLOOKUP nextsnapshot4 v = NONE /\
        FLOOKUP (EL (SUC n) h).po_prov v = SOME site ==> _` mp_tac >>
      qpat_assum `!u tok id rb sz pos ix.
        ~in_revert_forward (EL (SUC n) h).po_fn (EL (SUC n) h).po_state /\ _ ==> _` mp_tac >>
      qpat_assum `!k site. k < LENGTH (EL n h).po_params ==> _` mp_tac >>
      qpat_assum `LENGTH snapshot3 = LENGTH (EL n h).po_params` mp_tac >>
      qpat_assum `LENGTH (EL n h).po_params = LENGTH (EL q ht).po_params` mp_tac >>
      qpat_assum `LENGTH snapshot5 = LENGTH (EL n h).po_stack` mp_tac >>
      qpat_assum `LIST_REL _ (ZIP (snapshot5,(EL n h).po_stack))
        (EL q ht).po_stack` mp_tac >>
      qpat_assum `nextsnapshot3 = snapshot3` mp_tac >>
      qpat_assum `nextsnapshot5 = snapshot5` mp_tac >>
      qpat_assum `(EL (SUC n) h).po_params = (EL n h).po_params` mp_tac >>
      qpat_assum `(EL (SUC q) ht).po_params = (EL q ht).po_params` mp_tac >>
      qpat_assum `(EL (SUC n) h).po_stack = (EL n h).po_stack` mp_tac >>
      qpat_assum `(EL (SUC q) ht).po_stack = (EL q ht).po_stack` mp_tac >>
      qpat_assum `(EL (SUC n) h).po_state.vs_params = (EL n h).po_state.vs_params` mp_tac >>
      qpat_assum `(EL (SUC q) ht).po_state.vs_params = (EL q ht).po_state.vs_params` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[] >>
      map_every qx_gen_tac [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
        `owned_size`,`owned_pos`,`owned_ix`] >>
      qpat_assum `!u tok id rb sz pos ix. _`
        (qspecl_then [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
          `owned_size`,`owned_pos`,`owned_ix`] mp_tac) >> simp[ADD_COMM]) >>

  Cases_on `(EL n h).po_inst.inst_opcode = JMP \/
    (EL n h).po_inst.inst_opcode = JNZ \/
    (EL n h).po_inst.inst_opcode = DJMP`
  >- (mp_tac (Q.INST [`Ct` |-> `C'`, `n0` |-> `n`,
        `ts0` |-> `snapshot0`, `rw0` |-> `snapshot1`, `bw0` |-> `snapshot2`,
        `PT0` |-> `snapshot3`, `TG0` |-> `snapshot4`, `sv0` |-> `snapshot5`,
        `en0` |-> `snapshot6`, `PT'` |-> `nextsnapshot3`,
        `TG'` |-> `nextsnapshot4`, `saved'` |-> `nextsnapshot5`]
        ptr_dalloca_historical_runtime_block) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
        (\token aid. F) (EL (SUC n) h) (EL (SUC q) ht)` by
        (simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
         first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`post_ts`,`post_rw`,`post_births`,`post_PT`,
        `post_TG`,`post_saved`,`post_entries`] >>
      qpat_assum `EL (SUC n) H = (nextsnapshot0,nextsnapshot1,nextsnapshot2,
        nextsnapshot3,nextsnapshot4,nextsnapshot5,nextsnapshot6)`
        (fn th => rewrite_tac[th, pairTheory.PAIR_EQ]) >>
      disch_then (map_every SUBST_ALL_TAC o map SYM o CONJUNCTS) >>
      qpat_assum `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
        (\token aid. F) (EL (SUC n) h) (EL (SUC q) ht)` mp_tac >>
      qpat_assum `!v site. FLOOKUP (EL (SUC q) ht).po_prov v = SOME site ==> _` mp_tac >>
      qpat_assum `!v site. FLOOKUP nextsnapshot4 v = NONE /\
        FLOOKUP (EL (SUC n) h).po_prov v = SOME site ==> _` mp_tac >>
      qpat_assum `!u tok id rb sz pos ix.
        ~in_revert_forward (EL (SUC n) h).po_fn (EL (SUC n) h).po_state /\ _ ==> _` mp_tac >>
      qpat_assum `!k site. k < LENGTH (EL n h).po_params ==> _` mp_tac >>
      qpat_assum `LENGTH snapshot3 = LENGTH (EL n h).po_params` mp_tac >>
      qpat_assum `LENGTH (EL n h).po_params = LENGTH (EL q ht).po_params` mp_tac >>
      qpat_assum `LENGTH snapshot5 = LENGTH (EL n h).po_stack` mp_tac >>
      qpat_assum `LIST_REL _ (ZIP (snapshot5,(EL n h).po_stack))
        (EL q ht).po_stack` mp_tac >>
      qpat_assum `nextsnapshot3 = snapshot3` mp_tac >>
      qpat_assum `nextsnapshot5 = snapshot5` mp_tac >>
      qpat_assum `(EL (SUC n) h).po_params = (EL n h).po_params` mp_tac >>
      qpat_assum `(EL (SUC q) ht).po_params = (EL q ht).po_params` mp_tac >>
      qpat_assum `(EL (SUC n) h).po_stack = (EL n h).po_stack` mp_tac >>
      qpat_assum `(EL (SUC q) ht).po_stack = (EL q ht).po_stack` mp_tac >>
      qpat_assum `(EL (SUC n) h).po_state.vs_params = (EL n h).po_state.vs_params` mp_tac >>
      qpat_assum `(EL (SUC q) ht).po_state.vs_params = (EL q ht).po_state.vs_params` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[] >>
      map_every qx_gen_tac [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
        `owned_size`,`owned_pos`,`owned_ix`] >>
      qpat_assum `!u tok id rb sz pos ix. _`
        (qspecl_then [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
          `owned_size`,`owned_pos`,`owned_ix`] mp_tac) >> simp[ADD_COMM]) >>
  Cases_on `(EL n h).po_inst.inst_opcode = INVOKE`
  >- (mp_tac (Q.INST [`a` |-> `EL n h`, `t` |-> `EL q ht`]
        concretizePtrDallocaActualWritesTheory.ptr_dalloca_actual_event_context) >>
      (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
      `(EL q ht).po_inst = (EL n h).po_inst` by
        (qpat_assum `(EL q ht).po_inst = concretize_inst_with_positions _ _` mp_tac >>
         simp[concretizeStepStructureTheory.concretize_positions_unchanged]) >>
      mp_tac (Q.INST [`a` |-> `EL n h`, `at` |-> `EL q ht`,
        `b` |-> `EL (SUC n) h`, `bt` |-> `EL (SUC q) ht`,
        `endpoint_t` |-> `at`, `tsj` |-> `snapshot0`, `rj` |-> `snapshot1`,
        `bj` |-> `snapshot2`, `PTj` |-> `snapshot3`, `TGj` |-> `snapshot4`,
        `sj` |-> `snapshot5`, `ej` |-> `snapshot6`,
        `PTj'` |-> `nextsnapshot3`, `TGj'` |-> `nextsnapshot4`,
        `sj'` |-> `nextsnapshot5`] ptr_dalloca_historical_runtime_call) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site)
        (EL (SUC n) h).po_params (EL (SUC q) ht).po_params` by
        (pure_rewrite_tac[LIST_REL_EL_EQN] >> BETA_TAC >> conj_tac
         >- first_assum ACCEPT_TAC >>
         qx_gen_tac `pg_index` >> disch_tac >>
         qx_gen_tac `pg_site` >> disch_tac >>
         qpat_assum `!k site. k < LENGTH (EL (SUC n) h).po_params ==> _`
           (qspecl_then [`pg_index`,`pg_site`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
      `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
        (\token aid. F) (EL (SUC n) h) (EL (SUC q) ht)` by
        (simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
         first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`post_ts`,`post_rw`,`post_births`,`post_PT`,
        `post_TG`,`post_saved`,`post_entries`] >>
      qpat_assum `EL (SUC n) H = (nextsnapshot0,nextsnapshot1,nextsnapshot2,
        nextsnapshot3,nextsnapshot4,nextsnapshot5,nextsnapshot6)`
        (fn th => rewrite_tac[th, pairTheory.PAIR_EQ]) >>
      disch_then (map_every SUBST_ALL_TAC o map SYM o CONJUNCTS) >>
      qpat_assum `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
        (\token aid. F) (EL (SUC n) h) (EL (SUC q) ht)` mp_tac >>
      qpat_assum `!v site. FLOOKUP (EL (SUC q) ht).po_prov v = SOME site ==> _` mp_tac >>
      qpat_assum `!v site. FLOOKUP nextsnapshot4 v = NONE /\
        FLOOKUP (EL (SUC n) h).po_prov v = SOME site ==> _` mp_tac >>
      qpat_assum `!u tok id rb sz pos ix.
        ~in_revert_forward (EL (SUC n) h).po_fn (EL (SUC n) h).po_state /\ _ ==> _` mp_tac >>
      qpat_assum `LENGTH nextsnapshot3 = LENGTH (EL (SUC n) h).po_params` mp_tac >>
      qpat_assum `LENGTH (EL (SUC n) h).po_params = LENGTH (EL (SUC q) ht).po_params` mp_tac >>
      qpat_assum `!k site. k < LENGTH (EL (SUC n) h).po_params ==> _` mp_tac >>
      qpat_assum `LENGTH snapshot5 = LENGTH (EL n h).po_stack` mp_tac >>
      qpat_assum `LIST_REL _ (ZIP (snapshot5,(EL n h).po_stack))
        (EL q ht).po_stack` mp_tac >>
      qpat_assum `ptr_dalloca_ghost_vars (EL n h).po_prov _ _ _ _ _` mp_tac >>
      qpat_assum `!v site. FLOOKUP (EL q ht).po_prov v = SOME site ==> _` mp_tac >>
      qpat_assum `!v site. FLOOKUP snapshot4 v = NONE /\
        FLOOKUP (EL n h).po_prov v = SOME site ==> _` mp_tac >>
      qpat_assum `LENGTH snapshot3 = LENGTH (EL n h).po_params` mp_tac >>
      qpat_assum `LENGTH (EL n h).po_params = LENGTH (EL q ht).po_params` mp_tac >>
      qpat_assum `!k site. k < LENGTH (EL n h).po_params ==> _` mp_tac >>
      qpat_assum `nextsnapshot5 = (snapshot3,snapshot4)::snapshot5` mp_tac >>
      qpat_assum `(EL (SUC n) h).po_stack = _ :: (EL n h).po_stack` mp_tac >>
      qpat_assum `(EL (SUC q) ht).po_stack = _ :: (EL q ht).po_stack` mp_tac >>
      qpat_assum `(EL q ht).po_inst = (EL n h).po_inst` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[] >>
      map_every qx_gen_tac [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
        `owned_size`,`owned_pos`,`owned_ix`] >>
      qpat_assum `!u tok id rb sz pos ix. _`
        (qspecl_then [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
          `owned_size`,`owned_pos`,`owned_ix`] mp_tac) >> simp[ADD_COMM])

  >>
  `is_raw_return_opcode (EL n h).po_inst.inst_opcode /\
   ?return_frame return_stk return_PT return_TG return_saved.
     (EL n h).po_stack = return_frame::return_stk /\
     snapshot5 = (return_PT,return_TG)::return_saved` by
    (qpat_assum `ptr_tagged_chrono_step C (HD snapshot0)
       (EL n h) (EL (SUC n) h) snapshot3 snapshot4 snapshot5
       nextsnapshot3 nextsnapshot4 nextsnapshot5` mp_tac >>
     qpat_assum `~(~is_terminator (EL n h).po_inst.inst_opcode /\ _)` mp_tac >>
     qpat_assum `~((EL n h).po_inst.inst_opcode = JMP \/ _)` mp_tac >>
     qpat_assum `(EL n h).po_inst.inst_opcode <> INVOKE` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt disch_tac >>
     qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once ptr_tagged_chrono_step_cases, ptr_observe_def] >> strip_tac >>
     gvs[ptr_observation_component_equality]
     >>~- ([`step_inst _ _ _ _ = OK _`],
       drule_all venomExecProofsTheory.step_inst_ok_terminator_jump >>
       strip_tac >> gvs[]) >>
     qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >>
     disch_then (mp_tac o MATCH_MP opcodeClassTheory.step_inst_base_intret_opcodes) >>
     simp[callLayoutDefsTheory.is_raw_return_opcode_def]) >>

  (* The preceding by assertion exposes the existential witnesses itself;
     do not pop_assum qx_choose_then here. No full record equalities from
     tagged-case inversion escape that isolated subproof. *)
  `?return_target return_target_stk.
     (EL q ht).po_stack = return_target::return_target_stk` by
    (qpat_assum `LIST_REL _ (ZIP (snapshot5,(EL n h).po_stack))
       (EL q ht).po_stack` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     qpat_assum `(EL n h).po_stack = return_frame::return_stk` mp_tac >>
     qpat_assum `snapshot5 = (return_PT,return_TG)::return_saved` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `(EL q ht).po_stack` >> gvs[]) >>

  (* Rewrite only the saved relation theorem, never the entire root context.
     Its head exposes exactly raw RET's approved weak head R/P/outputeq;
     its tail retains the original inline strong relation unchanged. *)
  qpat_assum `(EL n h).po_stack = return_frame::return_stk` (fn src_eq =>
    qpat_assum `snapshot5 = (return_PT,return_TG)::return_saved` (fn saved_eq =>
      qpat_assum `(EL q ht).po_stack = return_target::return_target_stk` (fn tgt_eq =>
        qpat_assum `LIST_REL _ (ZIP (snapshot5,(EL n h).po_stack))
          (EL q ht).po_stack`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [src_eq,saved_eq,tgt_eq])))) >>
  qpat_assum `(EL n h).po_stack = return_frame::return_stk` (fn src_eq =>
    qpat_assum `(EL q ht).po_stack = return_target::return_target_stk` (fn tgt_eq =>
      qpat_assum `LIST_REL _ (EL n h).po_stack (EL q ht).po_stack`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [src_eq,tgt_eq]))) >>

  `LENGTH return_saved = LENGTH return_stk` by
    (qpat_assum `LENGTH snapshot5 = LENGTH (EL n h).po_stack` mp_tac >>
     qpat_assum `(EL n h).po_stack = return_frame::return_stk` mp_tac >>
     qpat_assum `snapshot5 = (return_PT,return_TG)::return_saved` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[]) >>

  mp_tac (Q.INST [
    `a` |-> `EL n h`, `at` |-> `EL q ht`,
    `b` |-> `EL (SUC n) h`, `bt` |-> `EL (SUC q) ht`,
    `endpoint_t` |-> `at`,
    `tsj` |-> `snapshot0`, `rj` |-> `snapshot1`, `bj` |-> `snapshot2`,
    `PTj` |-> `snapshot3`, `TGj` |-> `snapshot4`,
    `sj` |-> `snapshot5`, `ej` |-> `snapshot6`,
    `PTj'` |-> `nextsnapshot3`, `TGj'` |-> `nextsnapshot4`,
    `sj'` |-> `nextsnapshot5`,
    `f` |-> `return_frame`, `stk` |-> `return_stk`,
    `ft` |-> `return_target`, `stkt` |-> `return_target_stk`,
    `RPT` |-> `return_PT`, `RTG` |-> `return_TG`,
    `tail` |-> `return_saved`]
    ptr_dalloca_historical_runtime_ret) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>

  `LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site)
    (EL (SUC n) h).po_params (EL (SUC q) ht).po_params` by
    (pure_rewrite_tac[LIST_REL_EL_EQN] >> BETA_TAC >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qx_gen_tac `pg_index` >> disch_tac >>
     qx_gen_tac `pg_site` >> disch_tac >>
     qpat_assum `!k site. k < LENGTH (EL (SUC n) h).po_params ==> _`
       (qspecl_then [`pg_index`,`pg_site`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1) >> simp[]) >>

  `LIST_REL (\f ft.
      ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
        ft.cf_prov ft.cf_tvar ft.cf_state /\
      LIST_REL (\p pt. !site. pt = SOME site ==> p = SOME site)
        f.cf_params ft.cf_params)
    (EL (SUC n) h).po_stack (EL (SUC q) ht).po_stack` by
    (qpat_assum `LIST_REL _ return_stk return_target_stk` mp_tac >>
     simp[]) >>

  `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
    (\token aid. F) (EL (SUC n) h) (EL (SUC q) ht)` by
    (simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
     first_assum ACCEPT_TAC) >>

  (* Strong saved tail was retained literally above. Raw RET identifies
     nextsnapshot5=return_saved and both post stacks with the actual tails;
     the source saved-length equality is already established. MemorySteps
     masks and uniform successor-owned were produced before this branch. *)
  map_every qx_gen_tac [`post_ts`,`post_rw`,`post_births`,`post_PT`,
    `post_TG`,`post_saved`,`post_entries`] >>
  qpat_assum `EL (SUC n) H = (nextsnapshot0,nextsnapshot1,nextsnapshot2,
    nextsnapshot3,nextsnapshot4,nextsnapshot5,nextsnapshot6)`
    (fn th => rewrite_tac[th, pairTheory.PAIR_EQ]) >>
  disch_then (map_every SUBST_ALL_TAC o map SYM o CONJUNCTS) >>
  qpat_assum `ptr_dalloca_ghost_sample lo (dyn_floor C vs) FEMPTY nextsnapshot2
    (\token aid. F) (EL (SUC n) h) (EL (SUC q) ht)` mp_tac >>
  qpat_assum `!v site. FLOOKUP (EL (SUC q) ht).po_prov v = SOME site ==> _` mp_tac >>
  qpat_assum `!v site. FLOOKUP nextsnapshot4 v = NONE /\
    FLOOKUP (EL (SUC n) h).po_prov v = SOME site ==> _` mp_tac >>
  qpat_assum `!u tok id rb sz pos ix.
    ~in_revert_forward (EL (SUC n) h).po_fn (EL (SUC n) h).po_state /\ _ ==> _` mp_tac >>
  qpat_assum `LENGTH nextsnapshot3 = LENGTH (EL (SUC n) h).po_params` mp_tac >>
  qpat_assum `LENGTH (EL (SUC n) h).po_params = LENGTH (EL (SUC q) ht).po_params` mp_tac >>
  qpat_assum `!k site. k < LENGTH (EL (SUC n) h).po_params ==> _` mp_tac >>
  qpat_assum `nextsnapshot5 = return_saved` mp_tac >>
  qpat_assum `(EL (SUC n) h).po_stack = return_stk` mp_tac >>
  qpat_assum `(EL (SUC q) ht).po_stack = return_target_stk` mp_tac >>
  qpat_assum `LENGTH return_saved = LENGTH return_stk` mp_tac >>
  qpat_assum `LIST_REL _ (ZIP (return_saved,return_stk)) return_target_stk` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[] >>
  map_every qx_gen_tac [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
    `owned_size`,`owned_pos`,`owned_ix`] >>
  qpat_assum `!u tok id rb sz pos ix. _`
    (qspecl_then [`owned_v`,`owned_token`,`owned_id`,`owned_base`,
      `owned_size`,`owned_pos`,`owned_ix`] mp_tac) >> simp[ADD_COMM]
QED
