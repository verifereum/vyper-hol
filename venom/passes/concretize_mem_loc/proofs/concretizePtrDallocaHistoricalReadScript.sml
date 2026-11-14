Theory concretizePtrDallocaHistoricalRead
Ancestors
  concretizePtrDallocaHistoricalMemory concretizePtrDallocaReadChannels
  concretizePtrDallocaCopyRead concretizePtrDallocaScalarReads concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrEventEmbedding
  list rich_list arithmetic finite_map words pred_set

(* Each read uses the recorded departure snapshot. Recursive memory
   assumptions range only over source indices strictly before i. *)
Theorem ptr_dalloca_historical_demanded_reflection_static:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG0 v = SOME (token,aid) /\
  FLOOKUP (EL i h).po_prov v = SOME (b,sz) /\
  FLOOKUP bw0 (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward (EL i h).po_fn (EL i h).po_state /\
  (EL i h).po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) (EL i h).po_inst.inst_operands /\
  (inst_read_op (EL i h).po_inst = SOME (Var v) \/ (EL i h).po_inst.inst_opcode = INVOKE) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k IN (EL q ht).po_taint.t_mem ==> b+k IN (EL i h).po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  drule ptr_paired_memory_samples >> strip_tac >>
  `i < LENGTH h /\ q < LENGTH ht /\ LENGTH H = LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  `EL (EL q done) H = (ts0,rw0,bw0,PT0,TG0,sv0,en0)` by metis_tac[] >>
  drule_all ptr_dalloca_memory_departure_cut >> strip_tac >>
  mp_tac (Q.INST
    [`h` |-> `TAKE (SUC i) h`, `endpoint` |-> `EL i h`,
     `ht` |-> `TAKE (SUC q) ht`, `at` |-> `EL q ht`,
     `done` |-> `TAKE q done`, `tokens` |-> `ts0`, `registry` |-> `rw0`,
     `births` |-> `bw0`, `PT` |-> `PT0`, `TG` |-> `TG0`,
     `saved` |-> `sv0`, `entries` |-> `en0`,
     `H` |-> `TAKE (SUC i) H`,
     `ws` |-> `FILTER (\(n,j,rho). j < q) ws`]
    ptr_dalloca_demanded_reflection_memory_static) >>
  impl_tac
  >- (simp[LENGTH_TAKE, EL_TAKE] >> rpt conj_tac >>
      rpt strip_tac >>
      `r < SUC q /\ EL r done < SUC (EL q done)` by
        (fs[EL_TAKE] >> decide_tac) >>
      `EL r (TAKE q done) = EL r done` by simp[EL_TAKE] >>
      `EL (EL r done) (TAKE (SUC (EL q done)) h) = EL (EL r done) h` by simp[EL_TAKE] >>
      `EL (EL r done) (TAKE (SUC (EL q done)) H) = EL (EL r done) H` by simp[EL_TAKE] >>
      fs[] >> first_x_assum irule >> simp[]
      >> (fn g =>
        if is_exists (snd g) then
          (rename1 `FLOOKUP bw (tok,id) = SOME (read_base,read_size)` >>
           qexistsl [`id`,`pos`,`read_size`,`tok`,`u`] >> simp[]) g
        else decide_tac g)) >>
  simp[]
QED

Theorem ptr_dalloca_historical_demanded_reflection:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG0 v = SOME (token,aid) /\
  FLOOKUP (EL i h).po_prov v = SOME (b,sz) /\
  FLOOKUP bw0 (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward (EL i h).po_fn (EL i h).po_state /\
  (EL i h).po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) (EL i h).po_inst.inst_operands /\
  (inst_read_op (EL i h).po_inst = SOME (Var v) \/ (EL i h).po_inst.inst_opcode = INVOKE) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k IN (EL q ht).po_taint.t_mem ==> b+k IN (EL i h).po_taint.t_mem
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_historical_demanded_reflection_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem ptr_dalloca_frontier_demanded_reflection_static:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  i < LENGTH h /\ q <= LENGTH done /\
  (q = 0 \/ EL (q-1) done < i) /\
  i <= EL q (done ++ [LENGTH h - 1]) /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG0 v = SOME (token,aid) /\
  FLOOKUP (EL i h).po_prov v = SOME (b,sz) /\
  FLOOKUP bw0 (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward (EL i h).po_fn (EL i h).po_state /\
  (EL i h).po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) (EL i h).po_inst.inst_operands /\
  (inst_read_op (EL i h).po_inst = SOME (Var v) \/ (EL i h).po_inst.inst_opcode = INVOKE) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k IN (EL q ht).po_taint.t_mem ==> b+k IN (EL i h).po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  Cases_on `q < LENGTH done /\ i = EL q done`
  >- (qpat_x_assum `q < LENGTH done /\ i = EL q done` strip_assume_tac >>
      mp_tac ptr_dalloca_historical_demanded_reflection_static >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
  drule ptr_paired_memory_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `!r s. r < s /\ s < LENGTH (done ++ [LENGTH h - 1]) ==>
    EL r (done ++ [LENGTH h - 1]) <
    EL s (done ++ [LENGTH h - 1])` by fs[ptr_event_embedding_def] >>
  `!r s. r < s /\ s < LENGTH done ==> EL r done < EL s done` by
    (rpt strip_tac >>
     qpat_x_assum `!r s. r < s /\ s < LENGTH (done ++ _) ==> _`
       (qspecl_then [`r`,`s`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  `!r. r < LENGTH done ==> EL r done < LENGTH h - 1` by
    (rpt strip_tac >>
     qpat_x_assum `!r s. r < s /\ s < LENGTH (done ++ _) ==> _`
       (qspecl_then [`r`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  Cases_on `i = LENGTH h - 1`
  >- (`q = LENGTH done` by
        (Cases_on `q < LENGTH done`
         >- (`EL q done < LENGTH h - 1` by metis_tac[] >>
             `i <= EL q done` by fs[EL_APPEND_EQN] >> decide_tac) >>
         decide_tac) >>
      drule ptr_paired_memory_samples >> strip_tac >>
      drule ptr_structural_transcript_endpoint >> strip_tac >>
      drule ptr_structural_trace_source >> strip_tac >>
      drule ptr_structural_trace_target >> strip_tac >>
      imp_res_tac ptr_chrono_history_end >>
      `LENGTH ht = SUC (LENGTH done)` by
        fs[ptr_paired_samples_def, ptr_sample_list_def] >>
      `H <> []` by (Cases_on `H` >> gvs[]) >>
      `EL (LENGTH done) ht = at /\
       EL (LENGTH h - 1) h = endpoint /\
       EL (LENGTH h - 1) H =
         (tokens,registry,births,PT,TG,saved,entries)` by
        (qpat_x_assum `LAST ht = at` mp_tac >>
         qpat_x_assum `LAST h = endpoint` mp_tac >>
         qpat_x_assum `LAST H = _` mp_tac >>
         simp[LAST_EL, PRE_SUB1]) >>
      gvs[] >>
      `INVOKE <> ASSIGN` by simp[] >>
      qpat_assum `ptr_paired_memory_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (fn th => mp_tac (PART_MATCH
          (fst o dest_conj o fst o dest_imp)
          ptr_dalloca_demanded_reflection_memory_static (concl th))) >>
      (impl_tac >-
        (rpt conj_tac >> asm_rewrite_tac[] >| [
          rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          qpat_x_assum `EL r done = j` (SUBST_ALL_TAC o SYM) >> fs[] >>
          qpat_assum `!r op. _ ==> op_taint _ op SUBSET _`
            (qspecl_then [`r`,`op`] mp_tac) >> simp[],
          rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          qpat_x_assum `EL r done = j` (SUBST_ALL_TAC o SYM) >> fs[] >>
          qpat_assum `!r a. _ /\ _ /\ a < lo ==> _`
            (qspecl_then [`r`,`a`] mp_tac) >> simp[],
          rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          qpat_x_assum `EL r done = j` (SUBST_ALL_TAC o SYM) >> fs[] >>
          qpat_assum `!r a. _ /\ _ /\ dyn_floor C vs <= a ==> _`
            (qspecl_then [`r`,`a`] mp_tac) >> simp[],
          map_every qx_gen_tac
            [`j`,`r`,`read_var`,`read_token`,`read_aid`,`read_base`,
             `read_size`,`read_pos`,`read_ix`,`hist_tokens`,`hist_registry`,
             `hist_births`,`hist_params`,`hist_prov`,`hist_saved`,`hist_entries`] >>
          disch_then (map_every assume_tac o CONJUNCTS) >>
          qpat_x_assum `EL r done = j` (SUBST_ALL_TAC o SYM) >> fs[] >>
          qpat_assum `!r u tok id base size pos ix ts rw bw PTw TGw sw ew. _`
            (qspecl_then [`r`,`read_var`,`read_token`,`read_aid`,`read_base`,
              `read_size`,`read_pos`,`read_ix`,`hist_tokens`,`hist_registry`,
              `hist_births`,`hist_params`,`hist_prov`,`hist_saved`,`hist_entries`]
              mp_tac) >> simp[]
        ])) >> simp[]) >>
  `i < LENGTH h - 1` by decide_tac >>
  `~MEM i done` by
    (CCONTR_TAC >>
     `?r. r < LENGTH done /\ EL r done = i` by metis_tac[MEM_EL] >>
     pop_assum strip_assume_tac >>
     Cases_on `r < q`
     >- (`0 < q /\ r <= q-1` by decide_tac >>
         Cases_on `r = q-1` >- gvs[] >>
         `r < q-1 /\ q-1 < LENGTH done` by decide_tac >>
         `EL r done < EL (q-1) done` by metis_tac[] >>
         gvs[] >> decide_tac) >>
     `q <= r /\ q < LENGTH done` by decide_tac >>
     `i < EL q done` by (gvs[EL_APPEND_EQN] >> decide_tac) >>
     Cases_on `r = q` >- gvs[] >>
     `q < r` by decide_tac >>
     `EL q done < EL r done` by metis_tac[] >> decide_tac) >>
  `(EL i h).po_inst.inst_opcode = NOP` by
    (drule ptr_structural_trace_unmatched_nop >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  gvs[concretizeMemLocDefsTheory.inst_read_op_def,
      memLocDefsTheory.mem_read_ops_def]
QED

Theorem ptr_dalloca_frontier_demanded_reflection:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  i < LENGTH h /\ q <= LENGTH done /\
  (q = 0 \/ EL (q-1) done < i) /\
  i <= EL q (done ++ [LENGTH h - 1]) /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG0 v = SOME (token,aid) /\
  FLOOKUP (EL i h).po_prov v = SOME (b,sz) /\
  FLOOKUP bw0 (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward (EL i h).po_fn (EL i h).po_state /\
  (EL i h).po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) (EL i h).po_inst.inst_operands /\
  (inst_read_op (EL i h).po_inst = SOME (Var v) \/ (EL i h).po_inst.inst_opcode = INVOKE) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k IN (EL q ht).po_taint.t_mem ==> b+k IN (EL i h).po_taint.t_mem
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_frontier_demanded_reflection_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem ptr_dalloca_historical_scalar_read_masks:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ n0 = EL q done /\
  EL n0 H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  ~in_revert_forward (EL n0 h).po_fn (EL n0 h).po_state /\
  (!i. i < lo ==> i IN (EL q ht).po_taint.t_mem ==> i IN (EL n0 h).po_taint.t_mem) /\
  (EL q ht).po_taint.t_stor SUBSET (EL n0 h).po_taint.t_stor /\
  (EL q ht).po_taint.t_trans SUBSET (EL n0 h).po_taint.t_trans /\
  MEM (EL n0 h).po_inst.inst_opcode [ILOAD;SLOAD;TLOAD] /\ ptr_chrono_step C' (EL q ht) zt ==>
  out_taint (EL q ht).po_taint (EL q ht).po_inst (EL q ht).po_state SUBSET
    out_taint (EL n0 h).po_taint (EL n0 h).po_inst (EL n0 h).po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EL (EL q done) H = (ts0,rw0,bw0,PT0,TG0,sv0,en0)` by metis_tac[] >>
  drule_all ptr_dalloca_memory_departure_cut >> strip_tac >>
  mp_tac (Q.INST
    [`h` |-> `TAKE (SUC n0) h`, `a` |-> `EL n0 h`,
     `ht` |-> `TAKE (SUC q) ht`, `at` |-> `EL q ht`,
     `done` |-> `TAKE q done`, `tokens` |-> `ts0`, `registry` |-> `rw0`,
     `births` |-> `bw0`, `PT` |-> `PT0`, `TG` |-> `TG0`,
     `saved` |-> `sv0`, `entries` |-> `en0`,
     `H` |-> `TAKE (SUC n0) H`,
     `ws` |-> `FILTER (\(n,j,rho). j < q) ws`]
    ptr_dalloca_scalar_read_masks_memory) >> simp[]
QED

Theorem ptr_dalloca_historical_mload_read_mask_static:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (EL i h).po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' (EL q ht) zt ==>
  ?op x y. (EL i h).po_inst.inst_operands = [op] /\
    eval_operand op (EL i h).po_state = SOME x /\
    eval_operand op (EL q ht).po_state = SOME y /\
    mem_word_taint (EL q ht).po_taint.t_mem (w2n y) SUBSET
      mem_word_taint (EL i h).po_taint.t_mem (w2n x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_memory_samples >> strip_tac >>
  `i < LENGTH h /\ q < LENGTH ht /\ LENGTH H = LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  `EL (EL q done) H = (ts0,rw0,bw0,PT0,TG0,sv0,en0)` by metis_tac[] >>
  drule_all ptr_dalloca_memory_departure_cut >> strip_tac >>
  mp_tac (Q.INST
    [`h` |-> `TAKE (SUC i) h`, `endpoint` |-> `EL i h`,
     `ht` |-> `TAKE (SUC q) ht`, `at` |-> `EL q ht`,
     `done` |-> `TAKE q done`, `tokens` |-> `ts0`, `registry` |-> `rw0`,
     `births` |-> `bw0`, `PT` |-> `PT0`, `TG` |-> `TG0`,
     `saved` |-> `sv0`, `entries` |-> `en0`,
     `H` |-> `TAKE (SUC i) H`,
     `ws` |-> `FILTER (\(n,j,rho). j < q) ws`]
    ptr_dalloca_mload_read_mask_memory_static) >>
  impl_tac
  >- (simp[LENGTH_TAKE, EL_TAKE] >> rpt conj_tac >>
      rpt strip_tac >>
      `r < SUC q /\ EL r done < SUC (EL q done)` by
        (fs[EL_TAKE] >> decide_tac) >>
      `EL r (TAKE q done) = EL r done` by simp[EL_TAKE] >>
      `EL (EL r done) (TAKE (SUC (EL q done)) h) = EL (EL r done) h` by simp[EL_TAKE] >>
      `EL (EL r done) (TAKE (SUC (EL q done)) H) = EL (EL r done) H` by simp[EL_TAKE] >>
      fs[] >> first_x_assum irule >> simp[]
      >> (fn g =>
        if is_exists (snd g) then
          (rename1 `FLOOKUP bw (tok,id) = SOME (read_base,read_size)` >>
           qexistsl [`id`,`pos`,`read_size`,`tok`,`u`] >> simp[]) g
        else decide_tac g)) >>
  simp[]
QED

Theorem ptr_dalloca_historical_mload_read_mask:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (EL i h).po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' (EL q ht) zt ==>
  ?op x y. (EL i h).po_inst.inst_operands = [op] /\
    eval_operand op (EL i h).po_state = SOME x /\
    eval_operand op (EL q ht).po_state = SOME y /\
    mem_word_taint (EL q ht).po_taint.t_mem (w2n y) SUBSET
      mem_word_taint (EL i h).po_taint.t_mem (w2n x)
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_historical_mload_read_mask_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem ptr_dalloca_historical_mcopy_read_mask_static:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (EL i h).po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' (EL q ht) zt ==>
  ?dop sop nop d r dt rt n.
    (EL i h).po_inst.inst_operands = [dop;sop;nop] /\
    eval_operand dop (EL i h).po_state = SOME d /\
    eval_operand sop (EL i h).po_state = SOME r /\
    eval_operand nop (EL i h).po_state = SOME n /\
    eval_operand dop (EL q ht).po_state = SOME dt /\
    eval_operand sop (EL q ht).po_state = SOME rt /\
    eval_operand nop (EL q ht).po_state = SOME n /\
    (!k. k < w2n n ==> w2n rt+k IN (EL q ht).po_taint.t_mem ==>
      w2n r+k IN (EL i h).po_taint.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_memory_samples >> strip_tac >>
  `i < LENGTH h /\ q < LENGTH ht /\ LENGTH H = LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  `EL (EL q done) H = (ts0,rw0,bw0,PT0,TG0,sv0,en0)` by metis_tac[] >>
  drule_all ptr_dalloca_memory_departure_cut >> strip_tac >>
  mp_tac (Q.INST
    [`h` |-> `TAKE (SUC i) h`, `endpoint` |-> `EL i h`,
     `ht` |-> `TAKE (SUC q) ht`, `at` |-> `EL q ht`,
     `done` |-> `TAKE q done`, `tokens` |-> `ts0`, `registry` |-> `rw0`,
     `births` |-> `bw0`, `PT` |-> `PT0`, `TG` |-> `TG0`,
     `saved` |-> `sv0`, `entries` |-> `en0`,
     `H` |-> `TAKE (SUC i) H`,
     `ws` |-> `FILTER (\(n,j,rho). j < q) ws`]
    ptr_dalloca_mcopy_read_mask_memory_static) >>
  impl_tac
  >- (simp[LENGTH_TAKE, EL_TAKE] >> rpt conj_tac >>
      rpt strip_tac >>
      `r < SUC q /\ EL r done < SUC (EL q done)` by
        (fs[EL_TAKE] >> decide_tac) >>
      `EL r (TAKE q done) = EL r done` by simp[EL_TAKE] >>
      `EL (EL r done) (TAKE (SUC (EL q done)) h) = EL (EL r done) h` by simp[EL_TAKE] >>
      `EL (EL r done) (TAKE (SUC (EL q done)) H) = EL (EL r done) H` by simp[EL_TAKE] >>
      fs[] >> first_x_assum irule >> simp[]
      >> (fn g =>
        if is_exists (snd g) then
          (rename1 `FLOOKUP bw (tok,id) = SOME (read_base,read_size)` >>
           qexistsl [`id`,`pos`,`read_size`,`tok`,`u`] >> simp[]) g
        else decide_tac g)) >>
  simp[]
QED

Theorem ptr_dalloca_historical_mcopy_read_mask:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (EL i h).po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' (EL q ht) zt ==>
  ?dop sop nop d r dt rt n.
    (EL i h).po_inst.inst_operands = [dop;sop;nop] /\
    eval_operand dop (EL i h).po_state = SOME d /\
    eval_operand sop (EL i h).po_state = SOME r /\
    eval_operand nop (EL i h).po_state = SOME n /\
    eval_operand dop (EL q ht).po_state = SOME dt /\
    eval_operand sop (EL q ht).po_state = SOME rt /\
    eval_operand nop (EL q ht).po_state = SOME n /\
    (!k. k < w2n n ==> w2n rt+k IN (EL q ht).po_taint.t_mem ==>
      w2n r+k IN (EL i h).po_taint.t_mem)
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_historical_mcopy_read_mask_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED
