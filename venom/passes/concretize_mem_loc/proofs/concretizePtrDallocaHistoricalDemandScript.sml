Theory concretizePtrDallocaHistoricalDemand
Ancestors
  concretizePtrDemandWriteExclusion concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrEventEmbedding
  concretizePtrChronologicalHistory list rich_list arithmetic

Theorem ptr_dalloca_transcript_departure_cut:
  !R vs C C' h endpoint ht at done tokens registry births PT TG saved entries H.
  ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H ==>
  !q ts rw bw PTw TGw sw ew.
    q < LENGTH done /\
    EL (EL q done) H = (ts,rw,bw,PTw,TGw,sw,ew) ==>
    ptr_structural_transcript R vs C C'
      (TAKE (SUC (EL q done)) h) (EL (EL q done) h) (TAKE (SUC q) ht) (EL q ht)
      (TAKE q done) ts rw bw PTw TGw sw ew (TAKE (SUC (EL q done)) H)
Proof
  ho_match_mp_tac ptr_structural_transcript_strongind >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
      drule ptr_structural_transcript_endpoint >> strip_tac >>
      drule ptr_structural_transcript_erasure >> strip_tac >>
      drule ptr_structural_trace_embedding >> strip_tac >>
      `EL q done < LENGTH h` by
        (gvs[ptr_event_embedding_def, EVERY_EL] >>
         first_x_assum drule >> simp[EL_APPEND_EQN]) >>
      `SUC (EL q done) - LENGTH h = 0` by decide_tac >>
      simp[TAKE_APPEND, EL_APPEND_EQN] >> fs[EL_APPEND_EQN] >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  Cases_on `q < LENGTH done`
  >- (`EL q done < LENGTH h` by
        (gvs[ptr_event_embedding_def, EVERY_EL] >>
         first_x_assum drule >> simp[EL_APPEND_EQN]) >>
      `SUC (EL q done) - LENGTH h = 0 /\ SUC q - LENGTH ht = 0 /\ q - LENGTH done = 0`
        by decide_tac >> simp[TAKE_APPEND, EL_APPEND_EQN] >> fs[EL_APPEND_EQN] >>
      first_x_assum irule >> simp[]) >>
  `q = LENGTH done` by gvs[] >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `H <> []` by (Cases_on `H` >> gvs[]) >>
  `SUC (LENGTH h - 1) = LENGTH h /\
   LENGTH h - 1 = PRE (LENGTH h) /\ LENGTH done = PRE (LENGTH ht) /\
   SUC (LENGTH done) - LENGTH ht = 0` by decide_tac >>
  `SUC (PRE (LENGTH ht)) - LENGTH ht = 0` by decide_tac >>
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, EL_APPEND_EQN] >>
  qpat_x_assum `LENGTH h - 1 = PRE (LENGTH h)` kall_tac >>
  qpat_x_assum `LENGTH done = PRE (LENGTH ht)` kall_tac >>
  gvs[EL_APPEND_EQN, LAST_EL, PRE_SUB1]
QED

(* This cuts only the structural witnesses, never the paired ghost relation.
   Writer consumers keep their full-history samples and use EL_TAKE at w<n. *)
Theorem ptr_dalloca_historical_demand_interval:
  ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H /\ q < LENGTH done /\ n = EL q done /\
  EL n H = (ts,rw,bw,PTw,TGw,sw,ew) /\ vs.vs_allocas = FEMPTY /\
  o1_ctx_shape C /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward (EL n h).po_fn (EL n h).po_state /\
  (EL n h).po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH (EL n h).po_stack /\
  FLOOKUP (ptr_owner_view d (EL n h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= b+k /\ k < sz /\ b+k NOTIN (EL n h).po_taint.t_mem /\
  MEM (Var v) (EL n h).po_inst.inst_operands /\
  (inst_read_op (EL n h).po_inst = SOME (Var v) \/ (EL n h).po_inst.inst_opcode = INVOKE) /\
  FLOOKUP (EL n h).po_prov v = SOME (b,sz) /\
  EL (LENGTH (EL n h).po_stack-d) ts = token /\
  fn = (ptr_owner_view d (EL n h)).cf_fn /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  o1_run_state_ok vs /\ ptr_discipline lo C vs /\
  EVERY fn_inst_wf C.ctx_functions ==>
  (?w. w < n /\
    ptr_demand_interval R vs C C' (TAKE (SUC n) h) (EL n h)
      (TAKE (SUC q) ht) (EL q ht) (TAKE q done) ts rw bw PTw TGw sw ew
      (TAKE (SUC n) H) lo P d aid b sz k v token fn bp mems observed
      rpolicy s out names w) \/
  dyn_floor C vs <= b+k
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n < LENGTH h` by
    (drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_embedding >> strip_tac >>
     gvs[ptr_event_embedding_def, EVERY_EL] >>
     first_x_assum drule >> simp[EL_APPEND_EQN]) >>
  `EL (EL q done) H = (ts,rw,bw,PTw,TGw,sw,ew)` by metis_tac[] >>
  drule_all ptr_dalloca_transcript_departure_cut >>
  qpat_x_assum `n = _` (fn th => rewrite_tac[GSYM th]) >> strip_tac >>
  `!obs. MEM obs (TAKE (SUC n) h) ==>
    access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state` by
    metis_tac[MEM_TAKE] >>
  drule_all ptr_demand_interval_exists >> strip_tac
  >- (disj1_tac >> qexists `w` >> simp[] >>
      qhdtm_x_assum `ptr_demand_interval` mp_tac >>
      simp[ptr_demand_interval_def, LENGTH_TAKE] >> decide_tac) >>
  simp[]
QED
