Theory concretizePtrDemandWriteExclusion
Ancestors concretizePtrProtectedLivesets concretizePtrTokenInterval
  concretizePtrHistoricalPlacement concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrExactWriteTransport
  concretizePtrTaggedCallLiveness concretizePtrRetrospectiveLocal
  concretizePtrChronologicalHistory
  list rich_list finite_map arithmetic

(* Keep the initializing writer selected by ProtectedLivesets: token
   continuity is proved on its interval, not on a second chosen history. *)
Theorem ptr_demand_protected_token_interval:
  ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
    births PT TG saved entries H /\ vs.vs_allocas = FEMPTY /\
  o1_ctx_shape C /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= b+k /\ k < sz /\ b+k NOTIN endpoint.po_taint.t_mem /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  EL (LENGTH endpoint.po_stack-d) tokens = token /\
  fn = (ptr_owner_view d endpoint).cf_fn /\
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
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  EVERY fn_inst_wf C.ctx_functions ==>
  ?w. w+1 < LENGTH h /\ ptr_chrono_write C (b+k) (EL w h) /\
    (!j. w < j /\ j+1 < LENGTH h ==> ~ptr_chrono_write C (b+k) (EL j h)) /\
    (!t. w < t /\ t < LENGTH h ==>
      ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
        observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
        MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
          (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs) /\
    (!j. w <= j /\ j < LENGTH h ==>
      d <= LENGTH (EL j h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL j h)).cf_state.vs_allocas aid = SOME (b,sz) /\
      ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
      EL (LENGTH (EL j h).po_stack-d) (FST (EL j H)) = token) /\
    ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
    ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `b <= b+k /\ b+k < b+sz` by decide_tac >>
  drule_all ptr_endpoint_protected_livesets >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  `LENGTH h-1 < LENGTH h /\ EL (LENGTH h-1) h = endpoint /\
   EL (LENGTH h-1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (Cases_on `h` >> Cases_on `H` >> gvs[LAST_EL]) >>
  `!j. w <= j /\ j < LENGTH h ==>
    EL (LENGTH (EL j h).po_stack-d) (FST (EL j H)) = token` by
    (`!j. w <= j /\ j <= LENGTH h-1 ==>
       ?tsj rj bj PTj TGj sj ej.
         EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
         EL (LENGTH (EL j h).po_stack-d) tsj = token` by
       (drule ptr_transcript_bottom_token_interval >>
        disch_then (qspecl_then [`w`,`LENGTH h-1`,`d`] mp_tac) >>
        simp[]) >>
     rpt strip_tac >> first_x_assum (qspec_then `j` mp_tac) >>
     (impl_tac >- decide_tac) >> strip_tac >> simp[]) >>
  qexists `w` >> asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]
QED
