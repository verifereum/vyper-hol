Theory concretizePtrCallSeparation
Ancestors
  concretizePtrStackImports concretizePtrOwnerConflict concretizePtrLayoutOutput
  concretizePtrOwnerPath concretizePtrChronologicalHistory
  concretizeAnalysisLivenessTransfer concretizeMemLocDefs
  list finite_map

Theorem ptr_output_suspended_descendant_separation:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  ptr_chrono_history vs C h endpoint /\ t < LENGTH h /\
  stk = (EL t h).po_stack /\ n < LENGTH stk /\ k <= n /\
  EL k (((EL t h).po_fn,(EL t h).po_state) ::
    MAP (\f. (f.cf_fn,f.cf_state)) stk) = (desc,ds) /\
  FLOOKUP ds.vs_allocas bid = SOME (db,sb) /\
  fn = (EL n stk).cf_fn /\
  addr = ((EL n stk).cf_state.vs_current_bb,(EL n stk).cf_state.vs_inst_idx) /\
  o1_walk_view rpolicy 2 C' fn observed /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  fn.fn_eom = NONE /\ fn_ptr_ok P fn /\
  wf_function fn /\ ptr_history_cfg_ok fn (cfg_analyze fn) /\
  concretize_function_fuel_in_context (concretize_memloc_fuel fn)
    observed.cu_context reserved fn = SOME fn' /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  fn' = out.fpo_function /\
  static_alloca_items fn = SOME items /\ MEM (a,sa) items /\
  MEM (a,pa,sa) fn'.fn_mems_used /\ 0 < sa /\ 0 < sb /\
  (!c p sz. MEM (c,p,sz) (imported_mems_used observed.cu_context fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
    observed.cu_context fn
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (cfg_analyze fn)) a = SOME la /\ MEM addr la ==>
  ?pb. MEM (Allocation bid,pb,sb) (imported_mems_used observed.cu_context fn) /\
    reserved_intervals_disjoint (pa,sa) (pb,sb)
Proof
  strip_tac >>
  `frame_reachable vs C (EL t h).po_stack (EL t h).po_params
    (EL t h).po_prov (EL t h).po_taint (EL t h).po_fn
    (EL t h).po_inst (EL t h).po_state` by
    (drule ptr_chrono_history_reachable >>
     simp[EVERY_EL, ptr_observation_reachable_def] >> metis_tac[]) >>
  `o1_walk_view rpolicy 2 C' (EL n stk).cf_fn observed` by metis_tac[] >>
  `?pb. MEM (Allocation bid,pb,sb)
    (imported_mems_used observed.cu_context fn)` by
    (qpat_assum `stk = _` SUBST_ALL_TAC >>
     drule_all ptr_frame_descendant_import >> metis_tac[]) >>
  `ml_callee_gen (Allocation bid)
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm)))
    (EL n stk).cf_inst` by
    (qpat_assum `stk = _` SUBST_ALL_TAC >>
     drule_all ptr_frame_descendant_demand >> simp[]) >>
  qabbrev_tac `d = LENGTH stk - (n + 1)` >>
  `d <= LENGTH (EL t h).po_stack /\
   ptr_owner_view d (EL t h) = EL n stk` by
    (`d < LENGTH stk /\ LENGTH stk - (d + 1) = n` by
       (simp[NoAsms, Abbr `d`] >> decide_tac) >>
     pure_rewrite_tac[ptr_owner_view_def] >>
     qpat_x_assum `stk = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[] >> decide_tac) >>
  `?lb. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
    observed.cu_context fn
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (cfg_analyze fn)) (Allocation bid) = SOME lb /\ MEM addr lb` by
    (qpat_assum `addr = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `ptr_owner_view d (EL t h) = _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     irule ptr_owner_context_liveset >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`t`,`t`] >> gnvs[ml_used_gen_def, ml_read_gen_def] >>
         metis_tac[arithmeticTheory.LESS_EQUAL_ANTISYM]) >> metis_tac[]) >>
  qexists_tac `pb` >> simp[] >>
  irule ptr_output_local_import_separation >>
  (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `concretize_function_fuel_in_context _ _ _ _ = SOME _`)) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
