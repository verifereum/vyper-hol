Theory concretizePtrCallConflict
Ancestors
  concretizePtrOwnerConflict concretizePtrStackImports
  concretizePtrOwnerPath concretizePtrChronologicalHistory
  concretizeAnalysisLivenessTransfer concretizeMemLocDefs
  list finite_map

Theorem ptr_owner_context_call_conflict:
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed_ctx nm))) /\
  sizes = (\a. if context_alloca_size fn (imported_mems_used observed_ctx fn) a = 0
              then NONE else SOME (context_alloca_size fn (imported_mems_used observed_ctx fn) a)) /\
  ptr_chrono_history vs C h endpoint /\ u <= t /\ t <= r /\ r < LENGTH h /\
  (!j. u <= j /\ j <= r ==> d <= LENGTH (EL j h).po_stack) /\
  (ptr_owner_view d (EL u h)).cf_fn = fn /\
  wf_function fn /\ ptr_history_cfg_ok fn (cfg_analyze fn) /\
  ml_used_gen a bp mems (ptr_owner_view d (EL u h)).cf_inst /\
  ml_read_gen a bp mems (ptr_owner_view d (EL r h)).cf_inst /\
  (!j. t <= j /\ j < r ==>
    ~ptr_ml_can_kill a bp sizes (ptr_owner_view d (EL j h)).cf_inst) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  stk = (EL t h).po_stack /\ n < LENGTH stk /\ k <= n /\
  EL k (((EL t h).po_fn,(EL t h).po_state) ::
    MAP (\f. (f.cf_fn,f.cf_state)) stk) = (desc_owner,desc_state) /\
  FLOOKUP desc_state.vs_allocas aid = SOME (b,sz) /\
  ptr_owner_view d (EL t h) = EL n stk /\
  o1_walk_view rpolicy 2 C' fn observed /\ observed_ctx = observed.cu_context ==>
  ?xs ys.
    FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed_ctx fn bp (cfg_analyze fn)) a = SOME xs /\
    FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed_ctx fn bp (cfg_analyze fn)) (Allocation aid) = SOME ys /\
    MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
         (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs /\
    MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
         (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) ys
Proof
  strip_tac >>
  drule_all ptr_owner_context_liveset >> strip_tac >>
  `t < LENGTH h` by decide_tac >>
  `frame_reachable vs C (EL t h).po_stack (EL t h).po_params
    (EL t h).po_prov (EL t h).po_taint (EL t h).po_fn
    (EL t h).po_inst (EL t h).po_state` by
    (drule ptr_chrono_history_reachable >>
     simp[EVERY_EL, ptr_observation_reachable_def] >> metis_tac[]) >>
  `(ptr_owner_view d (EL t h)).cf_fn = fn` by
    (`(ptr_owner_view d (EL u h)).cf_fn = (ptr_owner_view d (EL t h)).cf_fn` by
      (irule ptr_owner_view_interval_function >> rpt conj_tac
       >- (rpt strip_tac >> first_x_assum irule >> decide_tac)
       >- decide_tac >- decide_tac >> metis_tac[]) >> metis_tac[]) >>
  `ml_callee_gen (Allocation aid) mems (ptr_owner_view d (EL t h)).cf_inst` by
    (`o1_walk_view rpolicy 2 C' (EL n (EL t h).po_stack).cf_fn observed` by
       metis_tac[] >>
     qpat_x_assum `stk = _` SUBST_ALL_TAC >>
     drule_all ptr_frame_descendant_demand >> simp[]) >>
  `?ys. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed_ctx fn bp (cfg_analyze fn)) (Allocation aid) = SOME ys /\
    MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
         (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) ys` by
    (irule ptr_owner_context_liveset >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`t`,`t`] >>
         gvs[ml_used_gen_def, ml_read_gen_def] >>
         metis_tac[]) >>
     metis_tac[]) >>
  metis_tac[]
QED
