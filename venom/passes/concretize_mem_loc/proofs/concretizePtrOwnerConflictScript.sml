Theory concretizePtrOwnerConflict
Ancestors
  concretizePtrOwnerReadDemand concretizePtrOwnerPath concretizePtrHistoryUsed
  concretizePtrChronologicalHistory concretizePtrConflictContract
  concretizePtrOrdering concretizePtrReadCoverage concretizePtrStoreCoverage
  indexedLists concretizeMemLocDefs
  memLocDefs venomExecSemantics enumeral list finite_map pred_set contextCodegenRel

Theorem ptr_owner_two_demands[local]:
  ptr_chrono_history vs C h endpoint /\ u <= t /\ t <= r /\ r < LENGTH h /\
  (!k. u <= k /\ k <= r ==> d <= LENGTH (EL k h).po_stack) /\
  (ptr_owner_view d (EL u h)).cf_fn = fn /\
  wf_function fn /\ ptr_history_cfg_ok fn cfg /\
  (!nm. OL alloc_to (mems nm)) /\
  ml_used_gen a bp mems (ptr_owner_view d (EL u h)).cf_inst /\
  ml_read_gen a bp mems (ptr_owner_view d (EL r h)).cf_inst /\
  (!k. t <= k /\ k < r ==>
    ~ptr_ml_can_kill a bp sizes (ptr_owner_view d (EL k h)).cf_inst) ==>
  MEM a (ml_lookup
    (FST (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes [] cfg fn FEMPTY FEMPTY))
    ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
     (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx)) /\
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes [] cfg fn FEMPTY FEMPTY))
    ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
     (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx)) /\
  active_inst fn (ptr_owner_view d (EL t h)).cf_inst
    (ptr_owner_view d (EL t h)).cf_state
Proof
  strip_tac >>
  `(ptr_owner_view d (EL t h)).cf_fn = fn` by
    (`(ptr_owner_view d (EL u h)).cf_fn = (ptr_owner_view d (EL t h)).cf_fn` by
      (irule ptr_owner_view_interval_function >> rpt conj_tac
       >- (rpt strip_tac >> first_x_assum irule >> decide_tac)
       >- decide_tac >- decide_tac >> metis_tac[]) >> metis_tac[]) >>
  conj_tac
  >- (irule ptr_owner_interval_liveat >> simp[] >>
      conj_tac >- (qexists_tac `r` >> simp[] >> rpt strip_tac >>
        first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `active_inst (ptr_owner_view d (EL u h)).cf_fn
    (ptr_owner_view d (EL u h)).cf_inst (ptr_owner_view d (EL u h)).cf_state` by
    (irule (cj 1 ptr_owner_view_active) >>
     conj_tac >- (first_x_assum irule >> decide_tac) >>
     qexistsl_tac [`C`,`vs`] >> drule ptr_chrono_history_reachable >>
     simp[EVERY_EL] >> metis_tac[]) >>
  `ptr_history_route fn
    (ptr_owner_view d (EL u h)).cf_inst (ptr_owner_view d (EL u h)).cf_state
    (ptr_owner_view d (EL t h)).cf_inst (ptr_owner_view d (EL t h)).cf_state` by
    (gvs[] >> irule ptr_owner_interval_route >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  conj_tac >- (drule_all ptr_history_route_used >> simp[]) >>
  metis_tac[ptr_history_route_shape]
QED

Theorem ptr_owner_context_liveset:
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed_ctx nm))) /\
  sizes = (\a. if context_alloca_size fn (imported_mems_used observed_ctx fn) a = 0
              then NONE else SOME (context_alloca_size fn (imported_mems_used observed_ctx fn) a)) /\
  ptr_chrono_history vs C h endpoint /\ u <= t /\ t <= r /\ r < LENGTH h /\
  (!k. u <= k /\ k <= r ==> d <= LENGTH (EL k h).po_stack) /\
  (ptr_owner_view d (EL u h)).cf_fn = fn /\
  wf_function fn /\ ptr_history_cfg_ok fn (cfg_analyze fn) /\
  ml_used_gen a bp mems (ptr_owner_view d (EL u h)).cf_inst /\
  ml_read_gen a bp mems (ptr_owner_view d (EL r h)).cf_inst /\
  (!k. t <= k /\ k < r ==>
    ~ptr_ml_can_kill a bp sizes (ptr_owner_view d (EL k h)).cf_inst) ==>
  ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed_ctx fn bp (cfg_analyze fn)) a = SOME xs /\
    MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
         (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs
Proof
  strip_tac >>
  `!nm. OL alloc_to (mems nm)` by simp[ptr_incr_ssort_ordered] >>
  drule_all ptr_owner_two_demands >> strip_tac >>
  qabbrev_tac `iter = ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes []
    (cfg_analyze fn) fn FEMPTY FEMPTY` >>
  `ptr_ml_ordered (FST iter) /\ ptr_ml_ordered (SND iter)` by
    (`ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes []
       (cfg_analyze fn) fn FEMPTY FEMPTY = (FST iter,SND iter)` by simp[Abbr `iter`] >>
     drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`) ptr_iterate_fuel_ordered >>
     simp[OL]) >>
  fs[active_inst_def] >>
  qpat_assum `bb.bb_label = _` (fn th => rewrite_tac[GSYM th]) >>
  `MEM a (sinter alloc_to
     (ml_lookup (FST iter) (bb.bb_label,(ptr_owner_view d (EL t h)).cf_state.vs_inst_idx))
     (ml_lookup (SND iter) (bb.bb_label,(ptr_owner_view d (EL t h)).cf_state.vs_inst_idx)))` by
    (imp_res_tac ptr_ml_ordered_lookup >>
     qpat_assum `!addr. OL alloc_to (ml_lookup (FST iter) addr)`
       (qspec_then `(bb.bb_label,(ptr_owner_view d (EL t h)).cf_state.vs_inst_idx)`
         (mp_tac o MATCH_MP OL_INTER_IMP)) >>
     disch_then (qspec_then `ml_lookup (SND iter)
       (bb.bb_label,(ptr_owner_view d (EL t h)).cf_state.vs_inst_idx)` mp_tac) >>
     simp[EXTENSION] >> metis_tac[]) >>
  `context_mem_livesets (concretize_memloc_fuel fn) observed_ctx fn bp
      (cfg_analyze fn) =
    ml_mark_stores_live bp fn (ml_compute_livesets (FST iter) (SND iter) fn)` by
    simp[context_mem_livesets_def, mem_liveness_analyze_fuel_def,
         pairTheory.ELIM_UNCURRY, Abbr `iter`] >>
  qpat_assum `bp = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `context_mem_livesets _ _ _ _ _ = _` SUBST1_TAC >>
  irule ptr_marked_intersection >> metis_tac[]
QED

Theorem ptr_owner_context_store_conflict:
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed_ctx nm))) /\
  sizes = (\a. if context_alloca_size fn (imported_mems_used observed_ctx fn) a = 0
              then NONE else SOME (context_alloca_size fn (imported_mems_used observed_ctx fn) a)) /\
  ptr_chrono_history vs C h endpoint /\ u <= t /\ t <= r /\ r < LENGTH h /\
  (!k. u <= k /\ k <= r ==> d <= LENGTH (EL k h).po_stack) /\
  (ptr_owner_view d (EL u h)).cf_fn = fn /\
  wf_function fn /\ ptr_history_cfg_ok fn (cfg_analyze fn) /\
  ml_used_gen a bp mems (ptr_owner_view d (EL u h)).cf_inst /\
  ml_read_gen a bp mems (ptr_owner_view d (EL r h)).cf_inst /\
  (!k. t <= k /\ k < r ==>
    ~ptr_ml_can_kill a bp sizes (ptr_owner_view d (EL k h)).cf_inst) /\
  MEM b (find_base_allocas_opt bp
    (inst_write_op (ptr_owner_view d (EL t h)).cf_inst)) ==>
  ?xs ys.
    FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed_ctx fn bp (cfg_analyze fn)) a = SOME xs /\
    FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed_ctx fn bp (cfg_analyze fn)) b = SOME ys /\
    MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
         (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs /\
    MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
         (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) ys
Proof
  strip_tac >>
  drule_all ptr_owner_context_liveset >> strip_tac >>
  `!nm. OL alloc_to (mems nm)` by simp[ptr_incr_ssort_ordered] >>
  drule_all ptr_owner_two_demands >> strip_tac >>
  fs[active_inst_def] >>
  `MEM ((ptr_owner_view d (EL t h)).cf_state.vs_inst_idx,
        (ptr_owner_view d (EL t h)).cf_inst)
    (MAPi (\i inst. (i,inst)) bb.bb_instructions)` by simp[MEM_MAPi] >>
  `?ys. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed_ctx fn bp (cfg_analyze fn)) b = SOME ys /\
    MEM (bb.bb_label,(ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) ys` by
    (pure_rewrite_tac[context_mem_livesets_def, LET_THM] >> BETA_TAC >>
     irule ptr_fuel_liveness_covers_write >> metis_tac[]) >>
  metis_tac[]
QED
