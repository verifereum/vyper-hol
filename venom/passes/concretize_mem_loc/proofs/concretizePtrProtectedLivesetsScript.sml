Theory concretizePtrProtectedLivesets
Ancestors concretizePtrProtectedHistory concretizePtrOwnerDemand
  concretizePtrActualWrites
  concretizePtrOwnerConflict concretizePtrHistoryCfg concretizePtrBPOrigins
  concretizePtrOwnerPath concretizePtrChronologicalHistory
  o1PassContract ptrDiscipline concretizeMemLocDefs basePtrDefs
  list rich_list finite_map venomInst concretizePtrLifetime

Theorem ptr_endpoint_protected_livesets:
  ptr_chrono_history vs C h endpoint /\ vs.vs_allocas = FEMPTY /\
  o1_ctx_shape C /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= x /\ b <= x /\ x < b + sz /\ x NOTIN endpoint.po_taint.t_mem /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
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
  ?w. w + 1 < LENGTH h /\ ptr_chrono_write C x (EL w h) /\
    (!k. w < k /\ k + 1 < LENGTH h ==> ~ptr_chrono_write C x (EL k h)) /\
    (!t. w < t /\ t < LENGTH h ==>
      ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
          observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
        MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
             (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs) /\
    (!k. w <= k /\ k < LENGTH h ==>
      d <= LENGTH (EL k h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz) /\
      ~in_revert_forward (EL k h).po_fn (EL k h).po_state) /\
    ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
    ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bp = bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d endpoint).cf_fn)
    (cfg_analyze (ptr_owner_view d endpoint).cf_fn) (ptr_owner_view d endpoint).cf_fn` by metis_tac[] >>
  drule_all ptr_endpoint_protected_history >>
  disch_then (qspec_then `mems` strip_assume_tac) >>
  drule ptr_chrono_history_end >> strip_tac >>
  `PRE (LENGTH h) < LENGTH h /\ EL (PRE (LENGTH h)) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `!k. w <= k /\ k < LENGTH h ==> (ptr_owner_view d (EL k h)).cf_fn = fn` by
    (rpt strip_tac >>
     `(ptr_owner_view d (EL k h)).cf_fn = (ptr_owner_view d (EL (PRE (LENGTH h)) h)).cf_fn` by
       (irule ptr_owner_view_interval_function >> simp[] >>
        qexistsl [`C`,`endpoint`,`vs`] >> simp[] >>
        rpt strip_tac >> first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `wf_function fn /\ all_reachable fn` by
    (`MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     metis_tac[EVERY_MEM]) >>
  `ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)` by
    (rewrite_tac[ptr_bp_origins_def] >> metis_tac[ptr_bp_analyze_origins]) >>
  qexists `w` >> simp[] >> rpt strip_tac >>
  `!k. t <= k /\ k < PRE (LENGTH h) ==>
    ~ptr_ml_can_kill (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
      (\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0
           then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a))
      (ptr_owner_view d (EL k h)).cf_inst` by
    (gen_tac >> strip_tac >> irule ptr_stage_owner_interval_no_kill >>
     asm_rewrite_tac[] >> conj_tac
     >- (qexistsl [`b`,`x`,`t`,`PRE (LENGTH h)`,`sz`] >>
         simp[] >> rpt strip_tac >> spose_not_then strip_assume_tac >>
         `ptr_chrono_step C (EL k' h) (EL (SUC k') h)` by
           (irule ptr_chrono_history_adjacent >> simp[] >> metis_tac[]) >>
         `x IN range_bytes (source_memory_write_ranges (EL k' h).po_inst (EL k' h).po_state)` by
           (simp[range_bytes_def] >>
            qexistsl [`off`,`len`] >> simp[] >> decide_tac) >>
         `ptr_chrono_write C x (EL k' h)` by metis_tac[ptr_chrono_range_write] >>
         `w < k' /\ k' + 1 < LENGTH h` by decide_tac >>
         qpat_x_assum `!k. w < k /\ k + 1 < LENGTH h ==> _`
           (qspec_then `k'` mp_tac) >> simp[]) >>
     metis_tac[]) >>
  irule ptr_owner_context_liveset >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (irule ptr_history_cfg_analyze_ok >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl [`mems`,`PRE (LENGTH h)`] >>
  asm_rewrite_tac[] >>
  qexistsl [`\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0
                 then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)`,`w`] >>
  simp[] >>
  qpat_x_assum `fn = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `bp = _` SUBST_ALL_TAC >>
  qpat_x_assum `mems = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[]
QED

Theorem ptr_endpoint_actual_protected_livesets:
  ptr_chrono_history vs C h endpoint /\ vs.vs_allocas = FEMPTY /\
  o1_ctx_shape C /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= x /\ b <= x /\ x < b + sz /\ x NOTIN endpoint.po_taint.t_mem /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
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
  ?w. w + 1 < LENGTH h /\
    x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
                                  (EL (SUC w) h).po_state) /\
    x NOTIN (EL (SUC w) h).po_taint.t_mem /\
    (!k. w < k /\ k + 1 < LENGTH h ==>
      x NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
                                       (EL (SUC k) h).po_state)) /\
    (!t. w < t /\ t < LENGTH h ==>
      ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
          observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
        MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
             (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs) /\
    (!k. w <= k /\ k < LENGTH h ==>
      d <= LENGTH (EL k h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz) /\
      ~in_revert_forward (EL k h).po_fn (EL k h).po_state) /\
    ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
    ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bp = bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d endpoint).cf_fn)
    (cfg_analyze (ptr_owner_view d endpoint).cf_fn) (ptr_owner_view d endpoint).cf_fn` by metis_tac[] >>
  drule_all ptr_endpoint_actual_protected_history >>
  disch_then (qspec_then `mems` strip_assume_tac) >>
  drule ptr_chrono_history_end >> strip_tac >>
  `PRE (LENGTH h) < LENGTH h /\ EL (PRE (LENGTH h)) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `!k. w <= k /\ k < LENGTH h ==> (ptr_owner_view d (EL k h)).cf_fn = fn` by
    (rpt strip_tac >>
     `(ptr_owner_view d (EL k h)).cf_fn = (ptr_owner_view d (EL (PRE (LENGTH h)) h)).cf_fn` by
       (irule ptr_owner_view_interval_function >> simp[] >>
        qexistsl [`C`,`endpoint`,`vs`] >> simp[] >>
        rpt strip_tac >> first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `wf_function fn /\ all_reachable fn` by
    (`MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     metis_tac[EVERY_MEM]) >>
  `ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)` by
    (rewrite_tac[ptr_bp_origins_def] >> metis_tac[ptr_bp_analyze_origins]) >>
  qexists `w` >> simp[] >> rpt strip_tac >>
  `!k. t <= k /\ k < PRE (LENGTH h) ==>
    ~ptr_ml_can_kill (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
      (\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0
           then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a))
      (ptr_owner_view d (EL k h)).cf_inst` by
    (`w <= t` by decide_tac >>
     match_mp_tac (Q.INST [`byte` |-> `x`] ptr_stage_owner_actual_interval_no_kill) >>
     asm_rewrite_tac[] >> conj_tac >- decide_tac >>
     rpt conj_tac
     >- (rpt strip_tac >>
         `w <= k /\ k < LENGTH h` by decide_tac >> metis_tac[])
     >- metis_tac[]
     >- metis_tac[] >>
     rpt strip_tac
     >- (`w <= k /\ k < LENGTH h` by decide_tac >> metis_tac[]) >>
     `w < k /\ k + 1 < LENGTH h` by decide_tac >> metis_tac[]) >>
  irule ptr_owner_context_liveset >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (irule ptr_history_cfg_analyze_ok >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl [`mems`,`PRE (LENGTH h)`] >>
  asm_rewrite_tac[] >>
  qexistsl [`\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0
                 then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)`,`w`] >>
  simp[] >>
  qpat_x_assum `fn = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `bp = _` SUBST_ALL_TAC >>
  qpat_x_assum `mems = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[]
QED
