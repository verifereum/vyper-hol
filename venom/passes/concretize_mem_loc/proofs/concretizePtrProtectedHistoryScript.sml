Theory concretizePtrProtectedHistory
Ancestors venomWfProps concretizePtrEndpointOrigin concretizePtrOwnerSeeds
  concretizePtrOwnedActualInitializer concretizePtrHistoryDemand
  concretizePtrRevertHistory concretizePtrOwnerPath
  concretizePtrActivationSupport contextCodegenRel removeUnusedSsaProofs
  concretizePtrChronologicalHistory concretizePtrLifetime venomInst ptrDiscipline
  list rich_list finite_map

Theorem ptr_list_split[local]:
  !i h. i < LENGTH h ==> h = TAKE i h ++ [EL i h] ++ DROP (SUC i) h
Proof
  Induct >> Cases >> simp[listTheory.APPEND, listTheory.TAKE_def, listTheory.DROP_def]
QED

Theorem ptr_history_no_dalloca[local]:
  ptr_chrono_history vs C h endpoint /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions ==>
  !k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA
Proof
  strip_tac >> drule ptr_chrono_history_reachable >>
  simp[EVERY_EL] >> strip_tac >> rpt strip_tac >>
  `ptr_observation_reachable vs C (EL k h)` by metis_tac[] >>
  fs[ptr_observation_reachable_def] >>
  drule_all ptr_frame_table_support_invariant >> strip_tac >>
  drule ptr_owner_frame_active >> strip_tac >>
  `MEM (EL k h).po_inst (fn_insts (EL k h).po_fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[MEM_EL]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_endpoint_protected_history:
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
  bp = bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d endpoint).cf_fn)
    (cfg_analyze (ptr_owner_view d endpoint).cf_fn) (ptr_owner_view d endpoint).cf_fn ==>
  ?w. w + 1 < LENGTH h /\ ptr_chrono_write C x (EL w h) /\
    (!k. w <= k /\ k < LENGTH h ==>
      d <= LENGTH (EL k h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz) /\
      ~in_revert_forward (EL k h).po_fn (EL k h).po_state) /\
    (!k. w < k /\ k + 1 < LENGTH h ==> ~ptr_chrono_write C x (EL k h)) /\
    ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
    ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA` by
    metis_tac[ptr_history_no_dalloca] >>
  drule ptr_chrono_history_end >> strip_tac >>
  `PRE (LENGTH h) < LENGTH h /\ EL (PRE (LENGTH h)) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `?i fuel sa'. i < PRE (LENGTH h) /\ LENGTH (EL i h).po_stack = d /\
    (EL i h).po_inst.inst_opcode = ALLOCA /\ (EL i h).po_inst.inst_id = aid /\
    FLOOKUP (EL i h).po_state.vs_allocas aid = NONE /\
    step_inst fuel C (EL i h).po_inst (EL i h).po_state = OK sa' /\
    FLOOKUP sa'.vs_allocas aid = SOME (b,sz) /\
    (!k. i <= k /\ k <= PRE (LENGTH h) ==> d <= LENGTH (EL k h).po_stack) /\
    FLOOKUP (ptr_bottom_state d (EL (SUC i) h)).vs_allocas aid = SOME (b,sz)` by
    (irule ptr_chrono_endpoint_birth >>
     simp[GSYM ptr_owner_view_state] >> metis_tac[]) >>
  `i < LENGTH h /\ SUC i < LENGTH h` by decide_tac >>
  `h = TAKE i h ++ [EL i h] ++ DROP (SUC i) h` by
    simp[ptr_list_split] >>
  `DROP (SUC i) h <> []` by
    (Cases_on `DROP (SUC i) h` >> fs[LENGTH_DROP]) >>
  `x IN new_site_bytes (EL i h).po_state sa'` by
    (simp[new_site_bytes_def] >> disj1_tac >>
     qexistsl_tac [`aid`,`b`,`sz`] >> fs[FLOOKUP_DEF]) >>
  `?w. i < w /\ w + 1 < LENGTH h /\ ptr_chrono_write C x (EL w h) /\
    ptr_observation_reachable vs C (EL w h) /\
    (!k. w < k /\ k + 1 < LENGTH h ==> ~ptr_chrono_write C x (EL k h))` by
    (drule_all ptr_chrono_fresh_last_write_index >> simp[LENGTH_TAKE]) >>
  qpat_x_assum `h = _` kall_tac >>
  `!k. w <= k /\ k < LENGTH h ==> d <= LENGTH (EL k h).po_stack` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!k. w <= k /\ k < LENGTH h ==>
    FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz)` by
    (rpt strip_tac >> irule ptr_owner_view_lookup_interval >>
     simp[] >> conj_tac
     >- (qexists `SUC i` >> simp[ptr_owner_view_state]) >>
     metis_tac[]) >>
  drule_all ptr_chrono_ordinary_non_revert >> simp[EVERY_EL] >> strip_tac >>
  `(ptr_owner_view d (EL w h)).cf_fn = (ptr_owner_view d endpoint).cf_fn` by
    (qpat_x_assum `EL (PRE (LENGTH h)) h = endpoint` (fn th =>
       once_rewrite_tac[GSYM th]) >>
     irule ptr_owner_view_interval_function >> simp[] >> metis_tac[]) >>
  `ptr_observation_reachable vs C endpoint` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >> metis_tac[]) >>
  `0 < sz` by decide_tac >>
  `ml_read_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d endpoint).cf_fn)
      (cfg_analyze (ptr_owner_view d endpoint).cf_fn) (ptr_owner_view d endpoint).cf_fn)
    mems (ptr_owner_view d endpoint).cf_inst` by
    (irule ptr_owner_selected_read_seed >> simp[] >> metis_tac[]) >>
  qexists `w` >> simp[] >>
  qpat_x_assum `(ptr_owner_view d (EL w h)).cf_fn = _` (fn th =>
    once_rewrite_tac[GSYM th]) >>
  irule ptr_owner_write_byte_seed >>
  simp[] >> conj_tac
  >- metis_tac[] >>
  qexistsl_tac [`lo`,`x`] >> simp[] >>
  qpat_x_assum `ptr_chrono_write C x (EL w h)` mp_tac >>
  simp[ptr_chrono_write_def] >> strip_tac >>
  first_x_assum irule >> simp[MEM_EL] >> qexists `w` >> simp[]
QED

Theorem ptr_endpoint_actual_protected_history:
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
  bp = bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d endpoint).cf_fn)
    (cfg_analyze (ptr_owner_view d endpoint).cf_fn) (ptr_owner_view d endpoint).cf_fn ==>
  ?w. w + 1 < LENGTH h /\
    x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
                                  (EL (SUC w) h).po_state) /\
    x NOTIN (EL (SUC w) h).po_taint.t_mem /\
    (!k. w <= k /\ k < LENGTH h ==>
      d <= LENGTH (EL k h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz) /\
      ~in_revert_forward (EL k h).po_fn (EL k h).po_state) /\
    (!k. w < k /\ k + 1 < LENGTH h ==>
      x NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
                                       (EL (SUC k) h).po_state)) /\
    ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
    ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA` by
    metis_tac[ptr_history_no_dalloca] >>
  drule_all ptr_endpoint_owned_actual_initializer >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `PRE (LENGTH h) < LENGTH h /\ EL (PRE (LENGTH h)) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  drule_all ptr_chrono_ordinary_non_revert >> simp[EVERY_EL] >> strip_tac >>
  `(ptr_owner_view d (EL w h)).cf_fn = (ptr_owner_view d endpoint).cf_fn` by
    (qpat_x_assum `EL (PRE (LENGTH h)) h = endpoint` (fn th =>
       once_rewrite_tac[GSYM th]) >>
     irule ptr_owner_view_interval_function >> simp[] >> metis_tac[]) >>
  `ptr_observation_reachable vs C endpoint` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >> metis_tac[]) >>
  `ptr_observation_reachable vs C (EL w h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >> metis_tac[]) >>
  `0 < sz` by decide_tac >>
  `ml_read_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d endpoint).cf_fn)
      (cfg_analyze (ptr_owner_view d endpoint).cf_fn) (ptr_owner_view d endpoint).cf_fn)
    mems (ptr_owner_view d endpoint).cf_inst` by
    (irule ptr_owner_selected_read_seed >> simp[] >> metis_tac[]) >>
  qexists `w` >> simp[arithmeticTheory.ADD1] >>
  qpat_x_assum `(ptr_owner_view d (EL w h)).cf_fn = _` (fn th =>
    once_rewrite_tac[GSYM th]) >>
  irule ptr_owner_write_byte_seed >> simp[] >> conj_tac
  >- metis_tac[] >>
  qexistsl [`lo`,`x`] >> simp[] >> reverse conj_tac
  >- (first_x_assum irule >> simp[MEM_EL] >> qexists `w` >> simp[]) >>
  drule (REWRITE_RULE [pred_setTheory.SUBSET_DEF] ptr_step_writes_subset) >> simp[]
QED
