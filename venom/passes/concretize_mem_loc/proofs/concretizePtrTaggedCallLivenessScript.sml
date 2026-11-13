Theory concretizePtrTaggedCallLiveness
Ancestors concretizePtrTaggedCallOrigins concretizePtrTaggedOrigins
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrChronologicalHistory
  concretizePtrRuntimeGeneration concretizePtrOwnerConflict
  concretizePtrCallSeparation concretizePtrChronologicalDemand
  concretizePtrOwnerPath concretizePtrHistoryCfg concretizePtrProductionCoverage
  concretizeAnalysisLivenessTransfer concretizeAnalysisScanCoverage concretizeMemLocDefs
  ptrDiscipline venomWf venomInst list rich_list finite_map arithmetic

Theorem ptr_tagged_owner_singleton_liveset[local]:
  ptr_chrono_history vs C h a /\ d <= LENGTH a.po_stack /\
  (ptr_owner_view d a).cf_fn = fn /\ wf_function fn /\
  ptr_history_cfg_ok fn (cfg_analyze fn) /\
  ml_used_gen key
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed_ctx nm)))
    (ptr_owner_view d a).cf_inst /\
  ml_read_gen key
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed_ctx nm)))
    (ptr_owner_view d a).cf_inst ==>
  ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn) observed_ctx fn
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (cfg_analyze fn)) key = SOME xs /\
    MEM ((ptr_owner_view d a).cf_state.vs_current_bb,
      (ptr_owner_view d a).cf_state.vs_inst_idx) xs
Proof
  strip_tac >> drule ptr_chrono_history_end >> strip_tac >>
  `LENGTH h - 1 < LENGTH h /\ EL (LENGTH h - 1) h = a` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  qpat_assum `EL (LENGTH h - 1) h = a`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule ptr_owner_context_liveset >>
  simp[] >> reverse conj_tac
  >- (goal_assum $ drule_at Any) >>
  qexistsl [`LENGTH h - 1`, `LENGTH h - 1`] >>
  simp[] >> rpt strip_tac >>
  `k = LENGTH h - 1` by decide_tac >> gvs[]
QED

Theorem ptr_source_tagged_owner_call_liveset:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  n < LENGTH a.po_stack /\ EL (SUC n) tokens = owner /\
  FLOOKUP TG v = SOME (owner,aid) /\ fn = (EL n a.po_stack).cf_fn /\
  fn_ptr_ok P fn /\ ssa_form fn /\ wf_function fn /\ all_reachable fn /\
  fn_inst_wf fn /\ EVERY inst_wf (fn_insts fn) /\
  ptr_history_cfg_ok fn (cfg_analyze fn) ==>
  ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn) observed_ctx fn
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (cfg_analyze fn)) (Allocation aid) = SOME xs /\
    MEM ((EL n a.po_stack).cf_state.vs_current_bb,
      (EL n a.po_stack).cf_state.vs_inst_idx) xs
Proof
  strip_tac >>
  `fn_inst_wf (EL n a.po_stack).cf_fn` by metis_tac[] >>
  drule_all ptr_source_tagged_owner_call_operand >> strip_tac >>
  `ptr_chrono_history vs C h a` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations,
      ptr_source_activations_sound] >>
  `ptr_observation_reachable vs C a` by metis_tac[ptr_chrono_history_reachable] >>
  `MEM (EL n a.po_stack).cf_inst (fn_insts fn)` by
    (gvs[ptr_observation_reachable_def] >>
     drule ptr_frame_operand_instructions >> simp[EVERY_EL]) >>
  `ml_operand_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (EL n a.po_stack).cf_inst` by
    (irule ptr_production_operand_gen >> simp[] >>
     metis_tac[bp_scan_production_complete]) >>
  `(EL n a.po_stack).cf_inst.inst_opcode = INVOKE` by
    (gvs[ptr_observation_reachable_def] >>
     drule ptr_owner_frame_active >> simp[EVERY_EL]) >>
  `inst_wf (EL n a.po_stack).cf_inst` by metis_tac[EVERY_MEM] >>
  `?nm ops. (EL n a.po_stack).cf_inst.inst_operands = Label nm :: ops` by
    gvs[inst_wf_def] >>
  `ptr_owner_view (LENGTH a.po_stack - (n+1)) a = EL n a.po_stack` by
    simp[ptr_owner_view_def] >>
  qpat_assum `ptr_owner_view _ a = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule ptr_tagged_owner_singleton_liveset >>
  simp[ml_used_gen_def, ml_read_gen_def] >> metis_tac[]
QED

Theorem ptr_output_tagged_ancestor_destination_separation:
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
  static_alloca_items fn = SOME items /\ MEM (Allocation aid,sa) items /\
  MEM (Allocation aid,pa,sa) fn'.fn_mems_used /\ 0 < sa /\ 0 < sb /\
  (!c p sz. MEM (c,p,sz) (imported_mems_used observed.cu_context fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  ptr_source_ownership vs C prefix (EL t h) tokens registry births PT TG saved /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EL (SUC n) tokens = owner /\ FLOOKUP TG v = SOME (owner,aid) /\
  ssa_form fn /\ all_reachable fn /\ fn_inst_wf fn /\ EVERY inst_wf (fn_insts fn) ==>
  ?pb. MEM (Allocation bid,pb,sb) (imported_mems_used observed.cu_context fn) /\
    reserved_intervals_disjoint (pa,sa) (pb,sb)
Proof
  strip_tac >>
  `n < LENGTH (EL t h).po_stack /\ fn = (EL n (EL t h).po_stack).cf_fn` by
    metis_tac[] >>
  drule_all ptr_source_tagged_owner_call_liveset >>
  disch_then (qspec_then `observed.cu_context` strip_assume_tac) >>
  irule ptr_output_suspended_descendant_separation >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `ptr_chrono_history _ _ _ _`)) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
