Theory concretizePtrProtectedSeparation
Ancestors concretizePtrProtectedLivesets concretizePtrProductionSeparation
  concretizePtrOwnerPath concretizePtrStoreCoverage concretizePtrChronologicalHistory
  concretizeMemLocDefs ptrDiscipline o1PassContract basePtrDefs
  list indexedLists finite_map venomInst contextCodegenRel

Theorem ptr_endpoint_local_store_separation:
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
  EVERY fn_inst_wf C.ctx_functions /\
  fn_ptr_ok P fn /\ static_alloca_items fn = SOME items /\
  candidate = compute_alloc_map_fuel_in_context (concretize_memloc_fuel fn)
    observed.cu_context fn bp (cfg_analyze fn)
    (forced_candidate_positions items fn.fn_forced_alloc_positions FEMPTY) reserved /\
  complete_alloc_positions_with_imports items fn.fn_forced_alloc_positions
    reserved imported fn candidate = SOME completed /\
  (!c p sz. MEM (c,p,sz) (imported_mems_used observed.cu_context fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  MEM (Allocation aid,sa) items /\ MEM (other,sb) items /\
  Allocation aid <> other /\ 0 < sa /\ 0 < sb /\
  FLOOKUP completed (Allocation aid) = SOME pa /\ FLOOKUP completed other = SOME pb ==>
  ?w. w + 1 < LENGTH h /\ ptr_chrono_write C x (EL w h) /\
    (!k. w < k /\ k + 1 < LENGTH h ==> ~ptr_chrono_write C x (EL k h)) /\
    (!t. w < t /\ t < LENGTH h /\ (EL t h).po_fn = fn /\
      d = LENGTH (EL t h).po_stack /\
      MEM other (find_base_allocas_opt bp (inst_write_op (EL t h).po_inst)) ==>
      reserved_intervals_disjoint (pa,sa) (pb,sb))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_endpoint_protected_livesets >> strip_tac >>
  qexists `w` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!t. w < t /\ t < LENGTH h ==> _` (qspec_then `t` mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_observation_reachable vs C (EL t h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL]) >>
  `active_inst fn (EL t h).po_inst (EL t h).po_state` by
    (drule_at (Pat `ptr_observation_reachable _ _ _`) (cj 1 ptr_owner_view_active) >>
     disch_then (qspec_then `LENGTH (EL t h).po_stack` mp_tac) >> simp[]) >>
  gnvs[] >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `MEM ((EL t h).po_state.vs_inst_idx,(EL t h).po_inst)
    (MAPi (\i inst. (i,inst)) bb.bb_instructions)` by simp[MEM_MAPi] >>
  `?ys. FLOOKUP (context_mem_livesets (concretize_memloc_fuel (EL t h).po_fn)
      observed.cu_context (EL t h).po_fn
      (bp_analyze_fuel (concretize_memloc_fuel (EL t h).po_fn) (cfg_analyze (EL t h).po_fn) (EL t h).po_fn)
      (cfg_analyze (EL t h).po_fn)) other = SOME ys /\
    MEM (bb.bb_label,(EL t h).po_state.vs_inst_idx) ys` by
    (pure_rewrite_tac[context_mem_livesets_def, LET_THM] >> BETA_TAC >>
     irule ptr_fuel_liveness_covers_write >> metis_tac[]) >>
  qpat_x_assum `(EL t h).po_fn = _` SUBST_ALL_TAC >>
  irule ptr_production_completed_local_local >>
  asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `complete_alloc_positions_with_imports _ _ _ _ _ _ = SOME _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME pa`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME pb`)) >>
  goal_assum (drule_at (Pat `FLOOKUP (context_mem_livesets _ _ _ _ _) _ = SOME _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP (context_mem_livesets _ _ _ _ _) _ = SOME _`)) >>
  asm_rewrite_tac[] >>
  qexistsl [`P`,`(bb.bb_label,(EL t h).po_state.vs_inst_idx)`] >>
  metis_tac[]
QED
