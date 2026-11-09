Theory concretizePtrRetrospectiveLocal
Ancestors concretizePtrProtectedLivesets concretizePtrLayoutOutput
  concretizePtrStoreCoverage concretizePtrWriteFootprint concretizePtrOwnerPath
  concretizePtrChronologicalHistory concretizeMemLocDefs ptrDiscipline
  o1PassContract basePtrDefs list indexedLists finite_map venomInst
  contextCodegenRel arithmetic pred_set staticLayoutDefs

Theorem ptr_active_write_liveset:
  active_inst fn inst st /\
  MEM a (find_base_allocas_opt bp (inst_write_op inst)) ==>
  ?xs. FLOOKUP (context_mem_livesets fuel ctx fn bp (cfg_analyze fn)) a = SOME xs /\
    MEM (st.vs_current_bb,st.vs_inst_idx) xs
Proof
  simp[active_inst_def] >> strip_tac >>
  `MEM (st.vs_inst_idx,inst)
    (MAPi (\i inst. (i,inst)) bb.bb_instructions)` by simp[MEM_MAPi] >>
  qpat_x_assum `bb.bb_label = _` (SUBST_ALL_TAC o SYM) >>
  pure_rewrite_tac[context_mem_livesets_def, LET_THM] >> BETA_TAC >>
  irule ptr_fuel_liveness_covers_write >> metis_tac[]
QED

Theorem ptr_endpoint_local_interval_exclusion:
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
  lo <= b+k /\ k < sz /\ b+k NOTIN endpoint.po_taint.t_mem /\
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
  concretize_function_fuel_in_context (concretize_memloc_fuel fn)
    observed.cu_context reserved fn = SOME out.fpo_function /\
  fn_ptr_ok P fn /\ static_alloca_items fn = SOME items /\
  MEM (Allocation aid,sz) items /\
  MEM (Allocation aid,pa,sz) out.fpo_function.fn_mems_used /\
  (!c p size. MEM (c,p,size) (imported_mems_used observed.cu_context fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) ==>
  ?w. w + 1 < LENGTH h /\ ptr_chrono_write C (b+k) (EL w h) /\
    (!j. w < j /\ j + 1 < LENGTH h ==> ~ptr_chrono_write C (b+k) (EL j h)) /\
    (!j bid sb pb start len delta footprint.
      w < j /\ j + 1 < LENGTH h /\
      (EL j h).po_fn = fn /\ d = LENGTH (EL j h).po_stack /\
      bid <> aid /\ MEM (Allocation bid,sb) items /\
      MEM (Allocation bid,pb,sb) out.fpo_function.fn_mems_used /\
      MEM (Allocation bid) (find_base_allocas_opt bp (inst_write_op (EL j h).po_inst)) /\
      start = pb + delta /\ delta + len <= sb /\
      (!x. x IN footprint ==> start <= x /\ x < start + len) ==>
      pa + k NOTIN footprint)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `b <= b+k /\ b+k < b+sz` by decide_tac >>
  drule_all ptr_endpoint_protected_livesets >> strip_tac >>
  qpat_x_assum `fn = _` (assume_tac o SYM) >>
  qpat_x_assum `bp = _` (assume_tac o SYM) >>
  qexists `w` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!t. w < t /\ t < LENGTH h ==> _` (qspec_then `j` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  `ptr_observation_reachable vs C (EL j h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL]) >>
  `active_inst fn (EL j h).po_inst (EL j h).po_state` by
    (drule_at (Pat `ptr_observation_reachable _ _ _`) (cj 1 ptr_owner_view_active) >>
     disch_then (qspec_then `LENGTH (EL j h).po_stack` mp_tac) >> simp[]) >>
  `?ys. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed.cu_context fn bp (cfg_analyze fn)) (Allocation bid) = SOME ys /\
    MEM ((EL j h).po_state.vs_current_bb,(EL j h).po_state.vs_inst_idx) ys` by
    (irule ptr_active_write_liveset >> metis_tac[]) >>
  `MEM ((EL j h).po_state.vs_current_bb,(EL j h).po_state.vs_inst_idx) xs` by
    (qpat_x_assum `MEM (_,_) xs` mp_tac >> simp[ptr_owner_view_def]) >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `lookup_function _ C.ctx_functions = SOME fn` mp_tac >>
     disch_then (mp_tac o MATCH_MP lookup_function_MEM) >>
     qpat_x_assum `EVERY (\f. f.fn_eom = NONE) _` mp_tac >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `pb+delta <= pa+k /\ pa+k < pb+delta+len` by
    (qpat_x_assum `!x. x IN footprint ==> _` (qspec_then `pa+k` mp_tac) >>
     (impl_tac >- metis_tac[ADD_COMM]) >> decide_tac) >>
  `0 < sz /\ 0 < sb` by decide_tac >>
  `reserved_intervals_disjoint (pa,sz) (pb,sb)` by
    (irule ptr_output_local_local_separation >> asm_rewrite_tac[] >>
     goal_assum (drule_at (Pat `concretize_function_fuel_in_context _ _ _ _ = SOME _`)) >>
     goal_assum (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM (_,pa,sz) _`)) >>
     goal_assum (drule_at (Pat `MEM (_,pb,sb) _`)) >>
     asm_rewrite_tac[] >>
     qexistsl [`P`,`Allocation aid`,
       `((EL j h).po_state.vs_current_bb,(EL j h).po_state.vs_inst_idx)`,
       `items`,`xs`,`ys`] >> simp[]) >>
  fs[reserved_intervals_disjoint_def] >> decide_tac
QED

Theorem ptr_endpoint_local_mstore_exclusion:
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
  lo <= b+k /\ k < sz /\ b+k NOTIN endpoint.po_taint.t_mem /\
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
  concretize_function_fuel_in_context (concretize_memloc_fuel fn)
    observed.cu_context reserved fn = SOME out.fpo_function /\
  fn_ptr_ok P fn /\ static_alloca_items fn = SOME items /\
  MEM (Allocation aid,sz) items /\
  MEM (Allocation aid,pa,sz) out.fpo_function.fn_mems_used /\
  (!c p size. MEM (c,p,size) (imported_mems_used observed.cu_context fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) ==>
  ?w. w + 1 < LENGTH h /\ ptr_chrono_write C (b+k) (EL w h) /\
    (!j. w < j /\ j + 1 < LENGTH h ==> ~ptr_chrono_write C (b+k) (EL j h)) /\
    (!j bid sb pb ti ts post ta tv y value delta.
      w < j /\ j + 1 < LENGTH h /\
      (EL j h).po_fn = fn /\ d = LENGTH (EL j h).po_stack /\
      bid <> aid /\ MEM (Allocation bid,sb) items /\
      MEM (Allocation bid,pb,sb) out.fpo_function.fn_mems_used /\
      MEM (Allocation bid) (find_base_allocas_opt bp (inst_write_op (EL j h).po_inst)) /\
      ti.inst_opcode = MSTORE /\ ti.inst_operands = [ta;tv] /\
      eval_operand ta ts = SOME y /\ eval_operand tv ts = SOME value /\
      w2n y = pb + delta /\ delta + 32 <= sb ==>
      pa + k NOTIN range_bytes (step_writes ti ts post))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_endpoint_local_interval_exclusion >> strip_tac >>
  qpat_x_assum `fn = _` (assume_tac o SYM) >>
  qpat_x_assum `bp = _` (assume_tac o SYM) >>
  qexists `w` >> asm_rewrite_tac[] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!j bid sb pb start len delta footprint. _` irule >> asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `MEM (Allocation bid,_,_) _`)) >>
  asm_rewrite_tac[] >>
  qexistsl [`delta`,`j`,`32`,`w2n y`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> drule_all ptr_mstore_footprint_interval >>
  disch_then (qspecl_then [`post`,`x`] mp_tac) >> simp[]
QED
