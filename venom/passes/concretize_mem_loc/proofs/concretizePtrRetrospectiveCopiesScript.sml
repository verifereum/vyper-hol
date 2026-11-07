Theory concretizePtrRetrospectiveCopies
Ancestors concretizePtrRetrospectiveLocal concretizePtrRetrospectiveCalls
  concretizePtrProtectedLivesets concretizePtrCallSeparation concretizePtrLayoutOutput
  concretizePtrWriteFootprint concretizePtrOwnerPath concretizePtrHistoryCfg
  concretizePtrChronologicalHistory concretizeMemLocDefs ptrDiscipline
  o1PassContract basePtrDefs list indexedLists finite_map venomInst
  contextCodegenRel arithmetic pred_set staticLayoutDefs

Theorem ptr_endpoint_local_copy_exclusion:
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
    (!j bid sb pb ti ts post dst src cnt y z len delta.
      w < j /\ j + 1 < LENGTH h /\
      (EL j h).po_fn = fn /\ d = LENGTH (EL j h).po_stack /\
      bid <> aid /\ MEM (Allocation bid,sb) items /\
      MEM (Allocation bid,pb,sb) out.fpo_function.fn_mems_used /\
      MEM (Allocation bid) (find_base_allocas_opt bp (inst_write_op (EL j h).po_inst)) /\
      MEM ti.inst_opcode [MCOPY; CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY] /\
      ti.inst_operands = [dst;src;cnt] /\
      eval_operand dst ts = SOME y /\ eval_operand src ts = SOME z /\
      eval_operand cnt ts = SOME len /\
      w2n y = pb + delta /\ delta + w2n len <= sb ==>
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
  qexistsl [`delta`,`j`,`w2n len`,`w2n y`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> drule_all ptr_copy_footprint_interval >>
  disch_then (qspecl_then [`post`,`x`] mp_tac) >> simp[]
QED

Theorem ptr_endpoint_descendant_copy_exclusion:
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
    (!j n q desc ds bid db sb.
      w < j /\ j + 1 < LENGTH h /\
      n < LENGTH (EL j h).po_stack /\
      d = LENGTH (EL j h).po_stack - (n + 1) /\
      fn = (EL n (EL j h).po_stack).cf_fn /\ q <= n /\
      EL q (((EL j h).po_fn,(EL j h).po_state) ::
        MAP (\f. (f.cf_fn,f.cf_state)) (EL j h).po_stack) = (desc,ds) /\
      FLOOKUP ds.vs_allocas bid = SOME (db,sb) /\ 0 < sb ==>
      ?pb. MEM (Allocation bid,pb,sb) (imported_mems_used observed.cu_context fn) /\
        (!ti ts post dst src cnt y z len delta.
          MEM ti.inst_opcode [MCOPY; CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY] /\
          ti.inst_operands = [dst;src;cnt] /\
          eval_operand dst ts = SOME y /\ eval_operand src ts = SOME z /\
          eval_operand cnt ts = SOME len /\
          w2n y = pb + delta /\ delta + w2n len <= sb ==>
          pa + k NOTIN range_bytes (step_writes ti ts post)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_endpoint_descendant_interval_exclusion >> strip_tac >>
  qpat_x_assum `fn = _` (assume_tac o SYM) >>
  qexists `w` >> asm_rewrite_tac[] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!j n q desc ds bid db sb. _` (qspec_then `j` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  qexists `pb` >> asm_rewrite_tac[] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!start len delta footprint. _` irule >>
  qexistsl [`delta`,`w2n len`,`w2n y`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> drule_all ptr_copy_footprint_interval >>
  disch_then (qspecl_then [`post`,`x`] mp_tac) >> simp[]
QED
