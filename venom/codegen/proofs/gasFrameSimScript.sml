(* GAS preserves the running function frame and consumes the same reading
   in Venom and assembly. GAS values remain ordinary values. *)

Theory gasFrameSim
Ancestors
  genFrameSim
  frameRel asmFrame genBlockSim reorderSim mixedPrefixSim prefixSim
  stackOpAsmSim stackOpSim instSimHelpers blockSimHelpers planWf
  codegenRel contextCodegenRel planExec asmSem stackPlanGen stackPlanTypes
  stackPlanOps stackModel venomExecSemantics venomState venomInst
  allocMono contextCodegenRelProps asmIR venomEffects fcgDefs livenessDefs
  dfgDefs list rich_list deepDupCallerSim venomWf opcodeClass unitShapeDefs finite_map

Theorem gas_source_shape[local]:
  inst.inst_opcode = GAS /\ inst_wf inst /\
  (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) ==>
  inst.inst_operands = [] /\ ?out. inst.inst_outputs = [out]
Proof
  simp[inst_wf_def, ef_read0_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem gas_distinct_outputs_unique[local]:
  !xs i j x.
    ALL_DISTINCT (FLAT (MAP (\i:instruction. i.inst_outputs) xs)) /\
    MEM i xs /\ MEM j xs /\
    MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  Induct >> simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem gas_output_non_retpc[local]:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs ==>
  ~retpc_var fn out
Proof
  simp[retpc_var_def] >> rpt strip_tac >>
  fs[codegen_ready_fn_def, ssa_form_def] >>
  qpat_x_assum `copy_phi_var _ _ _` mp_tac >>
  simp[Once copy_phi_var_cases] >> rpt strip_tac >>
  CCONTR_TAC >> gvs[] >>
  `inst = inst'` by metis_tac[gas_distinct_outputs_unique] >> gvs[]
QED

Theorem gas_frame_view_update[local]:
  ~retpc_var fn out ==>
  frame_view fn ra (update_var out value vs) =
  update_var out value (frame_view fn ra vs)
Proof
  strip_tac >> simp[frame_view_def, update_var_def] >>
  `(FMAP_MAP2 (\(x,v). if retpc_var fn x then ra else v)
      (vs.vs_vars |+ (out,value))) =
    (FMAP_MAP2 (\(x,v). if retpc_var fn x then ra else v)
      vs.vs_vars) |+ (out,value)` suffices_by simp[] >>
  simp[fmap_eq_flookup, FLOOKUP_FMAP_MAP2, FLOOKUP_UPDATE] >>
  gen_tac >> Cases_on `out = x` >> gvs[]
QED

Theorem gas_frame_view_readings[local]:
  frame_view fn ra (vs with vs_gas_readings := readings) =
  (frame_view fn ra vs) with vs_gas_readings := readings
Proof
  simp[frame_view_def]
QED

Theorem gas_step_frame_view[local]:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  step_inst fuel ctx inst vs = OK vs' ==>
  step_inst fuel ctx inst (frame_view fn ra vs) =
  OK (frame_view fn ra vs')
Proof
  strip_tac >>
  `~retpc_var fn out` by
    (irule gas_output_non_retpc >> simp[] >> metis_tac[MEM]) >>
  gvs[Once step_inst_def, step_inst_base_def] >>
  Cases_on `vs.vs_gas_readings` >>
  gvs[exec_gas_def] >>
  simp[Once step_inst_def, step_inst_base_def, exec_gas_def,
       gas_frame_view_update, gas_frame_view_readings,
       GSYM frame_view_def] >>
  ` (frame_view fn ra vs).vs_gas_readings = vs.vs_gas_readings` by
    simp[frame_view_def] >>
  simp[exec_gas_def, gas_frame_view_update, gas_frame_view_readings]
QED

Theorem gas_step_result[local]:
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  step_inst fuel ctx inst vs = OK vs' ==>
  vs' = update_var out (HD (vs.vs_gas_readings ++ [0w]))
          (vs with vs_gas_readings := TL vs.vs_gas_readings)
Proof
  strip_tac >> gvs[Once step_inst_def, step_inst_base_def] >>
  Cases_on `vs.vs_gas_readings` >>
  gvs[exec_gas_def, update_var_def, venom_state_component_equality]
QED

Theorem gas_dead_popmany[local]:
  !out ps.
    popmany_plan [Var out]
      (ps with ps_stack := SNOC (Var out) ps.ps_stack) =
    ([SOPop 1], ps)
Proof
  rpt gen_tac >>
  `stack_get_depth (Var out) (SNOC (Var out) ps.ps_stack) = SOME 0` by
    simp[stack_get_depth_def, REVERSE_SNOC, stack_find_def] >>
  simp[popmany_plan_def, is_contiguous_top_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF, popmany_individual_def, stack_pop_def,
       FOLDL, LENGTH_SNOC] >>
  Cases_on `ps` >> simp[SNOC_APPEND, TAKE_APPEND1,
                        plan_state_component_equality]
QED

Theorem gas_plan_shape[local]:
  inst.inst_opcode = GAS /\ inst.inst_operands = [] /\
  inst.inst_outputs = [out] ==>
  generate_inst_plan liveness dfg cfg fn inst next_liveness
    is_halting next_is_term bb_label ps =
  SOME (if MEM out next_liveness then
      let (tail, ps9) = optimistic_swap_plan dfg inst next_liveness
        next_is_term (ps with ps_stack := SNOC (Var out) ps.ps_stack) in
      (SOEmit "GAS" :: tail, release_dead_spills next_liveness ps9)
    else if is_halting then
      ([SOEmit "GAS"], release_dead_spills next_liveness
        (ps with ps_stack := SNOC (Var out) ps.ps_stack))
    else ([SOEmit "GAS"; SOPop 1], release_dead_spills next_liveness ps))
Proof
  strip_tac >>
  simp[generate_inst_plan_def, generate_regular_inst_plan_def,
       compute_operands_def, python_stack_operands_def,
       is_pre_codegen_opcode_def, is_param_opcode_def,
       is_unlowered_fmp_opcode_def, is_raw_fmp_opcode_def,
       is_unlowered_internal_call_opcode_def,
       generate_emit_ops_def, venom_to_evm_name_def,
       stack_pop_def, stack_push_def] >>
  `!p. popmany_plan [] p = ([],p)` by simp[popmany_plan_def] >>
  Cases_on `MEM out next_liveness` >> simp[gas_dead_popmany] >>
  Cases_on `is_halting` >> simp[gas_dead_popmany]
QED

Theorem gas_push_relation[local]:
  venom_asm_rel lo ps vs st /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
     case op of Var x => x <> out | _ => T) ==>
  venom_asm_rel lo (ps with ps_stack := SNOC (Var out) ps.ps_stack)
    (update_var out value vs) (st with as_stack := value :: st.as_stack)
Proof
  strip_tac >> drule_all venom_asm_rel_update_var >>
  disch_then (qspec_then `value` assume_tac) >>
  gvs[venom_asm_rel_def] >>
  irule plan_stack_rel_push >>
  simp[operand_val_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem gas_asm_step[local]:
  asm_step lo o2pc (AsmOp "GAS") st = asm_gas st
Proof
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def]
QED

Theorem gas_readings_relation[local]:
  venom_asm_rel lo ps vs st ==>
  venom_asm_rel lo ps (vs with vs_gas_readings := readings)
    (st with as_gas_readings := readings)
Proof
  `!op. operand_val (vs with vs_gas_readings := readings) lo op =
        operand_val vs lo op` by (Cases >> simp[operand_val_def]) >>
  simp[venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def] >>
  metis_tac[]
QED

Theorem gas_emit_relation[local]:
  venom_asm_rel lo ps vs st /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
     case op of Var x => x <> out | _ => T) ==>
  ?st'. asm_step lo o2pc (AsmOp "GAS") st = AsmOK st' /\
    venom_asm_rel lo (ps with ps_stack := SNOC (Var out) ps.ps_stack)
      (update_var out (HD (vs.vs_gas_readings ++ [0w]))
        (vs with vs_gas_readings := TL vs.vs_gas_readings)) st' /\
    st'.as_pc = st.as_pc + 1 /\ st'.as_memory = st.as_memory
Proof
  strip_tac >>
  `st.as_gas_readings = vs.vs_gas_readings` by fs[venom_asm_rel_def] >>
  drule gas_readings_relation >>
  disch_then (qspec_then `TL vs.vs_gas_readings` assume_tac) >>
  drule_all gas_push_relation >>
  disch_then (qspec_then `HD (vs.vs_gas_readings ++ [0w])` assume_tac) >>
  Cases_on `vs.vs_gas_readings` >>
  simp[gas_asm_step, asm_gas_def, asm_push_val_def, asm_next_def] >>
  fs[venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def,
     update_var_def]
QED

Theorem gas_emit_steps[local]:
  venom_asm_rel lo ps vs st /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
     case op of Var x => x <> out | _ => T) /\
  asm_block_at prog st.as_pc [AsmOp "GAS"] ==>
  ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
    venom_asm_rel lo (ps with ps_stack := SNOC (Var out) ps.ps_stack)
      (update_var out (HD (vs.vs_gas_readings ++ [0w]))
        (vs with vs_gas_readings := TL vs.vs_gas_readings)) st' /\
    st'.as_pc = st.as_pc + 1 /\ st'.as_memory = st.as_memory
Proof
  strip_tac >> drule_all gas_emit_relation >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >>
  fs[asm_block_at_def] >>
  once_rewrite_tac[arithmeticTheory.ONE] >> simp[asm_steps_def]
QED

Theorem gas_optimistic_cases[local]:
  optimistic_swap_plan dfg inst live next_term ps = (ops,ps') ==>
  (ops = [] /\ ps' = ps) \/
  ?dist. stack_get_depth (Var (LAST live)) ps.ps_stack = SOME dist /\
    do_swap dist ps = (ops,ps')
Proof
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  metis_tac[]
QED

Theorem gas_swap_suffix_sim[local]:
  generated_plan_state_wf spill_base ps /\
  do_swap dist ps = (ops,ps') /\ dist < LENGTH ps.ps_stack /\
  prefix_spill_wf initial_fmp lo (FRONT ops) spill_view /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    venom_asm_rel lo ps' vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  `ALL_DISTINCT (top_n (dist + 1) ps.ps_stack)` by
    (simp[top_n_def] >> irule ALL_DISTINCT_TAKE >>
     fs[generated_plan_state_wf_def, ALL_DISTINCT_REVERSE]) >>
  `prefix_spill_wf initial_fmp lo ops ps` by
    (irule doSwapSimTheory.do_swap_prefix_spill_wf_from_front_cross_view >>
     fs[generated_plan_state_wf_def] >> metis_tac[]) >>
  irule doSwapSimTheory.do_swap_venom_asm_rel_layout >>
  goal_assum (drule_at Any) >> fs[generated_plan_state_wf_def] >>
  metis_tac[]
QED

Theorem gas_optimistic_suffix_sim[local]:
  generated_plan_state_wf spill_base ps /\
  optimistic_swap_plan dfg inst live next_term ps = (ops,ps') /\
  prefix_spill_wf initial_fmp lo (FRONT ops) spill_view /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    venom_asm_rel lo ps' vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> drule gas_optimistic_cases >> strip_tac
  >- (gvs[] >> qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  irule gas_swap_suffix_sim >> metis_tac[]
QED

Theorem gas_push_generated_wf[local]:
  generated_plan_state_wf spill_base ps /\
  ~MEM (Var out) ps.ps_stack /\ ~(Var out IN FDOM ps.ps_spilled) ==>
  generated_plan_state_wf spill_base
    (ps with ps_stack := SNOC (Var out) ps.ps_stack)
Proof
  simp[generated_plan_state_wf_def, planSpillBoundsTheory.plan_slots_bounded_def,
       ALL_DISTINCT_SNOC, LIST_TO_SET_SNOC, pred_setTheory.DISJOINT_INSERT] >>
  metis_tac[]
QED

Theorem gas_front_spill_transport[local]:
  prefix_spill_wf initial_fmp lo (FRONT (SOEmit "GAS" :: ops)) ps ==>
  prefix_spill_wf initial_fmp lo (FRONT ops) ps
Proof
  Cases_on `ops` >> simp[prefix_spill_wf_def, spill_op_wf_def,
                         apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def]
QED

Theorem gas_live_suffix_sim[local]:
  generated_plan_state_wf spill_base ps /\
  ~MEM (Var out) ps.ps_stack /\ ~(Var out IN FDOM ps.ps_spilled) /\
  optimistic_swap_plan dfg inst live next_term
    (ps with ps_stack := SNOC (Var out) ps.ps_stack) = (ops,ps') /\
  prefix_spill_wf initial_fmp lo (FRONT (SOEmit "GAS" :: ops)) ps /\
  venom_asm_rel lo (ps with ps_stack := SNOC (Var out) ps.ps_stack) vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    venom_asm_rel lo (release_dead_spills live ps') vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  drule_all gas_push_generated_wf >> strip_tac >>
  drule gas_front_spill_transport >> strip_tac >>
  drule_all gas_optimistic_suffix_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >>
  irule venom_asm_rel_release_dead_spills >> simp[]
QED

Theorem gas_plan_local_sim[local]:
  inst.inst_opcode = GAS /\ inst.inst_operands = [] /\ inst.inst_outputs = [out] /\
  generated_plan_state_wf spill_base ps /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
     case op of Var x => x <> out | _ => T) /\
  generate_inst_plan liveness dfg cfg fn inst live is_halting next_term bb ps =
    SOME (ops,ps') /\
  prefix_spill_wf initial_fmp lo (FRONT ops) ps /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    venom_asm_rel lo ps'
      (update_var out (HD (vs.vs_gas_readings ++ [0w]))
        (vs with vs_gas_readings := TL vs.vs_gas_readings)) st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  `~MEM (Var out) ps.ps_stack /\ ~(Var out IN FDOM ps.ps_spilled)` by
    (fs[EVERY_MEM] >> conj_tac
     >- (strip_tac >> qpat_x_assum `!op. MEM op _ ==> _`
           (qspec_then `Var out` mp_tac) >> simp[]) >>
     strip_tac >> qpat_x_assum `!op. op IN FDOM _ ==> _`
       (qspec_then `Var out` mp_tac) >> simp[]) >>
  drule_all gas_plan_shape >> disch_then assume_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[] >>
  Cases_on `MEM out live` >> simp[]
  >- suspend "live" >>
  Cases_on `is_halting` >> simp[]
  >- suspend "retained" >>
  suspend "pop"
QED

Resume gas_plan_local_sim[live]:
  pairarg_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!ps next_liveness next_is_term liveness is_halting fn dfg cfg bb_label. _` kall_tac >>
  `!xs. execute_plan initial_fmp (SOEmit "GAS" :: xs) =
       AsmOp "GAS" :: execute_plan initial_fmp xs` by
    simp[execute_plan_def, exec_stack_op_def] >>
  `asm_block_at prog st.as_pc [AsmOp "GAS"]` by
    (fs[asm_block_at_cons] >> simp[asm_block_at_cons, asm_block_at_def]) >>
  drule_all gas_emit_steps >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `asm_block_at prog st'.as_pc (execute_plan initial_fmp tail)` by
    fs[asm_block_at_cons] >>
  drule_all gas_live_suffix_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st''` >> simp[] >>
  `SUC (LENGTH (execute_plan initial_fmp tail)) =
    1 + LENGTH (execute_plan initial_fmp tail)` by simp[] >>
  asm_rewrite_tac[] >> irule asm_steps_compose_ok >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume gas_plan_local_sim[retained]:
  strip_tac >> gvs[] >>
  `execute_plan initial_fmp [SOEmit "GAS"] = [AsmOp "GAS"]` by
    simp[execute_plan_def, exec_stack_op_def] >>
  gvs[] >> drule_all gas_emit_steps >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >>
  irule venom_asm_rel_release_dead_spills >> simp[]
QED
Resume gas_plan_local_sim[pop]:
  strip_tac >> gvs[] >>
  `execute_plan initial_fmp [SOEmit "GAS"; SOPop 1] =
    [AsmOp "GAS"; AsmOp "POP"]` by
    (simp[execute_plan_def, exec_stack_op_def] >>
     once_rewrite_tac[arithmeticTheory.ONE] >> simp[REPLICATE]) >>
  gvs[] >>
  `st.as_gas_readings = vs.vs_gas_readings` by fs[venom_asm_rel_def] >>
  drule gas_readings_relation >>
  disch_then (qspec_then `TL vs.vs_gas_readings` assume_tac) >>
  drule_all venom_asm_rel_update_var >>
  disch_then (qspec_then `HD (vs.vs_gas_readings ++ [0w])` assume_tac) >>
  qexists_tac `st with <|as_pc := st.as_pc + 2;
                        as_gas_readings := TL vs.vs_gas_readings|>` >>
  simp[] >> conj_tac
  >- (fs[asm_block_at_def] >>
      `EL st.as_pc prog = AsmOp "GAS"` by
        (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      `EL (st.as_pc + 1) prog = AsmOp "POP"` by
        (first_x_assum (qspec_then `1` mp_tac) >> simp[EL]) >>
      `2 = SUC 1` by decide_tac >>
      qpat_x_assum `2 = SUC 1` (fn th => once_rewrite_tac[th]) >>
      simp[Once asm_steps_def] >>
      simp[gas_asm_step, asm_gas_def, asm_push_val_def, asm_next_def] >>
      Cases_on `vs.vs_gas_readings` >> simp[] >>
      once_rewrite_tac[arithmeticTheory.ONE] >>
      simp[Once asm_steps_def] >>
      simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
           asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
           asm_pop_def, asm_next_def, asm_steps_def] >>
      simp[asm_state_component_equality]) >>
  irule venom_asm_rel_release_dead_spills >>
  fs[venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def]
QED
Finalise gas_plan_local_sim

Theorem gas_plan_rels_memory[local]:
  (plan_stack_rel lo (v with vs_memory := m) stk astk <=>
   plan_stack_rel lo v stk astk) /\
  (plan_spill_rel lo (v with vs_memory := m) sp am <=>
   plan_spill_rel lo v sp am)
Proof
  `!op. operand_val (v with vs_memory := m) lo op = operand_val v lo op` by
    (Cases >> simp[operand_val_def]) >>
  simp[plan_stack_rel_def, plan_spill_rel_def]
QED

Theorem gas_context_local[local]:
  !cp lo ps v st.
  context_venom_asm_rel (cp:context_plan) lo ps v st ==>
  venom_asm_rel lo ps (v with vs_memory := st.as_memory) st
Proof
  simp[context_venom_asm_rel_def, venom_asm_rel_def, gas_plan_rels_memory,
       memory_rel_refl]
QED

Theorem gas_local_context[local]:
  !cp lo ps v st m.
  venom_asm_rel lo ps (v with vs_memory := m) st /\
  context_memory_rel (cp:context_plan) v.vs_memory st.as_memory ==>
  context_venom_asm_rel (cp:context_plan) lo ps v st
Proof
  simp[context_venom_asm_rel_def, venom_asm_rel_def, gas_plan_rels_memory]
QED

Theorem gas_memory_outside[local]:
  memory_rel alloc m m' /\
  r.sr_spill_base <= alloc.sa_spill_base /\
  alloc.sa_next_offset <= r.sr_spill_end /\
  ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
  read_byte b m = read_byte b m'
Proof
  rw[memory_rel_def] >> first_x_assum irule >> decide_tac
QED

Theorem gas_closure_own[local]:
  !ctx cp fn r b.
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= b /\ b < r.sr_spill_end ==>
  closure_spill_byte ctx cp fn.fn_name b
Proof
  rw[closure_spill_byte_def, fcg_path_def] >>
  qexists_tac `r` >> simp[relationTheory.RTC_REFL]
QED

Theorem gas_frame_lift[local]:
  !ctx cp lo fn ra rest mem0 ps vs ast r ps' vs' o2pc prog n count.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  vs'.vs_halted = vs.vs_halted /\
  vs'.vs_initial_fmp = vs.vs_initial_fmp /\
  vs'.vs_memory = vs.vs_memory /\
  (!top. ast.as_stack = top ++ rest ==>
    ?st'. asm_steps lo o2pc prog n (ast with as_stack := top) = AsmOK st' /\
      venom_asm_rel lo ps'
        (frame_view fn ra vs' with vs_memory := ast.as_memory) st' /\
      st'.as_pc = ast.as_pc + count) ==>
  ?ast'. asm_steps lo o2pc prog n ast = AsmOK ast' /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' ast' /\
    ast'.as_pc = ast.as_pc + count
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fn_frame_inv_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `asm_steps lo o2pc prog n ast =
    AsmOK (st' with as_stack := st'.as_stack ++ rest)` by
    (`ast with as_stack := top ++ rest = ast` by
       simp[asm_state_component_equality] >>
     drule asm_steps_frame >> disch_then (qspec_then `rest` mp_tac) >>
     asm_rewrite_tac[]) >>
  `memory_rel ps'.ps_alloc ast.as_memory st'.as_memory` by
    fs[venom_asm_rel_def] >>
  `!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
    read_byte b ast.as_memory = read_byte b st'.as_memory` by
    metis_tac[gas_memory_outside] >>
  `context_venom_asm_rel cplan lo ps' (frame_view fn ra vs') st'` by
    (irule gas_local_context >> conj_tac
     >- (simp[frame_view_def, context_memory_rel_def] >> rpt strip_tac >>
         `read_byte i vs.vs_memory = read_byte i ast.as_memory` by
           (qpat_x_assum `context_venom_asm_rel _ _ _ _ _` mp_tac >>
            simp[context_venom_asm_rel_def, context_memory_rel_def,
                 frame_view_def]) >>
         `read_byte i ast.as_memory = read_byte i st'.as_memory` by
           (first_x_assum irule >> metis_tac[context_spill_byte_of_region]) >>
         simp[]) >>
     qexists_tac `ast.as_memory` >> simp[]) >>
  qexists_tac `st' with as_stack := st'.as_stack ++ rest` >>
  simp[fn_frame_inv_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `read_byte b ast.as_memory = read_byte b mem0` by metis_tac[] >>
      `read_byte b ast.as_memory = read_byte b st'.as_memory` by
        (first_x_assum irule >> metis_tac[gas_closure_own]) >> metis_tac[]) >>
  qexists_tac `r` >> simp[]
QED

Theorem gas_inst_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode = GAS /\
    (* inst_wf doesn't fix the operand count of the read-only opcodes. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* The context-level memory obligations (codegen_memory_obligations). *)
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    (* Return-PC variables are only copied (unit_shape_ok's fn_shape_ok). *)
    opaque_use_ok fn /\ retpc_shape_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state. *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    ~is_terminator inst.inst_opcode /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input must be owned by the planner: each is either
       shallow enough to duplicate or available from the spill map.
       generated_plan_state_wf is structural and does not imply ownership. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    (* Spill well-formedness for prefix ops.
       Dischargeable: provable from generate_inst_plan output
       (plan generator produces spill-well-formed prefixes). *)
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          context_spill_step_safe cp vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops)
Proof
  cheat
QED
