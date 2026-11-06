(*
 * Helpers for fnFrameBoundary$gen_invoke_frame_sim: the INVOKE step
 * against frameRel$fn_frame_inv, given the callee's function simulation.
 *
 * Notes from the statement check (intuition only; read or ignore):
 * - Label arguments: unit_shape_ok gives fn_shape_ok fn, whose
 *   label_positions_ok forbids Label operands among INVOKE's arguments
 *   (unitShapeDefs), so compute_operands inst = arg_ops.
 * - Callee arity: fmp_lowered_context_wf gives invoke_layout_wf;
 *   invoke_input_arity_ok with canonical_param_prefix (callLayoutDefs)
 *   gives LENGTH args + 1 = LENGTH (get_params entry block) when the
 *   callee has a RETPC_PARAM.
 * - INVOKE arguments and outputs are never return-PC variables
 *   (opaque_use_ok / retpc_use_ok; retpc_shape_ok), so the frame view
 *   reads them as the plain state does.
 * - The caller's spill slots lie in its own region r (spill_alloc_layout_wf,
 *   allocMono's fixed spill base / growing next offset); ordered_spill_regions
 *   makes two MEM regions sharing a byte the same region, so a caller slot
 *   in the callee's closure means fcg_path nm fn.fn_name, a reachable cycle
 *   with the edge fn -> nm (fcgPostorder's reachable_fcg_acyclic lemmas).
 * - The asm semantics has no stack limit and JUMP only looks up o2pc.
 * - INVOKE can have several outputs, so the dead-output popmany postfix
 *   needs a general lemma (regularPostfixSim's structural lemma covers at
 *   most one output).
 * - fnBoundaryProps is downstream of fnFrameBoundary (via venomToAsmProps),
 *   so its small boundary lemmas can't be imported here.
 *)

Theory fnFrameBoundaryInvoke
Ancestors
  fnFrameBoundaryGenRet fnFrameBoundaryEntryParams genFrameSim frameRel contextCodegenRel codegenRel
  regularPostfixSim preparedPrefixSim asmFrame prefixSim stackOpSim blockSimHelpers
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs
  venomWf venomEffects stackPlanOps asmIR frameViewFacts finite_map
  callLayoutDefs fmpWfDefs list rich_list pred_set reorderSim planWf stackModel
  regularMemorySim fcgPostorder contextPlanLayoutProps fmpLowerProps generatedPrefixSim allocMono

Theorem invoke_source_ok:
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?callee args cvs ret rvs.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\
    setup_callee callee args vs = SOME cvs /\
    run_blocks fuel ctx callee cvs = IntRet ret rvs /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state vs rvs)) = SOME vs'
Proof
  simp[Once step_inst_def, decode_invoke_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem invoke_source_halt:
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?callee args cvs.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\
    setup_callee callee args vs = SOME cvs /\
    run_blocks fuel ctx callee cvs = Halt vs'
Proof
  simp[Once step_inst_def, decode_invoke_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem invoke_source_abort:
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?callee args cvs.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\
    setup_callee callee args vs = SOME cvs /\
    run_blocks fuel ctx callee cvs = Abort a vs'
Proof
  simp[Once step_inst_def, decode_invoke_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem invoke_plan_decompose:
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    SOME (ops, final) ==>
  ?iops prepared rops arranged consumed pushed ret_lbl called pops popped
   opts swapped.
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops, prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
    consumed = arranged with ps_stack :=
      stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack /\
    pushed = FOLDL (\s out.
      s with ps_stack := stack_push (Var out) s.ps_stack)
      consumed inst.inst_outputs /\
    fresh_label "return_label" pushed = (ret_lbl, called) /\
    (if inst.inst_outputs = [] then ([], called)
     else if ~halting \/ LENGTH inst.inst_outputs > 1 then
       popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) called
     else ([], called)) = (pops, popped) /\
    (if inst.inst_outputs = [] \/
        FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([], popped)
     else optimistic_swap_plan dfg inst nl term popped) = (opts, swapped) /\
    final = release_dead_spills nl swapped /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++
      pops ++ opts
Proof
  strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
      generate_regular_inst_plan_def, is_commutative_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  gvs[generate_emit_ops_def, venom_to_evm_name_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  Cases_on `inst.inst_outputs = []`
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[]
QED

Theorem invoke_closure_subset:
  !ctx cp caller callee b.
  fn_directly_calls ctx caller callee /\
  closure_spill_byte ctx cp callee b ==>
  closure_spill_byte ctx cp caller b
Proof
  rw[closure_spill_byte_def, fcg_path_def] >>
  qexists `r` >> simp[] >>
  metis_tac[relationTheory.RTC_RULES, relationTheory.RTC_TRANSITIVE,
            relationTheory.transitive_def]
QED

Theorem invoke_ordered_regions_overlap:
  !rs r s b.
    ordered_spill_regions rs /\ MEM r rs /\ MEM s rs /\
    r.sr_spill_base <= b /\ b < r.sr_spill_end /\
    s.sr_spill_base <= b /\ b < s.sr_spill_end ==> r = s
Proof
  Induct >> simp[ordered_spill_regions_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
    arithmeticTheory.NOT_LESS]
QED

Theorem invoke_caller_region_outside_callee:
  !ctx cp caller callee r b.
    ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
    r.sr_fn_name = caller /\ r.sr_spill_base <= b /\ b < r.sr_spill_end /\
    fn_directly_calls ctx caller callee /\
    ~TC (fn_directly_calls ctx) caller caller ==>
    ~closure_spill_byte ctx cp callee b
Proof
  rpt strip_tac >> gvs[closure_spill_byte_def] >>
  rename1 `fcg_path ctx callee other.sr_fn_name` >>
  `r = other` by metis_tac[invoke_ordered_regions_overlap] >>
  gvs[fcg_path_def] >>
  qpat_x_assum `~TC _ _ _` mp_tac >>
  simp[Once relationTheory.TC_CASES1] >>
  metis_tac[relationTheory.RTC_CASES_TC]
QED

Theorem invoke_return_preserves_caller_spills:
  !ctx cp caller callee r off vs cas ras.
    ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
    r.sr_fn_name = caller /\ r.sr_spill_base <= off /\
    off + 32 <= r.sr_spill_end /\
    fn_directly_calls ctx caller callee.fn_name /\
    ~TC (fn_directly_calls ctx) caller caller /\
    fn_return_state_rel ctx cp callee vs cas ras ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off ras.as_memory)) =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off cas.as_memory))
Proof
  rpt strip_tac >> irule spill_window_byte_frame >> rpt strip_tac >>
  rename1 `fn_return_state_rel ctx plan callee vs cas ras` >>
  `r.sr_spill_base <= i /\ i < r.sr_spill_end` by decide_tac >>
  `~closure_spill_byte ctx plan callee.fn_name i` by
    metis_tac[invoke_caller_region_outside_callee] >>
  gvs[fn_return_state_rel_def] >> first_x_assum irule >>
  simp[context_spill_byte_def] >> qexists `r` >> simp[] >> decide_tac
QED

Theorem invoke_lowered_targets_wf:
  fmp_lowered_context_wf ctx ==> wf_invoke_targets ctx
Proof
  rw[fmp_lowered_context_wf_def, wf_invoke_targets_def] >>
  first_x_assum drule_all >>
  simp[invoke_layout_wf_def] >> strip_tac >>
  metis_tac[lookup_function_mem, ctx_fn_names_def]
QED

Theorem invoke_context_no_cycle:
  !Inv ctx cp name.
    codegen_context_obligations Inv ctx cp /\
    MEM name (fcg_analyze ctx).fcg_reachable ==>
    ~TC (fn_directly_calls ctx) name name
Proof
  rpt gen_tac >> strip_tac >>
  irule reachable_fcg_acyclic_no_reachable_cycle >>
  gvs[codegen_context_obligations_def, reachable_call_graph_acyclic_def,
      fcg_is_reachable_def] >>
  `wf_invoke_targets ctx` by metis_tac[invoke_lowered_targets_wf] >>
  gvs[ctx_wf_def, ctx_has_entry_def] >> metis_tac[]
QED

Theorem invoke_direct_call:
  ctx_wf ctx /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops ==>
  fn_directly_calls ctx fn.fn_name nm
Proof
  strip_tac >>
  `lookup_function fn.fn_name ctx.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  simp[fn_directly_calls_def] >> metis_tac[]
QED

Theorem invoke_generated_return_spills:
  !Inv ctx cp fn inst nm arg_ops callee r off vs cas ras.
    codegen_context_obligations Inv ctx cp /\
    MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label nm :: arg_ops /\ callee.fn_name = nm /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end /\
    fn_return_state_rel ctx cp callee vs cas ras ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off ras.as_memory)) =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off cas.as_memory))
Proof
  rpt gen_tac >> strip_tac >>
  `~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name` by
    metis_tac[invoke_context_no_cycle] >>
  irule invoke_return_preserves_caller_spills >>
  gvs[codegen_context_obligations_def, context_plan_layout_wf_def] >>
  metis_tac[invoke_direct_call]
QED

Theorem invoke_label_free_one_input:
  ~is_label_operand op ==>
  emit_one_input INVOKE nl op ps = emit_one_input ADD nl op ps
Proof
  Cases_on `op` >> simp[is_label_operand_def, emit_one_input_def]
QED

Theorem invoke_label_free_input:
  !operands nl ps. EVERY (\op. ~is_label_operand op) operands ==>
  emit_input_plan INVOKE operands nl ps = emit_input_plan ADD operands nl ps
Proof
  Induct >> simp[emit_input_plan_def] >> rpt strip_tac >>
  simp[invoke_label_free_one_input] >> pairarg_tac >> simp[]
QED

Theorem invoke_compute_operands:
  unit_shape_ok unit /\ MEM fn unit.cu_context.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops ==>
  compute_operands inst = arg_ops /\ EVERY (\op. ~is_label_operand op) arg_ops
Proof
  strip_tac >>
  `label_positions_ok inst` by
    (gvs[unit_shape_ok_def, fn_shape_ok_def, inst_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  gvs[label_positions_ok_def] >>
  simp[compute_operands_def, get_non_label_operands_def, is_label_operand_def] >>
  gvs[listTheory.FILTER_EQ_ID, EVERY_MEM, is_label_operand_def] >>
  rpt strip_tac >> Cases_on `op` >> simp[] >>
  metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem invoke_arguments_not_retpc:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: args /\
  MEM (Var x) args ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >>
  `MEM (Var x) inst.inst_operands` by simp[] >>
  drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]
QED

Theorem invoke_operands_frame_values:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: args ==>
  eval_operands args (frame_view fn ra vs) = eval_operands args vs
Proof
  strip_tac >>
  `!x. MEM (Var x) args ==> ~retpc_var fn x` by
    metis_tac[invoke_arguments_not_retpc] >>
  `frame_view fn ra vs with vs_memory := vs.vs_memory = frame_view fn ra vs` by
    simp[frame_view_def, venom_state_component_equality] >>
  drule eval_operands_frame_view >>
  disch_then (qspecl_then [`vs`, `ra`, `vs.vs_memory`] mp_tac) >> simp[]
QED

Theorem invoke_input_prepared_sim:
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spill_base ps /\
  residual_budget_wf spill_base [] ps /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
  plan_slots_bounded spill_base ps' /\
  residual_budget_wf spill_base operands ps' /\
  pending_inventory_wf operands ps' /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  `emit_input_plan ADD operands nl ps = (ops,ps')` by
    metis_tac[invoke_label_free_input] >>
  irule emit_input_plan_prepared_sim >>
  conj_tac
  >- (gvs[EVERY_MEM] >> metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  simp[] >> qexistsl [`nl`, `ADD`, `ps`] >> simp[]
QED

Theorem invoke_prepared_structural:
  !base ps operands nl iops prepared dfg rops arranged outputs.
  residual_budget_wf base [] ps /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops, prepared) /\
  reorder_plan dfg operands prepared = (rops, arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs) ==>
  plan_state_residual_wf base operands (LENGTH operands) arranged /\
  ALL_DISTINCT (stack_pop (LENGTH operands) arranged.ps_stack) /\
  DISJOINT (set (stack_pop (LENGTH operands) arranged.ps_stack))
           (FDOM arranged.ps_spilled) /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) arranged.ps_stack /\
  (!op. op IN FDOM arranged.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `residual_budget_wf spillbase [] ps` >>
  `plan_state_residual_wf spillbase operands (LENGTH operands) arranged` by
    metis_tac[selected_input_arranged, sortingTheory.PERM_REFL] >>
  drule plan_state_residual_wf_pop >> strip_tac >> simp[] >>
  drule_all emit_input_plan_output_exclusion >> strip_tac >>
  `LENGTH operands <= 17` by decide_tac >>
  drule_all reorder_plan_output_exclusion >> simp[]
QED

Theorem invoke_selected_prefix_sim:
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val vs lo op = operand_val vs lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  plan_state_residual_wf spillbase operands (LENGTH operands) arranged /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops)))
          st = AsmOK st' /\
    venom_asm_rel lo arranged vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  strip_tac >>
  `emit_input_plan ADD operands nl ps = (iops,prepared)` by
    metis_tac[invoke_label_free_input] >>
  irule selected_prefix_prepared_sim >>
  simp[] >> qexistsl [`dfg`, `nl`, `ADD`, `operands`, `prepared`, `ps`] >>
  simp[] >>
  gvs[EVERY_MEM] >> metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem invoke_prefix_frame_transport:
  !ctx cp lo fn ra rest mem0 ps vs st arranged endpoint.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  venom_asm_rel lo arranged
    (frame_view fn ra vs with vs_memory := st.as_memory) endpoint /\
  (?r. MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end) ==>
  fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs
    (endpoint with as_stack := endpoint.as_stack ++ rest)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `memory_rel arranged.ps_alloc st.as_memory endpoint.as_memory` by
    fs[venom_asm_rel_def] >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    fs[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  `context_memory_rel cplan vs.vs_memory endpoint.as_memory` by
    (irule fnFrameTerminalPrepTheory.context_memory_rel_local_prefix >> metis_tac[]) >>
  `!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    read_byte b endpoint.as_memory = read_byte b st.as_memory` by
    (rpt strip_tac >>
     `~(arranged.ps_alloc.sa_spill_base <= b /\
        b < arranged.ps_alloc.sa_next_offset)` by
       (strip_tac >> qpat_x_assum `~closure_spill_byte _ _ _ _` mp_tac >>
        simp[closure_spill_byte_def] >> qexists `r` >> simp[] >>
        simp[fcg_path_def]) >>
     fs[memory_rel_def]) >>
  simp[fn_frame_inv_def] >>
  conj_tac >- fs[fn_frame_inv_def] >>
  conj_tac >- fs[fn_frame_inv_def] >>
  conj_tac
  >- (fs[context_venom_asm_rel_def, venom_asm_rel_def,
         plan_stack_rel_def, plan_spill_rel_def] >>
      fs[frame_view_def] >> metis_tac[]) >>
  conj_tac >- (fs[fn_frame_inv_def] >> metis_tac[]) >>
  qexists `r` >> simp[]
QED

Theorem invoke_frame_prefix:
  !ctx cp lo o2pc prog fn ra rest mem0 base ps vs st operands nl
    iops prepared dfg rops arranged r.
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf base ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp (iops ++ rops)) ==>
  plan_state_residual_wf base operands (LENGTH operands) arranged /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  ?mid. asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)))
          st = AsmOK mid /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generated_plan_state_wf spillbase ps` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  drule fnFrameTerminalPrepTheory.fn_frame_inv_local_state >> strip_tac >>
  `residual_budget_wf spillbase [] ps /\ plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (fs[generated_plan_state_wf_def] >>
     metis_tac[residual_budget_wf_canonical]) >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo at` by
    (simp[] >> metis_tac[]) >>
  `asm_block_at prog (st with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by simp[] >>
  drule_all invoke_selected_prefix_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "lift"
QED

Resume invoke_frame_prefix[lift]:
  rename1 `venom_asm_rel lo arranged _ endpoint` >>
  simp[] >>
  drule asm_steps_frame >> disch_then (qspec_then `rest` assume_tac) >>
  `st with as_stack := top ++ rest = st` by
    simp[asm_state_component_equality] >>
  qexists `endpoint with as_stack := endpoint.as_stack ++ rest` >>
  conj_tac >- gvs[] >>
  conj_tac >- (irule invoke_prefix_frame_transport >> metis_tac[]) >>
  simp[]
QED
Finalise invoke_frame_prefix

Theorem invoke_frame_arranged_stack:
  !ctx cp lo fn ra rest mem0 arranged vs mid operands values.
  fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  EVERY (\op. op <> dead_stack_marker) operands /\
  (!op. MEM op operands ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  eval_operands (REVERSE operands) (frame_view fn ra vs) = SOME values ==>
  ?saved. mid.as_stack = values ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH operands) arranged.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 arranged vs mid` >>
  `?top. mid.as_stack = top ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) arranged.ps_stack top` by
    fs[fn_frame_inv_def, context_venom_asm_rel_def] >>
  `LIST_REL (\op value. operand_val (frame_view fn ra vs) lo op = SOME value)
    (REVERSE operands) values` by
    (irule emitSimTheory.eval_operands_operand_val_rel >> simp[]) >>
  `top = values ++ DROP (LENGTH operands) top` by
    (qspecl_then [`lo`, `frame_view fn ra vs`,
       `stack_pop (LENGTH operands) arranged.ps_stack`, `REVERSE operands`]
       mp_tac emitSimTheory.asm_stack_inputs_from_plan >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  qexists `DROP (LENGTH operands) top` >>
  conj_tac >- metis_tac[APPEND_ASSOC] >>
  fs[plan_stack_rel_def, stack_pop_def] >>
  qpat_x_assum `arranged.ps_stack = _` (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
  simp[] >> decide_tac
QED

Theorem invoke_push_outputs_alloc[local]:
  !outs ps. (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
    ps outs).ps_alloc = ps.ps_alloc
Proof
  Induct >> simp[]
QED

Theorem invoke_arranged_alloc:
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
  reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) ==>
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule_all invoke_plan_decompose >> strip_tac >> gvs[] >>
  `called.ps_alloc = arranged.ps_alloc` by
    (gvs[fresh_label_def, invoke_push_outputs_alloc]) >>
  `called.ps_alloc.sa_spill_base = popped.ps_alloc.sa_spill_base /\
   called.ps_alloc.sa_next_offset <= popped.ps_alloc.sa_next_offset` by
    (Cases_on `inst.inst_outputs = []` >> gvs[] >>
     Cases_on `~halting \/ LENGTH inst.inst_outputs > 1` >> gvs[] >>
     metis_tac[allocMonoTheory.popmany_plan_spill_base,
       allocMonoTheory.popmany_plan_next_offset]) >>
  `popped.ps_alloc.sa_spill_base = swapped.ps_alloc.sa_spill_base /\
   popped.ps_alloc.sa_next_offset <= swapped.ps_alloc.sa_next_offset` by
    (Cases_on `inst.inst_outputs = [] \/ FILTER (\out. MEM out nl) inst.inst_outputs = []` >>
     gvs[] >> metis_tac[allocMonoTheory.optimistic_swap_plan_spill_base,
       allocMonoTheory.optimistic_swap_plan_next_offset]) >>
  gvs[allocMonoTheory.release_dead_spills_spill_base,
       allocMonoTheory.release_dead_spills_next_offset] >> decide_tac
QED

Theorem invoke_prefix_address_bounds:
  prefix_spill_wf initial_fmp lo
    (FRONT (iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) ps ==>
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)
Proof
  strip_tac >>
  `prefix_spill_wf initial_fmp lo
    (FRONT ((iops ++ rops ++ [SOPushLabel ret_lbl; SOPushLabel nm]) ++
      [SOEmit "JUMP"] ++ (SOLabel ret_lbl :: post))) ps` by
    (qpat_x_assum `prefix_spill_wf _ _ _ _` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  drule scratchPrefixSimTheory.prefix_spill_wf_front_emit_address_bounds >>
  simp[]
QED

Theorem invoke_generated_frame_prefix:
  !ctx cp lo o2pc prog liveness dfg cfg fn inst nl halting term label
    base ps vs st ops final ra rest mem0 nm arg_ops values r.
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  EVERY (\op. ~is_label_operand op) (compute_operands inst) /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan INVOKE (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  eval_operands (REVERSE (compute_operands inst)) (frame_view fn ra vs) = SOME values ==>
  ?iops prepared rops arranged ret_lbl post mid saved.
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)))
      st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf base (compute_operands inst) (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++ compute_operands inst /\
    mid.as_stack = values ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `generated_plan_state_wf spillbase ps` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  drule_all invoke_plan_decompose >> strip_tac >>
  suspend "bounds"
QED

Resume invoke_generated_frame_prefix[bounds]:
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (drule stack_get_depth_props >> simp[stack_peek_def] >>
         strip_tac >> disj1_tac >>
         qpat_x_assum `EL _ _ = op` (SUBST1_TAC o SYM) >>
         irule EL_MEM >> decide_tac) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[FLOOKUP_DEF]) >>
  `r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (drule_all invoke_arranged_alloc >> strip_tac >> gvs[] >> decide_tac) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (irule invoke_prefix_address_bounds >> metis_tac[APPEND_ASSOC]) >>
  `asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[execute_plan_append, asm_block_at_append] >>
  qpat_x_assum `consumed = _` kall_tac >>
  qpat_x_assum `pushed = _` kall_tac >>
  qpat_x_assum `fresh_label _ _ = _` kall_tac >>
  ntac 2 (qpat_x_assum `(if _ then _ else _) = _` kall_tac) >>
  qpat_x_assum `final = _` kall_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `prefix_spill_wf _ _ _ _` kall_tac >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by gvs[] >>
  drule_all invoke_frame_prefix >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "finish"
QED

Resume invoke_generated_frame_prefix[finish]:
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all invoke_frame_arranged_stack >> strip_tac >>
  `asm_block_at prog mid.as_pc (execute_plan cplan.cp_initial_fmp
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ (pops ++ opts)))` by
    (qpat_x_assum `asm_block_at prog st.as_pc (execute_plan _ ops)` mp_tac >>
     qpat_x_assum `ops = _` mp_tac >>
     qpat_x_assum `mid.as_pc = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[execute_plan_append, asm_block_at_append] >> rpt strip_tac >>
     gvs[] >> metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  qexistsl [`iops`, `prepared`, `rops`, `arranged`, `ret_lbl`, `pops ++ opts`, `mid`, `saved`] >>
  simp[APPEND_ASSOC]
QED
Finalise invoke_generated_frame_prefix

Theorem invoke_call_packet:
  asm_block_at prog st.as_pc [AsmPushLabel ret_lbl; AsmPushLabel nm; AsmOp "JUMP"] /\
  FLOOKUP lo ret_lbl = SOME ret_off /\ FLOOKUP lo nm = SOME off /\
  off < dimword(:256) /\ FLOOKUP o2pc off = SOME pc ==>
  asm_steps lo o2pc prog 3 st =
    AsmOK (st with <|as_stack := n2w ret_off :: st.as_stack; as_pc := pc|>)
Proof
  strip_tac >>
  `st.as_pc < LENGTH prog /\ st.as_pc + 1 < LENGTH prog /\ st.as_pc + 2 < LENGTH prog /\
   EL st.as_pc prog = AsmPushLabel ret_lbl /\
   EL (st.as_pc + 1) prog = AsmPushLabel nm /\
   EL (st.as_pc + 2) prog = AsmOp "JUMP"` by
    (gvs[asm_block_at_def] >>
     first_x_assum (fn th => map_every (fn q => mp_tac (Q.SPEC q th)) [`0`, `1`, `2`]) >>
     simp[] >> decide_tac) >>
  rewrite_tac[DECIDE ``3 = SUC (SUC (SUC 0))``] >>
  simp[Once asm_steps_def, asm_step_def, asm_next_def] >>
  rewrite_tac[DECIDE ``2 = SUC (SUC 0)``] >>
  simp[Once asm_steps_def, asm_step_def, asm_next_def] >>
  rewrite_tac[DECIDE ``1 = SUC 0``] >>
  simp[Once asm_steps_def, asm_step_def, asm_step_op_def, asm_step_control_def,
       asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
       asm_step_memory_def, asm_jump_def, wordsTheory.w2n_n2w, asm_steps_def]
QED

Theorem invoke_callee_entry_facts:
  !Inv ctx cp fn inst vs nm arg_ops callee args cvs.
  codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs ==>
  callee.fn_name = nm /\ MEM callee ctx.ctx_functions /\
  fn_entry_inv Inv ctx callee cvs /\
  MEM callee.fn_name (fcg_analyze ctx).fcg_reachable
Proof
  rpt gen_tac >> strip_tac >>
  `callee.fn_name = nm /\ MEM callee ctx.ctx_functions` by
    (`!fns nm callee. lookup_function nm fns = SOME callee ==>
        callee.fn_name = nm /\ MEM callee fns` by
       (Induct >> simp[lookup_function_def, FIND_thm] >>
        rpt gen_tac >> IF_CASES_TAC >> gvs[lookup_function_def] >>
        metis_tac[]) >> metis_tac[]) >> simp[] >>
  conj_tac
  >- (gvs[reachability_closed_def] >>
      first_x_assum irule >>
      qexistsl [`args`, `fn`, `inst`, `callee.fn_name`, `arg_ops`, `vs`] >>
      simp[decode_invoke_def]) >>
  `fn_directly_calls ctx fn.fn_name nm` by
    (irule invoke_direct_call >>
     gvs[codegen_context_obligations_def] >> metis_tac[]) >>
  `wf_invoke_targets ctx` by
    (irule invoke_lowered_targets_wf >> gvs[codegen_context_obligations_def]) >>
  `ctx_wf ctx` by gvs[codegen_context_obligations_def] >>
  `?entry. ctx.ctx_entry = SOME entry` by
    gvs[ctx_wf_def, ctx_has_entry_def] >>
  fs[GSYM fcg_is_reachable_def] >>
  irule fcg_reachable_direct_callee >> simp[] >> metis_tac[]
QED

Theorem invoke_setup_entry_rel:
  !ctx cp lo fn ra rest mem0 arranged vs mid callee args cvs ret_off saved pc.
  setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
  LENGTH args + 1 = LENGTH (get_params (HD callee.fn_blocks).bb_instructions) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
  mid.as_stack = REVERSE args ++ saved ++ rest ==>
  fn_entry_state_rel cp callee cvs
    (mid with <|as_stack := n2w ret_off :: mid.as_stack; as_pc := pc|>)
    (n2w ret_off) (saved ++ rest)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[setup_callee_def, fn_entry_state_rel_def, fn_frame_inv_def,
      context_venom_asm_rel_def, shared_state_rel_def, venom_asm_terminal_rel_def,
      frame_view_def]
QED

Theorem invoke_canonical_param_count:
  !fn. canonical_param_prefix fn ==>
  LENGTH (get_params (HD fn.fn_blocks).bb_instructions) =
    LENGTH (fn_user_param_insts fn) +
    (if IS_SOME (fn_hidden_fmp_param fn) then 1 else 0) +
    (if fn_has_retpc fn then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule (iffLR canonical_param_prefix_iff) >> strip_tac >>
  `fn_user_param_insts fn = users /\
   OPTION_TO_LIST (fn_hidden_fmp_param fn) = fmp` by
    metis_tac[canonical_param_prefix_queries] >>
  rename1 `no_param_insts tail_insts` >>
  `get_params tail_insts = []` by
    (Cases_on `tail_insts` >> gvs[get_params_def, no_param_insts_def]) >>
  gvs[fn_has_retpc_def, get_params_param_prefix, EVERY_MEM,
      is_param_opcode_def, get_params_def, no_param_insts_def,
      EXISTS_APPEND, EXISTS_MEM] >>
  Cases_on `fn_hidden_fmp_param fn` >> gvs[OPTION_TO_LIST_def] >>
  IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem invoke_callee_param_arity:
  !ctx inst nm arg_ops callee args vs.
  invoke_layout_wf ctx inst /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\ fn_has_retpc callee ==>
  LENGTH args + 1 = LENGTH (get_params (HD callee.fn_blocks).bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[invoke_layout_wf_def, fmp_seal_layout_matches_fn_def,
      fmp_signature_syntax_wf_def, invoke_input_arity_ok_def] >>
  drule invoke_canonical_param_count >> simp[] >>
  `!ops vs vals. eval_operands ops vs = SOME vals ==>
      LENGTH vals = LENGTH ops` by
    (Induct >> simp[eval_operands_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `LENGTH args = LENGTH arg_ops` by metis_tac[] >> simp[]
QED

Theorem invoke_call_entry:
  !ctx cp lo o2pc prog fn ra rest mem0 arranged vs mid callee args cvs
   ret_lbl ret_off saved off pc.
  setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
  LENGTH args + 1 = LENGTH (get_params (HD callee.fn_blocks).bb_instructions) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\
  asm_block_at prog mid.as_pc [AsmPushLabel ret_lbl; AsmPushLabel callee.fn_name; AsmOp "JUMP"] /\
  FLOOKUP lo ret_lbl = SOME ret_off /\ FLOOKUP lo callee.fn_name = SOME off /\
  off < dimword(:256) /\ FLOOKUP o2pc off = SOME pc ==>
  ?cas. asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    cas.as_pc = pc
Proof
  rpt gen_tac >> strip_tac >>
  drule_all invoke_call_packet >> strip_tac >>
  drule_all invoke_setup_entry_rel >>
  disch_then (qspecl_then [`ret_off`, `pc`] assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem invoke_indexed_callee_target:
  !ctx cp lo o2pc prog callee nm.
  MEM callee ctx.ctx_functions /\ callee.fn_name = nm /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
    ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword(:256) /\
      FLOOKUP o2pc off = SOME pc /\
      asm_block_at prog pc
        (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) ==>
  ?j off pc. j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    FLOOKUP lo nm = SOME off /\ off < dimword(:256) /\
    FLOOKUP o2pc off = SOME pc /\
    asm_block_at prog pc
      (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)
Proof
  rpt gen_tac >> strip_tac >>
  fs[MEM_EL] >> first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem invoke_return_label_target:
  !lo o2pc fmp ops pre ret_lbl post pc.
  ops = pre ++ [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP";
                SOLabel ret_lbl] ++ post /\
  (!lbl i. i < LENGTH (execute_plan fmp ops) /\
    EL i (execute_plan fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword(:256) /\
      FLOOKUP o2pc off = SOME (pc + i)) ==>
  ?off. FLOOKUP lo ret_lbl = SOME off /\ off < dimword(:256) /\
    FLOOKUP o2pc off = SOME (pc + LENGTH (execute_plan fmp pre) + 3)
Proof
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`ret_lbl`, `LENGTH (execute_plan fmp pre) + 3`] mp_tac) >>
  gvs[execute_plan_append] >>
  qmatch_goalsub_abbrev_tac `LENGTH prefix` >>
  qmatch_goalsub_abbrev_tac `LENGTH suffix` >>
  simp[execute_plan_def, exec_stack_op_def, EL_APPEND_EQN]
QED

Theorem invoke_bind_frame_outside:
  !outs vals s t fn ra x.
  bind_outputs outs vals s = SOME t /\ ~MEM x outs ==>
  lookup_var x (frame_view fn ra t) = lookup_var x (frame_view fn ra s)
Proof
  Induct >- (Cases >> simp[bind_outputs_def]) >>
  Cases_on `vals` >- simp[bind_outputs_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `bind_outputs (out::outs) (value::values) source = SOME result` >>
  `bind_outputs outs values (update_var out value source) = SOME result` by
    gvs[bind_outputs_def, ZIP, FOLDL] >>
  first_x_assum (drule_at Any) >>
  disch_then (qspecl_then [`fn`, `ra`, `x`] mp_tac) >>
  gvs[lookup_var_def, frame_view_vars_lookup, update_var_def, FLOOKUP_UPDATE]
QED

Theorem invoke_bind_frame_position:
  !outs vals s t fn ra k.
  ALL_DISTINCT outs /\ EVERY (\x. ~retpc_var fn x) outs /\
  bind_outputs outs vals s = SOME t /\ k < LENGTH outs ==>
  lookup_var (EL k outs) (frame_view fn ra t) = SOME (EL k vals)
Proof
  Induct >- simp[] >>
  Cases_on `vals` >- simp[bind_outputs_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `bind_outputs (out::outs) (value::values) source = SOME result` >>
  `bind_outputs outs values (update_var out value source) = SOME result` by
    gvs[bind_outputs_def, ZIP, FOLDL] >>
  Cases_on `k`
  >- (fs[] >> drule_all invoke_bind_frame_outside >>
      disch_then (qspecl_then [`fn`, `ra`] mp_tac) >>
      gvs[lookup_var_def, frame_view_vars_lookup, update_var_def, FLOOKUP_UPDATE]) >>
  gvs[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem invoke_bind_frame_values:
  !fn ra outs vals s t.
  ALL_DISTINCT outs /\ EVERY (\x. ~retpc_var fn x) outs /\
  bind_outputs outs vals s = SOME t ==>
  (!k. k < LENGTH outs ==>
    lookup_var (EL k outs) (frame_view fn ra t) = SOME (EL k vals)) /\
  (!x. ~MEM x outs ==>
    lookup_var x (frame_view fn ra t) = lookup_var x (frame_view fn ra s))
Proof
  metis_tac[invoke_bind_frame_position, invoke_bind_frame_outside]
QED

Theorem invoke_return_outside_closure:
  !ctx cp lo fn ra rest mem0 arranged vs mid callee cvs cas ras.
  fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
  fn_directly_calls ctx fn.fn_name callee.fn_name /\
  cas.as_memory = mid.as_memory /\
  fn_return_state_rel ctx cp callee cvs cas ras ==>
  !b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
    read_byte b ras.as_memory = read_byte b mem0
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `fn_return_state_rel ctx plan callee cvs cas ras` >>
  `~closure_spill_byte ctx plan callee.fn_name b` by
    metis_tac[invoke_closure_subset] >>
  gvs[fn_frame_inv_def, fn_return_state_rel_def] >> metis_tac[]
QED

Theorem invoke_bind_shared_state:
  !outs vals s t st.
  bind_outputs outs vals s = SOME t /\ shared_state_rel s st ==>
  shared_state_rel t st
Proof
  Induct >- (Cases >> simp[bind_outputs_def]) >>
  Cases_on `vals` >- simp[bind_outputs_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `bind_outputs (out::outs) (value::values) source = SOME result` >>
  `bind_outputs outs values (update_var out value source) = SOME result` by
    gvs[bind_outputs_def, ZIP, FOLDL] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  gvs[shared_state_rel_def, venom_asm_terminal_rel_def, update_var_def]
QED

Theorem invoke_merge_return_shared:
  !ctx cp callee cvs cas ras caller ret.
  fn_return_state_rel ctx cp callee cvs cas ras /\
  cas.as_call_ctx = caller.vs_call_ctx /\ cas.as_tx_ctx = caller.vs_tx_ctx /\
  cas.as_block_ctx = caller.vs_block_ctx /\ cas.as_code = caller.vs_code /\
  cas.as_prev_hashes = caller.vs_prev_hashes ==>
  shared_state_rel (adopt_return_fmp ret (merge_callee_state caller cvs)) ras
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ret.iret_adopt_fmp` >>
  gvs[fn_return_state_rel_def, shared_state_rel_def, venom_asm_terminal_rel_def,
      adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem invoke_bind_frame_fields:
  !outs vals s t.
  bind_outputs outs vals s = SOME t ==>
  t = s with vs_vars := t.vs_vars
Proof
  Induct >- (Cases >> simp[bind_outputs_def]) >>
  Cases_on `vals` >- simp[bind_outputs_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `bind_outputs (out::outs) (value::values) source = SOME result` >>
  `bind_outputs outs values (update_var out value source) = SOME result` by
    gvs[bind_outputs_def, ZIP, FOLDL] >>
  first_x_assum drule >> simp[update_var_def]
QED

Theorem invoke_return_old_operand:
  !outs vals caller cvs ret result fn ra lo op.
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state caller cvs)) = SOME result /\
  EVERY (\out. case op of Var x => x <> out | _ => T) outs ==>
  operand_val (frame_view fn ra result) lo op =
  operand_val (frame_view fn ra caller) lo op
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  gvs[operand_val_def] >>
  rename1 `FLOOKUP (frame_view fn ra result).vs_vars x` >>
  `~MEM x outs` by gvs[EVERY_MEM] >>
  drule_all invoke_bind_frame_outside >>
  disch_then (qspecl_then [`fn`, `ra`] mp_tac) >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[lookup_var_def, frame_view_vars_lookup, adopt_return_fmp_def,
       merge_callee_state_def]
QED

Theorem invoke_return_saved_stack:
  !outs vals caller cvs ret result fn ra lo stack saved.
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state caller cvs)) = SOME result /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs) stack /\
  plan_stack_rel lo (frame_view fn ra caller) stack saved ==>
  plan_stack_rel lo (frame_view fn ra result) stack saved
Proof
  rpt gen_tac >> strip_tac >>
  gvs[plan_stack_rel_def] >> rpt strip_tac >>
  `MEM (EL i (REVERSE stack)) stack` by
    metis_tac[EL_MEM, LENGTH_REVERSE, MEM_REVERSE] >>
  `EVERY (\out. case EL i (REVERSE stack) of Var x => x <> out | _ => T) outs` by
    (qpat_x_assum `EVERY _ stack` mp_tac >>
     rewrite_tac[EVERY_MEM] >> disch_then drule >> simp[]) >>
  drule_all invoke_return_old_operand >>
  disch_then (qspecl_then [`fn`, `ra`, `lo`] assume_tac) >>
  metis_tac[]
QED

Theorem invoke_return_output_stack:
  !outs vals s result fn ra lo stack saved.
  ALL_DISTINCT outs /\ EVERY (\x. ~retpc_var fn x) outs /\
  bind_outputs outs vals s = SOME result /\
  plan_stack_rel lo (frame_view fn ra result) stack saved ==>
  plan_stack_rel lo (frame_view fn ra result) (stack ++ MAP Var outs)
    (REVERSE vals ++ saved)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH vals = LENGTH outs` by gvs[bind_outputs_def] >>
  `!k. k < LENGTH outs ==>
    lookup_var (EL k outs) (frame_view fn ra result) = SOME (EL k vals)` by
    (rpt strip_tac >> irule invoke_bind_frame_position >>
     simp[] >> metis_tac[]) >>
  gvs[plan_stack_rel_def, REVERSE_APPEND] >> rpt strip_tac >>
  Cases_on `i < LENGTH outs`
  >- (simp[EL_APPEND_EQN, EL_MAP, EL_REVERSE, operand_val_def] >>
      first_x_assum (qspec_then `PRE (LENGTH outs - i)` mp_tac) >>
      simp[lookup_var_def]) >>
  simp[EL_APPEND_EQN] >> first_x_assum irule >> decide_tac
QED

Theorem invoke_return_spills:
  !ctx cp fn callee r lo ra spilled outs vals caller cvs ret result cas ras.
  ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
  r.sr_fn_name = fn.fn_name /\ fn_directly_calls ctx fn.fn_name callee.fn_name /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  fn_return_state_rel ctx cp callee cvs cas ras /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state caller cvs)) = SOME result /\
  plan_spill_rel lo (frame_view fn ra caller) spilled cas.as_memory /\
  (!op off. FLOOKUP spilled op = SOME off ==>
    r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end /\
    EVERY (\out. case op of Var x => x <> out | _ => T) outs) ==>
  plan_spill_rel lo (frame_view fn ra result) spilled ras.as_memory
Proof
  rpt gen_tac >> strip_tac >> simp[plan_spill_rel_def] >> rpt strip_tac >>
  `r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end /\
    EVERY (\out. case op of Var x => x <> out | _ => T) outs` by metis_tac[] >>
  drule_all invoke_return_old_operand >>
  disch_then (qspecl_then [`fn`, `ra`, `lo`] assume_tac) >>
  drule_all invoke_return_preserves_caller_spills >> strip_tac >>
  gvs[plan_spill_rel_def] >> metis_tac[]
QED

Theorem invoke_return_context:
  !ctx cp fn callee r lo ra consumed outs vals caller cvs ret result cas ras.
  ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
  r.sr_fn_name = fn.fn_name /\ fn_directly_calls ctx fn.fn_name callee.fn_name /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  fn_return_state_rel ctx cp callee cvs cas ras /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state caller cvs)) = SOME result /\
  ALL_DISTINCT outs /\ EVERY (\x. ~retpc_var fn x) outs /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs)
    consumed.ps_stack /\
  (!op off. FLOOKUP consumed.ps_spilled op = SOME off ==>
    r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end /\
    EVERY (\out. case op of Var x => x <> out | _ => T) outs) /\
  context_venom_asm_rel cp lo consumed (frame_view fn ra caller) cas /\
  ras.as_stack = REVERSE vals ++ cas.as_stack ==>
  context_venom_asm_rel cp lo
    (consumed with ps_stack := consumed.ps_stack ++ MAP Var outs)
    (frame_view fn ra result) ras
Proof
  rpt gen_tac >> strip_tac >>
  `plan_stack_rel lo (frame_view fn ra caller) consumed.ps_stack cas.as_stack /\
   plan_spill_rel lo (frame_view fn ra caller) consumed.ps_spilled cas.as_memory` by
    gvs[context_venom_asm_rel_def] >>
  `plan_stack_rel lo (frame_view fn ra result) consumed.ps_stack cas.as_stack` by
    (irule invoke_return_saved_stack >> simp[] >> metis_tac[]) >>
  `plan_stack_rel lo (frame_view fn ra result)
    (consumed.ps_stack ++ MAP Var outs) ras.as_stack` by
    (gvs[] >> irule invoke_return_output_stack >> simp[] >> metis_tac[]) >>
  `plan_spill_rel lo (frame_view fn ra result) consumed.ps_spilled ras.as_memory` by
    (irule invoke_return_spills >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `shared_state_rel (adopt_return_fmp ret (merge_callee_state caller cvs)) ras` by
    (irule invoke_merge_return_shared >> goal_assum (drule_at Any) >>
     gvs[context_venom_asm_rel_def, frame_view_def]) >>
  `shared_state_rel result ras` by metis_tac[invoke_bind_shared_state] >>
  `result.vs_memory = cvs.vs_memory` by
    (drule invoke_bind_frame_fields >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >>
     Cases_on `ret.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  qpat_x_assum `fn_return_state_rel _ _ _ _ _ _` mp_tac >>
  rewrite_tac[fn_return_state_rel_def] >> strip_tac >>
  simp[context_venom_asm_rel_def, frame_view_def] >>
  gvs[shared_state_rel_def, venom_asm_terminal_rel_def, frame_view_def]
QED

Theorem invoke_return_frame_fields:
  !outs vals caller cvs ret result.
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state caller cvs)) = SOME result ==>
  result.vs_initial_fmp = caller.vs_initial_fmp /\
  result.vs_halted = caller.vs_halted
Proof
  rpt gen_tac >> strip_tac >> drule invoke_bind_frame_fields >>
  disch_then (mp_tac o Q.AP_TERM `\s. (s.vs_initial_fmp, s.vs_halted)`) >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem invoke_called_plan_fields:
  !outs consumed ret_lbl called.
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      consumed outs) = (ret_lbl, called) ==>
  called.ps_stack = consumed.ps_stack ++ MAP Var outs /\
  called.ps_spilled = consumed.ps_spilled /\
  called.ps_alloc = consumed.ps_alloc
Proof
  `!outs stk. FOLDL (\stk out. stack_push (Var out) stk) stk outs =
    stk ++ MAP Var outs` by
    (Induct >> simp[stack_push_def, APPEND_ASSOC]) >>
  simp[fresh_label_def, emit_output_fold_stack] >> rpt strip_tac >> gvs[]
QED

Theorem invoke_consumed_context:
  !ctx cp lo fn ra rest mem0 arranged vs mid operands values saved.
  fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  mid.as_stack = values ++ saved ++ rest /\
  LENGTH values = LENGTH operands ==>
  context_venom_asm_rel cp lo
    (arranged with ps_stack := stack_pop (LENGTH operands) arranged.ps_stack)
    (frame_view fn ra vs) (mid with as_stack := saved)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 arranged vs mid` >>
  `?top. mid.as_stack = top ++ rest /\
    context_venom_asm_rel cplan lo arranged (frame_view fn ra vs)
      (mid with as_stack := top)` by fs[fn_frame_inv_def] >>
  `top = values ++ saved` by metis_tac[APPEND_ASSOC, APPEND_11] >>
  `plan_stack_rel lo (frame_view fn ra vs) arranged.ps_stack top` by
    gvs[context_venom_asm_rel_def] >>
  `LENGTH operands <= LENGTH arranged.ps_stack` by
    (qpat_x_assum `arranged.ps_stack = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     pure_rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  `plan_stack_rel lo (frame_view fn ra vs)
    (stack_pop (LENGTH operands) arranged.ps_stack) (DROP (LENGTH operands) top)` by
    (pure_rewrite_tac[stack_pop_def] >> irule plan_stack_rel_pop >> simp[]) >>
  `DROP (LENGTH operands) values = []` by metis_tac[DROP_LENGTH_NIL] >>
  gvs[context_venom_asm_rel_def, DROP_APPEND]
QED

Theorem invoke_context_release_dead_spills:
  !cplan lo ps vs st nl.
  context_venom_asm_rel cplan lo ps vs st ==>
  context_venom_asm_rel cplan lo (release_dead_spills nl ps) vs st
Proof
  rpt gen_tac >> strip_tac >>
  drule entry_context_to_local_memory >> strip_tac >>
  drule venom_asm_rel_release_dead_spills >>
  disch_then (qspec_then `nl` assume_tac) >>
  `!op. operand_val (vs with vs_memory := st.as_memory) lo op =
    operand_val vs lo op` by (Cases >> simp[operand_val_def]) >>
  gvs[context_venom_asm_rel_def, venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def]
QED

Theorem invoke_called_structural:
  !consumed outs ret_lbl called.
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      consumed outs) = (ret_lbl, called) /\
  spill_alloc_layout_wf consumed.ps_alloc consumed.ps_spilled /\
  ALL_DISTINCT consumed.ps_stack /\ ALL_DISTINCT outs /\
  DISJOINT (set consumed.ps_stack) (FDOM consumed.ps_spilled) /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs)
    consumed.ps_stack /\
  (!op. op IN FDOM consumed.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outs) ==>
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  ALL_DISTINCT called.ps_stack /\
  DISJOINT (set called.ps_stack) (FDOM called.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >> drule invoke_called_plan_fields >> strip_tac >>
  `ALL_DISTINCT (MAP Var outs)` by (irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  `!x. MEM x outs ==> ~MEM (Var x) consumed.ps_stack` by
    (rpt strip_tac >>
     qpat_x_assum `EVERY _ consumed.ps_stack` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `Var x` mp_tac) >> simp[] >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  `!x. MEM x outs ==> Var x NOTIN FDOM consumed.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. op IN FDOM _ ==> _`
       (qspec_then `Var x` mp_tac) >>
     pure_rewrite_tac[EVERY_MEM] >> simp[] >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  simp[ALL_DISTINCT_APPEND, MEM_MAP, DISJOINT_UNION, LIST_TO_SET_APPEND] >>
  conj_tac >- metis_tac[] >>
  gvs[DISJOINT_DEF, EXTENSION, MEM_MAP] >> metis_tac[]
QED

Theorem invoke_cleanup_popmany:
  !outs nl halting called pops popped cplan lo o2pc prog vs st r ctx name.
  (if outs = [] then ([], called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([], called)) = (pops,popped) /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  ALL_DISTINCT called.ps_stack /\
  DISJOINT (set called.ps_stack) (FDOM called.ps_spilled) /\
  (!off. MEM (SOSpill off) pops ==> off < dimword (:256)) /\
  context_venom_asm_rel cplan lo called vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp pops) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= popped.ps_alloc.sa_spill_base /\
  popped.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?mid. asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pops)) st = AsmOK mid /\
    context_venom_asm_rel cplan lo popped vs mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp pops) /\
    (!b. ~closure_spill_byte ctx cplan name b ==>
      read_byte b mid.as_memory = read_byte b st.as_memory) /\
    spill_alloc_layout_wf popped.ps_alloc popped.ps_spilled /\
    ALL_DISTINCT popped.ps_stack /\
    DISJOINT (set popped.ps_stack) (FDOM popped.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `outs = []`
  >- (gvs[] >> qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `~halting \/ LENGTH outs > 1`
  >- (fs[] >> drule_all entry_context_popmany_outside_closure >>
      disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
      qexists `st'` >> simp[]) >>
  gvs[] >> qexists `st` >> simp[execute_plan_def, asm_steps_def]
QED

Theorem invoke_cleanup_swap:
  !outs nl dfg inst term popped opts swapped cplan lo o2pc prog vs st r ctx name.
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  spill_alloc_layout_wf popped.ps_alloc popped.ps_spilled /\
  ALL_DISTINCT popped.ps_stack /\
  DISJOINT (set popped.ps_stack) (FDOM popped.ps_spilled) /\
  (!off. MEM (SOSpill off) opts ==> off < dimword (:256)) /\
  context_venom_asm_rel cplan lo popped vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp opts) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= swapped.ps_alloc.sa_spill_base /\
  swapped.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?fin. asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp opts)) st = AsmOK fin /\
    context_venom_asm_rel cplan lo swapped vs fin /\
    fin.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp opts) /\
    (!b. ~closure_spill_byte ctx cplan name b ==>
      read_byte b fin.as_memory = read_byte b st.as_memory)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `outs = [] \/ FILTER (\out. MEM out nl) outs = []`
  >- (gvs[] >> qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  fs[] >> drule_all entry_context_optimistic_swap_outside_closure >>
  disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
  qexists `st'` >> simp[]
QED

Theorem invoke_cleanup_alloc:
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped ==>
  called.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  popped.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  swapped.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  called.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
  popped.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
  swapped.ps_alloc.sa_next_offset = final.ps_alloc.sa_next_offset
Proof
  strip_tac >>
  `called.ps_alloc.sa_spill_base = popped.ps_alloc.sa_spill_base /\
   called.ps_alloc.sa_next_offset <= popped.ps_alloc.sa_next_offset` by
    (Cases_on `outs = []` >> gvs[] >>
     Cases_on `~halting \/ LENGTH outs > 1` >> gvs[] >>
     metis_tac[popmany_plan_spill_base, popmany_plan_next_offset]) >>
  `popped.ps_alloc.sa_spill_base = swapped.ps_alloc.sa_spill_base /\
   popped.ps_alloc.sa_next_offset <= swapped.ps_alloc.sa_next_offset` by
    (Cases_on `outs = [] \/ FILTER (\out. MEM out nl) outs = []` >> gvs[] >>
     metis_tac[optimistic_swap_plan_spill_base, optimistic_swap_plan_next_offset]) >>
  gvs[release_dead_spills_spill_base, release_dead_spills_next_offset]
QED

Theorem invoke_cleanup_context:
  !outs nl halting called pops popped dfg inst term opts swapped final
    cplan lo o2pc prog vs st r ctx name.
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  ALL_DISTINCT called.ps_stack /\
  DISJOINT (set called.ps_stack) (FDOM called.ps_spilled) /\
  (!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)) /\
  context_venom_asm_rel cplan lo called vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp (pops ++ opts)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) st = AsmOK st' /\
    context_venom_asm_rel cplan lo final vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts)) /\
    (!b. ~closure_spill_byte ctx cplan name b ==>
      read_byte b st'.as_memory = read_byte b st.as_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all invoke_cleanup_alloc >> strip_tac >>
  `r.sr_spill_base <= popped.ps_alloc.sa_spill_base /\
   popped.ps_alloc.sa_next_offset <= r.sr_spill_end /\
   r.sr_spill_base <= swapped.ps_alloc.sa_spill_base /\
   swapped.ps_alloc.sa_next_offset <= r.sr_spill_end` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `(!off. MEM (SOSpill off) pops ==> off < dimword (:256)) /\
   (!off. MEM (SOSpill off) opts ==> off < dimword (:256))` by gvs[] >>
  `asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp pops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp pops))
     (execute_plan cplan.cp_initial_fmp opts)` by
    gvs[execute_plan_append, asm_block_at_append] >>
  drule_all invoke_cleanup_popmany >>
  disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
  `asm_block_at prog mid.as_pc (execute_plan cplan.cp_initial_fmp opts)` by
    (qpat_x_assum `mid.as_pc = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all invoke_cleanup_swap >>
  disch_then (qspecl_then [`o2pc`, `ctx`] strip_assume_tac) >>
  qexists `fin` >>
  conj_tac >- (pure_rewrite_tac[execute_plan_append, LENGTH_APPEND] >>
              irule asm_steps_compose_ok >> qexists `mid` >> simp[]) >>
  conj_tac >- metis_tac[invoke_context_release_dead_spills] >>
  simp[execute_plan_append] >> metis_tac[]
QED

(* ===== Composition ===== *)

Theorem eval_operands_some_length:
  !xs s ys. eval_operands xs s = SOME ys ==> LENGTH ys = LENGTH xs
Proof
  Induct >> simp[eval_operands_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem invoke_packet_block:
  !prog pc fmp a b post.
  asm_block_at prog pc
    (execute_plan fmp ([SOPushLabel a; SOPushLabel b; SOEmit "JUMP"; SOLabel a] ++ post)) ==>
  asm_block_at prog pc [AsmPushLabel a; AsmPushLabel b; AsmOp "JUMP"]
Proof
  rw[asm_block_at_def, execute_plan_def, exec_stack_op_def] >>
  first_x_assum (qspec_then `j` mp_tac) >>
  `j = 0 \/ j = 1 \/ j = 2` by decide_tac >> gvs[]
QED

(* The prefix and the call packet: from the caller's frame to the callee's
   entry, with everything the callee hypothesis needs. *)
Theorem invoke_enter_callee:
  !Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops callee args cvs.
  ctx = unit.cu_context /\
  unit_shape_ok unit /\
  codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\
  MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\
     inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc
                (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  MEM inst (fn_insts fn) /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode
      (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
           EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
           ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                 FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
  (!op. MEM op (compute_operands inst) ==>
        eval_operand op (frame_view fn ra vs) =
        operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
           (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
            MEM at (compute_operands inst)) /\
           operand_equiv dfg op at ==>
           operand_val (frame_view fn ra vs) lo op =
           operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
    (compute_operands inst) /\
  prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    SOME (ops, final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\
  setup_callee callee args vs = SOME cvs ==>
  ?j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc.
    callee.fn_name = nm /\
    LENGTH args = LENGTH (compute_operands inst) /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc
      (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)))
      st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |>
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `codegen_context_obligations Inv ctx cplan` >>
  `compute_operands inst = arg_ops /\ EVERY (\op. ~is_label_operand op) arg_ops` by
    (irule invoke_compute_operands >> gvs[] >> metis_tac[]) >>
  drule_all invoke_callee_entry_facts >> strip_tac >>
  `fn_has_retpc callee` by (first_x_assum irule >> metis_tac[]) >>
  `invoke_layout_wf ctx inst` by
    (fs[codegen_context_obligations_def, fmp_lowered_context_wf_def] >>
     metis_tac[]) >>
  drule_all invoke_callee_param_arity >> strip_tac >>
  `eval_operands (REVERSE (compute_operands inst)) (frame_view fn ra vs) =
     SOME (REVERSE args)` by
    (simp[eval_operands_reverse] >>
     drule_all invoke_operands_frame_values >> simp[]) >>
  `EVERY (\op. ~is_label_operand op) (compute_operands inst) /\
   LENGTH (compute_operands inst) <=
     LENGTH (SND (emit_input_plan INVOKE (compute_operands inst) nl ps)).ps_stack` by
    (qpat_x_assum `inst.inst_opcode = INVOKE` (fn th => fs[th]) >> gvs[]) >>
  drule_all invoke_generated_frame_prefix >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "call"
QED

Resume invoke_enter_callee[call]:
  `MEM callee ctx.ctx_functions /\ callee.fn_name = nm` by simp[] >>
  drule_all invoke_indexed_callee_target >>
  disch_then (qx_choosel_then [`j`, `off`, `pc`] strip_assume_tac) >>
  `?ret_off. FLOOKUP lo ret_lbl = SOME ret_off /\ ret_off < dimword (:256) /\
     FLOOKUP o2pc ret_off =
       SOME (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 3)` by
    (irule invoke_return_label_target >> qexistsl [`nm`, `ops`, `post`] >>
     simp[]) >>
  `asm_block_at prog mid.as_pc
     [AsmPushLabel ret_lbl; AsmPushLabel callee.fn_name; AsmOp "JUMP"]` by
    (irule invoke_packet_block >> metis_tac[]) >>
  `mid.as_stack = REVERSE args ++ saved ++ rest` by gvs[] >>
  qpat_x_assum `callee.fn_name = nm` (SUBST_ALL_TAC o SYM) >>
  drule_all invoke_call_entry >> strip_tac >>
  drule_all invoke_call_packet >> strip_tac >>
  `LENGTH args = LENGTH (compute_operands inst)` by
    metis_tac[eval_operands_some_length] >>
  `LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256)` by
    (`LENGTH args + 1 < 18` by decide_tac >>
     `18 < dimword (:256)` by simp[wordsTheory.dimword_def] >> decide_tac) >>
  qexistsl [`j`, `iops`, `prepared`, `rops`, `arranged`, `ret_lbl`, `ret_off`,
    `post`, `mid`, `saved`, `cas`, `pc`] >>
  gvs[] >> simp[asm_state_component_equality]
QED

Finalise invoke_enter_callee

(* After the callee returns to the return label: the label, the dead-output
   pops and the optimistic swap re-establish the caller's frame invariant. *)
Theorem invoke_return_frame:
  !ctx cplan lo o2pc prog fn ra rest mem0 arranged operands args vs mid saved vals
   callee rvs ret vs' asr r outs nl halting dfg inst term ret_lbl called
   pops popped opts swapped final.
  ordered_spill_regions cplan.cp_regions /\ MEM r cplan.cp_regions /\
  r.sr_fn_name = fn.fn_name /\
  fn_directly_calls ctx fn.fn_name callee.fn_name /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 arranged vs mid /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\
  LENGTH args = LENGTH operands /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  ALL_DISTINCT (stack_pop (LENGTH operands) arranged.ps_stack) /\
  DISJOINT (set (stack_pop (LENGTH operands) arranged.ps_stack))
    (FDOM arranged.ps_spilled) /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs)
    arranged.ps_stack /\
  (!op. op IN FDOM arranged.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outs) /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_return_state_rel ctx cplan callee rvs mid asr /\
  asr.as_stack = REVERSE vals ++ saved ++ rest /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state vs rvs)) = SOME vs' /\
  ALL_DISTINCT outs /\ EVERY (\x. ~retpc_var fn x) outs /\
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := stack_pop (LENGTH operands) arranged.ps_stack)
      outs) = (ret_lbl, called) /\
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  (!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)) /\
  asm_block_at prog asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?n fin.
    asm_steps lo o2pc prog n asr = AsmOK fin /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' fin /\
    fin.as_pc = asr.as_pc +
      LENGTH (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `consumed = arranged with
    ps_stack := stack_pop (LENGTH operands) arranged.ps_stack` >>
  `context_venom_asm_rel cplan lo consumed (frame_view fn ra vs)
     (mid with as_stack := saved)` by
    (simp[Abbr `consumed`] >> irule invoke_consumed_context >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ctx`, `mem0`, `rest`, `REVERSE args`] >> simp[]) >>
  suspend "local"
QED

Resume invoke_return_frame[local]:
  `spill_alloc_layout_wf consumed.ps_alloc consumed.ps_spilled /\
   ALL_DISTINCT consumed.ps_stack /\
   DISJOINT (set consumed.ps_stack) (FDOM consumed.ps_spilled) /\
   (!op. op IN FDOM consumed.ps_spilled ==>
     EVERY (\out. case op of Var x => x <> out | _ => T) outs) /\
   r.sr_spill_base <= consumed.ps_alloc.sa_spill_base /\
   consumed.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    simp[Abbr `consumed`] >>
  `EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs)
     consumed.ps_stack` by
    (simp[Abbr `consumed`] >>
     qpat_x_assum `arranged.ps_stack = _` (fn th =>
       qpat_x_assum `EVERY _ arranged.ps_stack`
         (mp_tac o ONCE_REWRITE_RULE [th])) >>
     simp[EVERY_APPEND]) >>
  `!op off. FLOOKUP consumed.ps_spilled op = SOME off ==>
     r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end /\
     EVERY (\out. case op of Var x => x <> out | _ => T) outs` by
    (rpt gen_tac >> strip_tac >>
     `op IN FDOM consumed.ps_spilled` by fs[FLOOKUP_DEF] >>
     fs[doSwapSimTheory.spill_alloc_layout_wf_def] >> res_tac >> simp[]) >>
  `fn_return_state_rel ctx cplan callee rvs (mid with as_stack := saved)
     (asr with as_stack := REVERSE vals ++ saved)` by
    fs[fn_return_state_rel_def, venom_asm_terminal_rel_def] >>
  qspecl_then [`ctx`, `cplan`, `fn`, `callee`, `r`, `lo`, `ra`, `consumed`, `outs`,
    `vals`, `vs`, `rvs`, `ret`, `vs'`, `mid with as_stack := saved`,
    `asr with as_stack := REVERSE vals ++ saved`] mp_tac invoke_return_context >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, fs[]]) >>
  strip_tac >>
  drule_all invoke_called_plan_fields >> strip_tac >>
  suspend "cleanup"
QED

Resume invoke_return_frame[cleanup]:
  `spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
   ALL_DISTINCT called.ps_stack /\
   DISJOINT (set called.ps_stack) (FDOM called.ps_spilled)` by
    (irule invoke_called_structural >> qexistsl [`consumed`, `outs`, `ret_lbl`] >>
     fs[]) >>
  `context_venom_asm_rel cplan lo called (frame_view fn ra vs')
     ((asr with as_pc := asr.as_pc + 1) with as_stack := REVERSE vals ++ saved)` by
    (qpat_x_assum `context_venom_asm_rel _ _ (consumed with ps_stack := _) _ _` mp_tac >>
     simp[context_venom_asm_rel_def]) >>
  `asm_block_at prog asr.as_pc [AsmLabel ret_lbl] /\
   asm_block_at prog (asr.as_pc + 1)
     (execute_plan cplan.cp_initial_fmp (pops ++ opts))` by
    (qpat_x_assum `asm_block_at prog asr.as_pc _` mp_tac >>
     pure_rewrite_tac[execute_plan_def, MAP, FLAT, exec_stack_op_def,
       asm_block_at_append] >> simp[]) >>
  `asm_steps lo o2pc prog 1 asr = AsmOK (asr with as_pc := asr.as_pc + 1)` by
    (irule label_op_asm_steps >> qexists `ret_lbl` >> simp[]) >>
  qspecl_then [`outs`, `nl`, `halting`, `called`, `pops`, `popped`, `dfg`, `inst`,
    `term`, `opts`, `swapped`, `final`, `cplan`, `lo`, `o2pc`, `prog`,
    `frame_view fn ra vs'`,
    `(asr with as_pc := asr.as_pc + 1) with as_stack := REVERSE vals ++ saved`,
    `r`, `ctx`, `fn.fn_name`] mp_tac invoke_cleanup_context >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, fs[]]) >>
  disch_then (qx_choose_then `fin0` strip_assume_tac) >>
  suspend "lift"
QED

Resume invoke_return_frame[lift]:
  qspecl_then [`LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))`, `lo`, `o2pc`,
    `prog`, `asr with as_pc := asr.as_pc + 1`, `REVERSE vals ++ saved`, `rest`,
    `fin0`] mp_tac asm_steps_frame >>
  impl_tac >- fs[] >> strip_tac >>
  `(asr with as_pc := asr.as_pc + 1) with as_stack := REVERSE vals ++ saved ++ rest =
     asr with as_pc := asr.as_pc + 1` by
    simp[asm_state_component_equality] >>
  qexistsl [`1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))`,
    `fin0 with as_stack := fin0.as_stack ++ rest`] >>
  conj_tac >- (irule asm_steps_compose_ok >>
               qexists `asr with as_pc := asr.as_pc + 1` >> fs[]) >>
  reverse conj_tac
  >- simp[execute_plan_def, exec_stack_op_def] >>
  drule invoke_return_frame_fields >> strip_tac >>
  `!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
     read_byte b asr.as_memory = read_byte b mem0` by
    (qspecl_then [`ctx`, `cplan`, `lo`, `fn`, `ra`, `rest`, `mem0`, `arranged`,
       `vs`, `mid`, `callee`, `rvs`, `mid`, `asr`] mp_tac
       invoke_return_outside_closure >> simp[]) >>
  qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fn_frame_inv_def] >> strip_tac >>
  rpt conj_tac >>
  qpat_x_assum `final = _` SUBST_ALL_TAC >>
  FIRST [first_assum ACCEPT_TAC,
         rpt strip_tac >> fs[] >> NO_TAC,
         qexists `r` >> fs[] >> NO_TAC]
QED

Finalise invoke_return_frame

(* The structural facts invoke_return_frame needs about the arranged state. *)
Theorem invoke_entry_structural:
  !spillbase ps inst nl iops prepared dfg rops arranged.
  generated_plan_state_wf spillbase ps /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
  reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) ==>
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  ALL_DISTINCT (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) /\
  DISJOINT (set (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack))
    (FDOM arranged.ps_spilled) /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) arranged.ps_stack /\
  (!op. op IN FDOM arranged.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs)
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (drule stack_get_depth_props >> simp[stack_peek_def] >>
         strip_tac >> disj1_tac >>
         qpat_x_assum `EL _ _ = op` (SUBST1_TAC o SYM) >>
         irule EL_MEM >> decide_tac) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[FLOOKUP_DEF]) >>
  `residual_budget_wf spillbase [] ps` by
    (fs[generated_plan_state_wf_def] >>
     metis_tac[residual_budget_wf_canonical]) >>
  qspecl_then [`spillbase`, `ps`, `compute_operands inst`, `nl`, `iops`,
    `prepared`, `dfg`, `rops`, `arranged`, `inst.inst_outputs`] mp_tac
    invoke_prepared_structural >>
  impl_tac >- simp[] >>
  simp[plan_state_residual_wf_def]
QED

Theorem invoke_mem_front[local]:
  !l x. MEM x l /\ LAST l <> x ==> MEM x (FRONT l)
Proof
  rpt strip_tac >> `l <> []` by (strip_tac >> fs[]) >>
  drule APPEND_FRONT_LAST >>
  disch_then (fn th => qpat_x_assum `MEM x l`
    (mp_tac o ONCE_REWRITE_RULE [GSYM th])) >>
  simp[]
QED

Theorem invoke_do_swap_last[local]:
  !dist ps ops ps' off.
  do_swap dist ps = (ops,ps') /\ ops <> [] ==> LAST ops <> SOSpill off
Proof
  rw[do_swap_def] >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[REVERSE_APPEND, LAST_APPEND_CONS]
QED

Theorem invoke_foldl_pop_last[local]:
  !f l ops0 ps0 ops ps'.
  (!a b v. FST (f (a,b) v) = a \/
           ?sw n. FST (f (a,b) v) = a ++ sw ++ [SOPop n]) /\
  FOLDL f (ops0, ps0) l = (ops, ps') ==>
  ops = ops0 \/ ?pre n. ops = pre ++ [SOPop n]
Proof
  gen_tac >> Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `f (ops0,ps0) h` >> fs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`ops0`, `ps0`, `h`] mp_tac) >> simp[] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem invoke_popmany_last[local]:
  !to_pop ps ops ps' off.
  popmany_plan to_pop ps = (ops,ps') /\ ops <> [] ==> LAST ops <> SOSpill off
Proof
  Cases >> simp[popmany_plan_def] >> rpt gen_tac >> rw[]
  >- (pairarg_tac >> gvs[] >> simp[LAST_APPEND_CONS]) >>
  fs[popmany_individual_def] >>
  drule_at (Pos last) invoke_foldl_pop_last >>
  (impl_tac >- (rpt gen_tac >> simp[] >> CASE_TAC >>
                simp[pairTheory.UNCURRY] >> metis_tac[])) >>
  strip_tac >> gvs[]
QED

(* Spill offsets of the cleanup are covered by the prefix spill invariant on
   FRONT ops: the last op of the plan is never a spill. *)
Theorem invoke_cleanup_spill_bounds:
  !f lo iops rops b lbl outs nl halting called pops popped dfg inst term opts swapped ps.
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  prefix_spill_wf f lo (FRONT (iops ++ rops ++
    [SOPushLabel lbl; SOPushLabel b; SOEmit "JUMP"; SOLabel lbl] ++ pops ++ opts)) ps ==>
  !off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  `!off. LAST (pops ++ opts) <> SOSpill off` by
    (gen_tac >> Cases_on `opts = []`
     >- (gvs[] >> Cases_on `pops = []` >- gvs[] >>
         qpat_x_assum `(if _ then _ else _) = (pops,popped)` mp_tac >>
         rw[] >> metis_tac[invoke_popmany_last]) >>
     simp[LAST_APPEND_NOT_NIL] >>
     qpat_x_assum `(if _ then _ else _) = (opts,swapped)` mp_tac >>
     rw[optimistic_swap_plan_def] >> gvs[AllCaseEqs()] >>
     metis_tac[invoke_do_swap_last]) >>
  `MEM (SOSpill off) (FRONT (iops ++ rops ++
     [SOPushLabel lbl; SOPushLabel b; SOEmit "JUMP"; SOLabel lbl] ++ pops ++ opts))` by
    (irule invoke_mem_front >> simp[] >>
     `pops ++ opts <> []` by (strip_tac >> fs[]) >>
     `LAST (iops ++ rops ++
        [SOPushLabel lbl; SOPushLabel b; SOEmit "JUMP"; SOLabel lbl] ++ pops ++ opts) =
      LAST (pops ++ opts)` by
       metis_tac[LAST_APPEND_NOT_NIL, APPEND_ASSOC] >>
     fs[]) >>
  metis_tac[prefix_spill_wf_address_bound]
QED

Theorem invoke_return_block:
  !prog pc f iops rops a b pops opts.
  asm_block_at prog pc (execute_plan f
    (iops ++ rops ++ [SOPushLabel a; SOPushLabel b; SOEmit "JUMP"; SOLabel a] ++
     pops ++ opts)) ==>
  asm_block_at prog (pc + LENGTH (execute_plan f (iops ++ rops)) + 3)
    (execute_plan f (SOLabel a :: (pops ++ opts)))
Proof
  rpt gen_tac >>
  `iops ++ rops ++ [SOPushLabel a; SOPushLabel b; SOEmit "JUMP"; SOLabel a] ++
     pops ++ opts =
   (iops ++ rops ++ [SOPushLabel a; SOPushLabel b; SOEmit "JUMP"]) ++
     (SOLabel a :: (pops ++ opts))` by simp[] >>
  pop_assum SUBST1_TAC >>
  `LENGTH (execute_plan f (iops ++ rops ++
     [SOPushLabel a; SOPushLabel b; SOEmit "JUMP"])) =
   LENGTH (execute_plan f (iops ++ rops)) + 3` by
    simp[execute_plan_append, execute_plan_def, exec_stack_op_def] >>
  strip_tac >>
  qpat_x_assum `asm_block_at _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [asm_block_at_append] o
     ONCE_REWRITE_RULE [execute_plan_append]) >>
  qpat_x_assum `LENGTH _ = _` (fn th => fs[th])
QED
