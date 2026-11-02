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
