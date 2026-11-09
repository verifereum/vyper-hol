(*
 * Leaf B of the label-discipline proof: the control and terminal steps of
 * a block, run on the symbolic machine without SymBad.  Each statement is
 * codegen's own deep-tier lemma with the symbolic premises and conclusions
 * added, over the same n steps: a step that continues keeps the symbolic
 * frame invariant, a RET leaves the returned values as words above the
 * caller's symbolic stack, and a halt or abort ends the symbolic run.
 *
 * A jump's target is a code label of the program (MEM (AsmLabel l) prog):
 * the symbolic machine jumps only to code labels.
 *
 * TOP-LEVEL:
 *   sym_jmp_frame_sim_deep            - JMP
 *   sym_jnz_frame_sim_deep            - JNZ
 *   sym_ret_frame_sim_deep            - RET
 *   sym_halt_frame_sim_deep           - an instruction that halts
 *   sym_abort_frame_sim_deep          - an instruction that aborts
 *   sym_gas_frame_sim_deep            - GAS
 *   sym_revert_forward_frame_sim_deep - a forwarded revert
 *)
Theory symFrameControl
Ancestors
  codegenSymRel fnFrameDeepJmp fnFrameDeepJnz fnFrameDeepRet fnFrameDeepHalt
  fnFrameDeepAbort fnFrameDeepGas fnFrameStepsRevertForwardDeep asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs

Theorem sym_jmp_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   target target_bb target_stack off pc_t
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JMP /\
    inst.inst_operands = [Label target] /\
    inst.inst_outputs = [] /\
    lookup_block target fn.fn_blocks = SOME target_bb /\
    target_stack =
      MAP Var (input_vars_from bb_label target_bb.bb_instructions
                 (live_vars_at liveness target 0)) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    (!off. MEM (SORestore off) (FST (restore_spilled_plan target_stack ps)) ==>
           off < dimword(:256)) /\
    LENGTH target_stack <=
      LENGTH (SND (restore_spilled_plan target_stack ps)).ps_stack /\
    pending_inventory_wf target_stack ps /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      target_stack /\
    (!op at. MEM op target_stack /\
       (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg op at ==>
       operand_val (frame_view fn ra vs) lo op =
       operand_val (frame_view fn ra vs) lo at) /\
    FLOOKUP lo target = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc_t /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (* SSA: planner-equivalent operands have the same kind. *)
    codegen_ready_fn fn /\
    MEM (AsmLabel target) prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = pc_t /\
        vs' = jump_to target vs /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  cheat
QED

Theorem sym_jnz_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   cond_op if_nz if_z off_nz off_z pc_nz pc_z
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
    (* The planner drops label operands of jumps, so a label condition would
       emit nothing; label_positions_ok excludes it. *)
    ~is_label_operand cond_op /\
    inst.inst_outputs = [] /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_liveness ps)).ps_stack /\
    (is_var_operand cond_op ==>
      IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
    eval_operand cond_op vs = operand_val (frame_view fn ra vs) lo cond_op /\
    (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg cond_op at ==>
       operand_val (frame_view fn ra vs) lo cond_op =
       operand_val (frame_view fn ra vs) lo at) /\
    cond_op <> dead_stack_marker /\
    (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    FLOOKUP lo if_nz = SOME off_nz /\ off_nz < dimword (:256) /\
    FLOOKUP o2pc off_nz = SOME pc_nz /\
    FLOOKUP lo if_z = SOME off_z /\ off_z < dimword (:256) /\
    FLOOKUP o2pc off_z = SOME pc_z /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (* SSA, and the shape facts that keep labels out of the condition. *)
    codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
    MEM (AsmLabel if_nz) prog /\ MEM (AsmLabel if_z) prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        ((vs' = jump_to if_nz vs /\ as'.as_pc = pc_nz) \/
         (vs' = jump_to if_z vs /\ as'.as_pc = pc_z)) /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  cheat
QED

Theorem sym_ret_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0 pc_ret
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = RET /\
    MEM inst (fn_insts (reachable_fn fn)) /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
    inst_wf inst /\
    generated_plan_state_wf_marked base ps /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
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
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    ps'.ps_stack = [] /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !rv vs'. step_inst fuel ctx inst vs = IntRet rv vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        as'.as_pc = pc_ret /\
        as'.as_stack = REVERSE rv.iret_values ++ rest /\
        context_memory_rel cp vs'.vs_memory as'.as_memory /\
        (!b. context_spill_byte cp b /\
             ~closure_spill_byte ctx cp fn.fn_name b ==>
             read_byte b as'.as_memory = read_byte b mem0) /\
        shared_state_rel vs' as' /\
        sym_steps prog env n ss = SymOK ss' /\
        asm_sym_rel prog env as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
        (!b. context_spill_byte cp b /\
             ~closure_spill_byte ctx cp fn.fn_name b ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  cheat
QED

Theorem sym_halt_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
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
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  cheat
QED

Theorem sym_abort_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    ~vs.vs_call_ctx.cc_static /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    (inst.inst_opcode = ASSERT ==>
     ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc
                (execute_plan cp.cp_initial_fmp revert_postamble)) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
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
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  cheat
QED

Theorem sym_gas_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
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
    generated_plan_state_wf_marked base ps /\
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
       on the stack at any depth or available from the spill map.
       generated_plan_state_wf_marked is structural and does not imply ownership. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
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
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          context_spill_step_safe cp vs vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  cheat
QED

Theorem sym_revert_forward_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j base ps vs as ops
   ps_end ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\
    generated_plan_state_wf_marked base ps /\
    (!k inst op.
       i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  cheat
QED
