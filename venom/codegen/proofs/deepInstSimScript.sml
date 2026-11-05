(*
 * genBlockSim's gen_inst_ok_sim over a planner state with repeated
 * dead_stack_marker slots (generated_plan_state_wf_marked), with operands
 * owned at any stack depth and only an address bound on the plan's spill
 * and restore offsets.  The input preparation runs on deepResidualSim's
 * marker-tolerant numeric chain.
 *
 * TOP-LEVEL:
 *   gen_inst_ok_sim_marked
 *)

Theory deepInstSim
Ancestors
  deepResidualSim fnPlanPrefix regularPostfixSim genBlockSim
  generatedPrefixSim preparedPrefixSim generatedReorderSim reorderSim
  doSwapSim mixedPrefixSim codegenRel blockSimHelpers planSpillBounds
  stackOpSim stackModel stackPlanGen stackPlanOps stackPlanTypes planExec
  asmSem venomExecSemantics venomState venomInst
  sorting list rich_list arithmetic

Theorem gen_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
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
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  cheat
QED
