(*
 * Terminal results of an instruction in the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation: an instruction whose step Halts
 * or Aborts, run against frameRel$fn_frame_inv as genFrameSim's lemmas do.
 * The conclusion is venom_asm_terminal_rel, which reads no stack, so the
 * frame's rest needs no lifting beyond the run on top ++ rest.
 *
 * TOP-LEVEL (all CHEATED):
 *   gen_inst_halt_frame_sim   — an instruction whose step Halts
 *   gen_inst_abort_frame_sim  — an instruction whose step Aborts
 *)

Theory fnFrameTerminal
Ancestors
  genFrameSim frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst livenessDefs dfgDefs cfgDefs

(* Used for an instruction whose step Halts (STOP, RETURN, SELFDESTRUCT)
   in the block induction: gen_fn_frame_simulation's Halt clause.  The
   premises are gen_inst_frame_sim's minus those only an OK result uses
   (SSA freshness, PHI soundness, the output state's region), as the
   block induction supplies them for every instruction.  INVOKE's Halt is
   gen_invoke_frame_sim's.

   Why it should hold: gen_inst_halt_sim (genBlockSim) run on the frame's
   own stack against frame_view fn ra vs with the assembly memory, as
   gen_inst_frame_sim does; RETURN reads only bytes outside every spill
   region (source_memory_reads_disjoint), where context_memory_rel makes
   the memories agree; the terminal step on top ++ rest halts with the
   same non-stack fields, and venom_asm_terminal_rel reads no stack.
   Operands are never return-PC variables (opaque_use_ok). *)
Theorem gen_inst_halt_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
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
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as'
Proof
  cheat
QED

(* Used for an instruction whose step Aborts (REVERT, ASSERT,
   ASSERT_UNREACHABLE, INVALID, a faulting RETURNDATACOPY or CREATE) in
   the block induction: gen_fn_frame_simulation's Abort clause.  Premises
   as gen_inst_halt_frame_sim's, plus genBlockSim$gen_inst_abort_sim's
   placement of the shared revert postamble for ASSERT
   (fnPlanPlace$revert_postamble_placed) and the own-label resolution
   ASSERT_UNREACHABLE's fresh label needs (fnPlanPlace$dfs_block_code_placed).
   A revert forwarding's RETURNDATACOPY and REVERT are exempt from the
   memory obligations; they are revert_forward_frame_sim's.

   Why it should hold: gen_inst_abort_sim lifted as in
   gen_inst_halt_frame_sim; spill offsets are disjoint by
   generated_plan_state_wf; REVERT's payload is outside every spill
   region. *)
Theorem gen_inst_abort_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    generated_plan_state_wf base ps /\
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
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
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
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as'
Proof
  cheat
QED
