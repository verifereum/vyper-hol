(*
 * gen_jmp_frame_sim_deep: genFrameSim's gen_jmp_frame_sim for JMP, with
 * operands at any stack depth, repeated dead_stack_marker slots
 * (generated_plan_state_wf_marked) and only an address bound on the
 * plan's spill and restore offsets.  fnFrameDeep collects it with the
 * other instruction frame lemmas the block induction composes.
 *
 * TOP-LEVEL:
 *   gen_jmp_frame_sim_deep
 *)

Theory fnFrameDeepJmp
Ancestors
  deepResidualSim fnPlanPrefix genFrameSim frameRel contextCodegenRel
  codegenRel blockSimHelpers unitShapeDefs genBlockSim mixedPrefixSim
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs

(* gen_jmp_frame_sim with any-depth ownership, generated_plan_state_wf_marked and an
   address bound on spill and restore offsets. *)
Theorem gen_jmp_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   target target_bb target_stack off pc_t.
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
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = pc_t /\
        vs' = jump_to target vs
Proof
  cheat
QED
