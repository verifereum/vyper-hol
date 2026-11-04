(*
 * Frame-invariant steps the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation needs besides genFrameSim's
 * OK-result instruction cases: a join block's PHI prefix, the terminal
 * (Halt, Abort) results of an instruction, and revert forwarding.
 *
 * Each runs against frameRel$fn_frame_inv, as genFrameSim's lemmas do.
 * The terminal ones end in venom_asm_terminal_rel, which reads no stack,
 * so the frame's rest needs no lifting beyond the run on top ++ rest.
 *
 * TOP-LEVEL (all CHEATED):
 *   phi_prefix_frame_sim      — a join block's PHI prefix
 *   gen_inst_halt_frame_sim   — an instruction whose step Halts
 *   gen_inst_abort_frame_sim  — an instruction whose step Aborts
 *   revert_forward_frame_sim  — RETURNDATACOPY ... REVERT forwarding
 *)

Theory fnFrameSteps
Ancestors
  genFrameSim fnPlanLineage frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst livenessDefs dfgDefs cfgDefs

(* ===== PHI prefix ===== *)

(* Used at the start of every non-entry block body: run_blocks evaluates
   the block's PHIs in parallel (eval_phis) and starts exec_block past
   them, while the code runs generate_phi_plan once per PHI.  It is
   stated over the whole prefix because the Venom side has no state
   between two PHIs.  The block body continues from ps1 with the
   generate_block_insts_plan call the planner makes for the rest.  ps is
   the lineage entry state from pred (the block vs_prev_bb names) with
   whatever cleanup fields lineage_state_block_plan chose; a PHI block has
   at least two predecessors, so no clean_stack_plan runs before it.  The
   region premise is for the block's end state: the allocator only grows
   along the plan (allocMono), so it covers ps1.

   Why it should hold: the lineage entry from pred leaves pred's PHI
   operands on the stack (the JMP reorder to input_vars_from pred), each
   holding the value resolve_phi pred reads (fn_frame_inv), with return-PC
   PHIs reading ra on both sides (retpc_shape_ok).  Each PHI pokes or dups
   that slot into its output; a PHI output used by another PHI of the
   same block is read at its old value by eval_phis, and its old slot is
   overwritten in the same prefix since it is dead after it (SSA), so the
   stack agrees with s_phi once the whole prefix has run.  Dead PHI
   outputs are popped.  The alias invariant holds for PHI outputs, which
   are their own roots. *)
Theorem phi_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb pred
   ps_l h promised ps base vs as s_phi phis body ops ps3 r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf base ps /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops)
    ==>
    ?phi_ops ps1 body_ops n as'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 =
        SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at))
Proof
  cheat
QED

(* ===== Terminal results ===== *)

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

(* ===== Revert forwarding ===== *)

(* Used in the block induction at a revert forwarding's RETURNDATACOPY
   (in_revert_forward fn vs at its first index i), in place of
   gen_inst_frame_sim and the abort step for the rest of the block:
   codegen_memory_obligations exempts both instructions, so their memory
   premises are not available.  The segment runs to the block's end (the
   REVERT is its terminator) and only ends in Abort (or Error).

   The plan from i has no SORestore (as ruled) and no SOSpill: the copy
   may write [p, p + rds) over spill slots when p = 0, so a restore after
   it would read clobbered bytes, and a spill after it would change the
   payload the REVERT reads.  The ownership premise is the block
   invariant at i for the segment's operands not defined inside it; the
   opcode premise is assembly_target_safe at the code's position
   (codegen_assembly + asm_block_at).

   Why it should hold: with no restore or spill, the segment's code only
   permutes the stack, pushes, and runs RETURNDATACOPY and REVERT, so the
   stack keeps the values fn_frame_inv gives (ASSIGNs copy, the alias
   premise covers alias-only reorders); both sides copy the same return
   data to the same range, or both fault when it is out of bounds; the
   REVERT's operands resolve to the copy's through the ASSIGNs
   (revert_forward_pair), so both read the bytes just copied. *)
Theorem revert_forward_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j base ps vs as ops
   ps_end ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\
    generated_plan_state_wf base ps /\
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
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as'
Proof
  cheat
QED
