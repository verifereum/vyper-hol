(*
 * Frame-invariant steps the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation needs besides genFrameSim's
 * OK-result instruction cases and fnFrameTerminal's Halt and Abort
 * results: a join block's PHI prefix and revert forwarding.
 *
 * Each runs against frameRel$fn_frame_inv, as genFrameSim's lemmas do.
 *
 * TOP-LEVEL:
 *   phi_prefix_frame_sim      — a join block's PHI prefix (CHEATED)
 *   revert_forward_frame_sim  — RETURNDATACOPY ... REVERT forwarding
 *)

Theory fnFrameSteps
Ancestors
  fnFrameStepsPhi genFrameSim fnPlanLineage fnPlanPrefix frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst livenessDefs dfgDefs cfgDefs
  fnFrameStepsRevertForward

(* ===== PHI prefix ===== *)

(* Used at the start of every non-entry block body: run_blocks evaluates
   the block's PHIs in parallel (eval_phis) and starts exec_block past
   them, while the code runs generate_phi_plan once per PHI.  It is
   stated over the whole prefix because the Venom side has no state
   between two PHIs.  The block body continues from ps1 with the
   generate_block_insts_plan call the planner makes for the rest.  ps is
   the lineage entry state from pred (the block vs_prev_bb names) with
   whatever cleanup fields lineage_state_block_plan chose; the block does
   not have exactly one predecessor, so no clean_stack_plan runs before
   it (generate_block_plan).  The
   region premise is for the block's end state: the allocator only grows
   along the plan (allocMono), so it covers ps1.

   Why it should hold: the lineage entry from pred leaves pred's PHI
   operands on top of the stack (the JMP reorder to input_vars_from pred),
   with only dead_stack_marker entries below them, and no other stack or
   spill entry is or normalizes to an output of the block
   (fnPlanLineageJoin$lineage_entry_join_stack), each holding the value
   resolve_phi pred reads (fn_frame_inv), with return-PC PHIs reading ra
   on both sides (retpc_shape_ok).  Each PHI pokes that slot into its
   output: no PHI operand is live past the prefix (phi_block_ready), so
   the dup branch never runs, and no PHI reads another PHI output of the
   same block (that output would then be live past the prefix), so the
   sequential code agrees with the parallel eval_phis.  Dead PHI outputs
   are popped.  The alias invariant holds for PHI outputs, which are their
   own roots. *)
Theorem phi_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb pred
   ps_l h promised ps base vs as s_phi phis body ops ps3 r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
           off < dimword (:256)) /\
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
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps =
        SOME (phi_ops, ps1) /\
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
  rpt gen_tac >> strip_tac >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `fn`, `ch`, `growth`, `spill_base`,
               `lbl_ctr`, `pred`, `bb`, `vs.vs_current_bb`, `ps_l`, `h`,
               `promised`, `ps`, `phis`, `body'`]
    mp_tac fnFrameStepsPhiTheory.phi_join_entry_hits >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `fn`, `ch`, `growth`, `spill_base`,
               `lbl_ctr`, `pred`, `bb`, `vs.vs_current_bb`, `ps_l`, `h`,
               `promised`, `ps`, `phis`, `body'`]
    mp_tac fnFrameStepsPhiTheory.phi_join_entry_fresh >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  qspecl_then [`ctx`, `cp'`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
               `fn`, `bb`, `pred`, `base'`, `ps`, `vs`, `as`, `s_phi`, `phis`,
               `body'`, `ops`, `ps3`, `r`, `ra`, `rest`, `mem0`]
    mp_tac fnFrameStepsPhiTheory.phi_prefix_hits_frame_sim >>
  impl_tac >- asm_rewrite_tac[] >>
  simp[]
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
   (revert_forward_pair), so both read the bytes just copied.  vs is
   arbitrary, so the REVERT's operand values equal the copy's through
   the normalize_operand premise and the ownership premise, not by
   re-running the block prefix: under SSA, dfg_defs maps each ASSIGN
   output to its ASSIGN. *)
Theorem revert_forward_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j base ps vs as ops
   ps_end ra rest mem0.
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
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  drule rf_spills_separated_entry >> strip_tac >>
  drule_all rf_entry_forward_abort >> simp[]
QED
