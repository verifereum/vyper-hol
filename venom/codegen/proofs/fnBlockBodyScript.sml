(*
 * The rest of a function's run from inside one of its blocks, simulated by
 * the block's DFS code from fn_frame_inv.  Shared by the two steps of the
 * fuel induction behind venomToAsmProps (fnEntryStep, fnBlockStep): each
 * simulates its block's prefix (entry parameters; cleanup and PHIs) and
 * hands the rest of the run to block_body_frame_sim.
 *
 * TOP-LEVEL:
 *   block_rest            - the run_blocks result from inside a block
 *   block_body_frame_sim  - CHEATED: the rest of the run, simulated
 *)

Theory fnBlockBody
Ancestors
  fnBlockPlanStatic fnAliasStep fnFrameStepsRevertForwardDeep
  fnFrameDeep fnLineageStatic fnPlanPrefix fnSimSpec fnFrameSteps fnFrameBoundary fnFrameTerminal gasFrameSim
  genFrameSim fnPlanPlace fnPlanCover fnAliasInv fnPlanLineage frameRel
  venomExecSemantics

(* What run_blocks (SUC fuel) returns once its block has reached state vs:
   the rest of the block, then the rest of the function from its successor
   (run_blocks_unfold, run_block_def). *)
Definition block_rest_def:
  block_rest fuel ctx fn bb vs =
    case exec_block fuel ctx bb vs of
      OK vs' => if vs'.vs_halted then Halt vs' else run_blocks fuel ctx fn vs'
    | res => res
End

(* vs is at instruction k of block bb, past its PHIs, and fn_frame_inv
   holds with ps, the planner's state at k when bb is planned from its
   lineage state ps_l (with the cleanup fields h, promised that
   lineage_state_block_plan picks, which also gives the alloc equation).
   That plan is the block's DFS code block_ops, placed at pc0, and as is
   at its rest_ops, the code of the instructions from k on.  The entry
   step starts here after the parameters (entry_params_frame_sim), the
   block step after the cleanup and the PHI prefix.

   Why it should hold: by induction on the instructions from k.  Each runs
   by its instruction lemma, in the fnFrameDeep form (operands at any
   depth, repeated dead_stack_marker slots): gen_inst_frame_sim_deep,
   gas_inst_frame_sim_owned_deep, gen_invoke_frame_sim_deep with
   gen_fn_sim_at fuel for the callee, the halt, abort and return steps,
   revert_forward_frame_sim_deep.  Their static premises at the planner
   state ps come from fnBlockPlanStatic$block_plan_state_static, the slot
   alias is carried through each step by fnAliasStep$alias_step_preserve,
   and their
   memory premises come from Inv (codegen_memory_obligations,
   reachability_closed).  A JMP or JNZ ends the block at a successor
   whose code is placed (dfs_block_code_placed), entered with the
   lineage entry from this block, so gen_fn_frame_sim_at fuel finishes
   the run and its assembly steps are added to the block's. *)
Theorem block_body_frame_sim:
  !fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0.
    gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    ~vs.vs_call_ctx.cc_static /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\
    (!inst. active_inst fn inst vs ==> Inv ctx fn inst vs) /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_reachable fn bb.bb_label /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      k ps /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions))
      (DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps = SOME (rest_ops, ps_after) /\
    block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
    phi_prefix_length bb.bb_instructions <= k /\
    vs.vs_inst_idx = k /\
    asm_block_at prog pc0 (execute_plan cp.cp_initial_fmp block_ops) /\
    as.as_pc = pc0 + LENGTH (execute_plan cp.cp_initial_fmp
                                 (SOLabel bb.bb_label :: prefix_ops)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
    ==>
    (!vs'. block_rest fuel ctx fn bb vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. block_rest fuel ctx fn bb vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as') /\
    (!ret vs'. block_rest fuel ctx fn bb vs = IntRet ret vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE ret.iret_values ++ rest /\
               context_memory_rel cp vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cp b /\
                    ~closure_spill_byte ctx cp fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as')
Proof
  cheat
QED
