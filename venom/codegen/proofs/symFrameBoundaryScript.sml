(*
 * Block-boundary pieces of the label-discipline proof on the symbolic
 * machine: a block's PHI prefix (after a cleanup when the block has one
 * predecessor) and a function's parameter prologue.  Each
 * is codegen's own lemma with the symbolic premises and conclusions added,
 * over the same n steps.  The prologue starts from the entry symbolic
 * state of sym_fn_sim_at and establishes the symbolic frame invariant,
 * with the memory labels at entry as the frame's labs0.
 *
 * TOP-LEVEL:
 *   sym_phi_prefix_frame_sim          - a join block's PHI prefix
 *   sym_single_pred_prefix_frame_sim  - a one-predecessor block's cleanup
 *                                       and PHI prefix
 *   sym_entry_prefix_frame_sim        - a function's parameter prologue
 *)
Theory symFrameBoundary
Ancestors
  codegenSymRel fnFrameSteps fnFrameSinglePred fnEntryParams fnFrameBoundary asmSymBridge asmSymSem
  frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs

Theorem sym_phi_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb pred
   ps_l h promised ps base vs as s_phi phis body ops ps3 r ra rest mem0
   env ret srest labs0 ss.
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
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
    ==>
    ?phi_ops ps1 body_ops n as' ss'.
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
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  cheat
QED

Theorem sym_single_pred_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised ps base vs as s_phi clean_ops ps2 phis body ops ps3
   r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
    ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps2 =
        SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 =
        SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  cheat
QED

Theorem sym_entry_prefix_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs as ra rest Inv
   env ret srest ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    fn_entry_inv Inv ctx fn vs /\ reachability_closed Inv ctx /\
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp
         (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    (* ----- The symbolic side: the entry symbolic state of sym_fn_sim_at *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    asm_sym_rel prog env as ss /\
    ss.sym_stack =
      (if fn_has_retpc fn then [Lab ret 0] else []) ++
      MAP Val (REVERSE vs.vs_params) ++ srest /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b)
    ==>
    ?n as' vs_p ss'.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp
                  (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
        exec_block fuel ctx (HD fn.fn_blocks) vs_p /\
      vs_p.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      fn_frame_inv ctx cp lo fn ra rest as.as_memory ps1 vs_p as' /\
      vs_p.vs_current_bb = vs.vs_current_bb /\
      vs_p.vs_labels = vs.vs_labels /\
      vs_p.vs_call_ctx = vs.vs_call_ctx /\
      (!inst. active_inst fn inst vs_p ==> Inv ctx fn inst vs_p) /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra vs_p) lo at =
         operand_val (frame_view fn ra vs_p) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest ss.sym_mem_labels ps1 as' ss'
Proof
  cheat
QED
