(*
 * The symbolic fuel induction: the two steps of fnEntryStep and fnBlockStep
 * with the symbolic run added, and their closure over all fuel.  The
 * concrete function-level statements at each fuel come from codegen's own
 * steps (fn_entry_block_step, fn_block_frame_step).
 *
 * TOP-LEVEL:
 *   sym_fn_entry_block_step  - sym_fn_sim_at (SUC fuel) from the four
 *                              function statements at fuel
 *   sym_fn_block_frame_step  - sym_fn_frame_sim_at (SUC fuel), likewise
 *   sym_fn_sims_all          - all four at every fuel
 *)
Theory symFnStep
Ancestors
  symFnStepOwn symFnPrefixOwn symFrameBoundaryPairing asmSymOwnStep
  asmOwnCodeInvariant codegenSymOwnRel fnBlockBodySteps fnPlanPlaceRevertPostamble
  symBlockBody symFrameBoundary symFnSimSpec codegenSymRel fnEntryStep
  fnBlockStep fnBlockStepHelpers fnBlockBody fnSimSpec asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel venomExecSemantics
  venomState planExec stackOpSim blockSimHelpers fnPlanLineageEntryProduction

(* These names are representation variables in the boundary contracts. *)
val _ = Parse.hide "base";
val _ = Parse.hide "body";
Theorem sym_frame_inv_cleanup_fields:
  !prog env ctx cp fn ret srest labs0 ps h promised as ss.
    sym_frame_inv prog env ctx cp fn ret srest labs0
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      as ss <=>
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
Proof
  simp[sym_frame_inv_def, sym_kinds_ok_def]
QED

Theorem sym_label_block_steps:
  !lo o2pc prog as fmp lbl ops env ctx cp fn ret srest labs0 ps ss.
    asm_block_at prog as.as_pc (execute_plan fmp (SOLabel lbl :: ops)) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    asm_steps lo o2pc prog 1 as = AsmOK (as with as_pc := as.as_pc + 1) /\
    sym_steps prog env 1 ss =
      SymOK (ss with sym_base := ss.sym_base with as_pc := as.as_pc + 1) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps
      (as with as_pc := as.as_pc + 1)
      (ss with sym_base := ss.sym_base with as_pc := as.as_pc + 1) /\
    asm_block_at prog (as.as_pc + 1) (execute_plan fmp ops)
Proof
  rpt gen_tac >> strip_tac >> drule label_block_steps >> strip_tac >> simp[] >>
  gvs[sym_frame_inv_def, asm_sym_rel_def] >>
  conj_tac
  >- (`asm_block_at prog ss.sym_base.as_pc [AsmLabel lbl]` by
        gvs[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
      drule symShuffleSimTheory.sym_steps_label >>
      simp[asmSemTheory.asm_next_def]) >>
  gvs[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_block_prefix_step_exact:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised vs as s_phi clean_ops ps2 ops ps3 r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    generated_plan_state_wf_marked spill_base ps_l /\
    (!op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1 ==>
     !op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==> off < dimword (:256)) /\
    (!at. MEM at ps_l.ps_stack \/ at IN FDOM ps_l.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps_l vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = bb.bb_instructions /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan liveness cfg fn bb
            (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
     else ([], ps_l with <| ps_cleanup_height := h;
                            ps_cleanup_promised := promised |>)) =
      (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps_l as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (phi_prefix_length bb.bb_instructions)
        (non_param_insts bb) ps2 = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (phi_prefix_length bb.bb_instructions)
        (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb))
        ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss' /\
      n = LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops))
Proof
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by simp[] >>
  drule label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  rename1 `sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_l as ss` >>
  `sym_frame_inv_own lo prog env as.as_code ctx cpl fn ret srest labs0 ps_l as ss`
    by simp[sym_frame_inv_canonical_own] >>
  drule_all (Q.SPEC `F` sym_block_prefix_step_exact_own) >>
  simp[sym_steps_mode_def, sym_frame_inv_canonical_own] >> strip_tac >>
  metis_tac[]
QED

Theorem sym_block_prefix_step:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised vs as s_phi clean_ops ps2 ops ps3 r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    generated_plan_state_wf_marked spill_base ps_l /\
    (!op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1 ==>
     !op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==> off < dimword (:256)) /\
    (!at. MEM at ps_l.ps_stack \/ at IN FDOM ps_l.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps_l vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = bb.bb_instructions /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan liveness cfg fn bb
            (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
     else ([], ps_l with <| ps_cleanup_height := h;
                            ps_cleanup_promised := promised |>)) =
      (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps_l as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (phi_prefix_length bb.bb_instructions)
        (non_param_insts bb) ps2 = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (phi_prefix_length bb.bb_instructions)
        (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb))
        ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  rpt gen_tac >> strip_tac >> drule_all sym_block_prefix_step_exact >>
  strip_tac >> qexistsl_tac [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`, `ss'`] >>
  gvs[] >> metis_tac[]
QED

Theorem sym_nonentry_run_rest:
  !fuel ctx fn vs bb s_phi.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis vs bb.bb_instructions = OK s_phi ==>
    run_blocks (SUC fuel) ctx fn vs =
    block_rest fuel ctx fn bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  ACCEPT_TAC sym_nonentry_run_rest_kernel
QED

Theorem sym_phi_entry_inv:
  !Inv ctx fn vs bb s_phi.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_entry_inv Inv ctx fn vs /\
    eval_phis vs bb.bb_instructions = OK s_phi ==>
    !inst. active_inst fn inst
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
      Inv ctx fn inst
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  ACCEPT_TAC sym_phi_entry_inv_kernel
QED

Theorem sym_entry_body_inv:
  !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   lbl_ctr ps_end ps0 param_ops ps1 body_ops ps_after pc_bb vs as
   Inv ra pc_ret rest mem0.
    ctx = unit.cu_context /\ lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\ generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
      MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
      MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label callee_name :: args /\
      lookup_function callee_name ctx.ctx_functions = SOME callee ==>
      fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
    (!inst. active_inst fn inst vs ==> Inv ctx fn inst vs) /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    ps0 = init_cleanup_plan_state ch growth r.sr_spill_base lbl_ctr /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      r.sr_spill_base lbl_ctr = SOME (r.sr_plan, ps_end) /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label /\
    vs.vs_current_bb = (HD fn.fn_blocks).bb_label /\
    lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks = SOME (HD fn.fn_blocks) /\
    dfs_block_state liveness dfg cfg fn ps0 (HD fn.fn_blocks).bb_label ps0 /\
    generate_block_plan liveness dfg cfg fn (HD fn.fn_blocks) ps0 =
      SOME (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops, ps_after) /\
    block_plan_state liveness dfg cfg fn (HD fn.fn_blocks) ps0
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1 /\
    generate_block_insts_plan liveness dfg cfg fn (HD fn.fn_blocks).bb_label
      (bb_is_halting (HD fn.fn_blocks))
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
      (LENGTH (HD fn.fn_blocks).bb_instructions) 0
      (non_param_insts (HD fn.fn_blocks)) ps1 = SOME (body_ops, ps_after) /\
    vs.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
    asm_block_at prog pc_bb (execute_plan cp.cp_initial_fmp
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
    as.as_pc = pc_bb + LENGTH (execute_plan cp.cp_initial_fmp
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps1 vs as /\
    (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
      operand_val (frame_view fn ra vs) lo at =
      operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) ==>
    body_inv rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth r.sr_spill_base lbl_ctr r.sr_plan ps_end (HD fn.fn_blocks)
      ps0 ps0.ps_cleanup_height ps0.ps_cleanup_promised ps0
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)
      ps_after ps_after param_ops body_ops
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1
      pc_bb vs as Inv ra pc_ret rest mem0
Proof
  rpt gen_tac >> strip_tac >> simp[body_inv_reloc_specialize] >>
  `code_labels_agree prog lo` by simp[] >>
  drule_all sym_entry_body_inv_own >> simp[]
QED

Theorem sym_nonentry_body_inv:
  !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb pred ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops ps pc0 vs s_phi as
   Inv ra pc_ret rest mem0 prefixL prefixD core.
    ctx = unit.cu_context /\ lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\ generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
      MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
      MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label callee_name :: args /\
      lookup_function callee_name ctx.ctx_functions = SOME callee ==>
      fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
    fn_entry_inv Inv ctx fn vs /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\ fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_reachable fn bb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (block_ops, ps_after) /\
    ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
    ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
    ps_after.ps_stack = prefixL ++ core /\
    ps_dfs_after.ps_stack = prefixD ++ core /\
    (!v. MEM v (live_vars_at liveness bb.bb_label (LENGTH bb.bb_instructions)) ==>
       ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD) /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
      (phi_prefix_length bb.bb_instructions) ps /\
    non_param_insts bb = bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (phi_prefix_length bb.bb_instructions)
      (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb))
      ps = SOME (rest_ops, ps_after) /\
    block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    asm_block_at prog pc0 (execute_plan cp.cp_initial_fmp block_ops) /\
    as.as_pc = pc0 + LENGTH (execute_plan cp.cp_initial_fmp
      (SOLabel bb.bb_label :: prefix_ops)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra s_phi) lo at =
      operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) ==>
    body_inv rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops
      (phi_prefix_length bb.bb_instructions) ps pc0
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      as Inv ra pc_ret rest mem0
Proof
  rpt gen_tac >> strip_tac >> simp[body_inv_reloc_specialize] >>
  `code_labels_agree prog lo` by simp[] >>
  drule_all sym_nonentry_body_inv_own >> simp[]
QED

Theorem sym_phi_error_body_result:
  !fuel ctx fn vs bb e lo o2pc prog env cp mem0 pc_ret rest srest labs0 as ss.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis vs bb.bb_instructions = Error e ==>
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as ss (run_blocks (SUC fuel) ctx fn vs)
Proof
  rpt gen_tac >> strip_tac >> drule_all sym_phi_error_run_blocks >>
  simp[sym_body_result_error]
QED

Theorem sym_entry_return_result:
  !lo o2pc prog env cp ctx fn pc_ret rest srest fuel vs as ss ra rv vs'.
    fn_entry_state_rel cp fn vs as ra rest /\
    sym_body_result lo o2pc prog env cp ctx fn as.as_memory pc_ret rest
      srest ss.sym_mem_labels as ss (run_blocks fuel ctx fn vs) /\
    run_blocks fuel ctx fn vs = IntRet rv vs' ==>
    ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = pc_ret /\ as'.as_stack = REVERSE rv.iret_values ++ rest /\
      fn_return_state_rel ctx cp fn vs' as as' /\
      sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
      ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
      (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac sym_entry_return_result_kernel >>
  gvs[sym_body_result_def] >> metis_tac[]
QED

Theorem sym_block_prefix_prepare:
  !unit cpl prog ctx i fn r liveness dfg cfg ch growth spill_base lbl_ctr
   fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after vs Inv.
    ctx = unit.cu_context /\ generate_context_plan ctx = SOME cpl /\
    unit_shape_ok unit /\ i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
    codegen_context_obligations Inv ctx cpl /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\ fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs = SOME (block_ops, ps_dfs_after)
    ==>
    ?h promised ps_after clean_ops ps2 inst_ops.
      (?prefixL prefixD core.
         ps_after.ps_stack = prefixL ++ core /\
         ps_dfs_after.ps_stack = prefixD ++ core /\
         (!v. MEM v (live_vars_at liveness bb.bb_label (LENGTH bb.bb_instructions)) ==>
            ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)) /\
      codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
      non_param_insts bb = bb.bb_instructions /\ get_params bb.bb_instructions = [] /\
      lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb
        (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
        SOME (block_ops, ps_after) /\
      ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
      ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
      (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
         clean_stack_plan liveness cfg fn bb
           (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
       else ([], ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
        (clean_ops, ps2) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
        (non_param_insts bb) ps2 = SOME (inst_ops, ps_after) /\
      block_ops = SOLabel bb.bb_label :: clean_ops ++ inst_ops /\
      generated_plan_state_wf_marked spill_base ps /\
      (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
        ~MEM op (FLAT (MAP (\inst. inst.inst_operands) (collect_phis bb.bb_instructions))) /\
        (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
        ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
      (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1 ==>
       !op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
         (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
         ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
      MEM r cpl.cp_regions /\ r.sr_fn_name = fn.fn_name /\
      r.sr_spill_base <= ps_after.ps_alloc.sa_spill_base /\
      ps_after.ps_alloc.sa_next_offset <= r.sr_spill_end /\
      (!off. MEM (SOSpill off) (clean_ops ++ inst_ops) \/
        MEM (SORestore off) (clean_ops ++ inst_ops) ==> off < dimword (:256))
Proof
  ACCEPT_TAC sym_block_prefix_prepare_kernel
QED

Theorem sym_block_step_prefix:
  !unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth spill_base
   lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after vs as Inv
   ra rest mem0 s_phi env ret srest labs0 ss.
    ctx = unit.cu_context /\ lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\ generate_context_plan ctx = SOME cpl /\
    unit_shape_ok unit /\ i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
    codegen_context_obligations Inv ctx cpl /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\ fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps /\
    vs.vs_prev_bb = SOME pred /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs = SOME (block_ops, ps_dfs_after) /\
    asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp block_ops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\ asm_static_wf prog /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
    ?h promised ps_after prefix_ops rest_ops ps1 n as1 ss1.
      (?prefixL prefixD core.
         ps_after.ps_stack = prefixL ++ core /\
         ps_dfs_after.ps_stack = prefixD ++ core /\
         (!v. MEM v (live_vars_at liveness bb.bb_label (LENGTH bb.bb_instructions)) ==>
            ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)) /\
      non_param_insts bb = bb.bb_instructions /\
      generate_block_plan liveness dfg cfg fn bb
        (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
        SOME (block_ops, ps_after) /\
      ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
      ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
      block_plan_state liveness dfg cfg fn bb
        (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
        (phi_prefix_length bb.bb_instructions) ps1 /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (phi_prefix_length bb.bb_instructions)
        (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb)) ps1 =
        SOME (rest_ops, ps_after) /\
      block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
        (SOLabel bb.bb_label :: prefix_ops)) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as1 /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        operand_val (frame_view fn ra s_phi) lo at =
        operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss1 /\
      sym_frame_inv prog env ctx cpl fn ret srest labs0 ps1 as1 ss1
Proof
  rpt gen_tac >> strip_tac >>
  `code_labels_agree prog lo` by simp[] >>
  drule label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  `sym_frame_inv_own lo prog env as.as_code ctx cpl fn ret srest labs0 ps as ss`
    by gvs[sym_frame_inv_canonical_own] >>
  drule_all (Q.SPEC `F` sym_block_step_prefix_own) >>
  simp[sym_steps_mode_def, sym_frame_inv_canonical_own] >> strip_tac >>
  qexistsl_tac [`h`, `promised`, `ps_after`, `prefix_ops`, `rest_ops`, `ps1`,
                `n`, `as1`, `ss1`] >> simp[] >> metis_tac[]
QED

(* General symbolic simulation over agreeing code labels and fixed code bytes. *)
Theorem sym_fn_sims_all_own:
  !allow_own fuel.
    gen_fn_sim_at_reloc F NONE fuel /\
    gen_fn_frame_sim_at_reloc F NONE fuel /\
    sym_fn_sim_at_own allow_own fuel /\
    sym_fn_frame_sim_at_own allow_own fuel
Proof
  gen_tac >> rewrite_tac[GSYM gen_fn_sim_at_simple_reloc_def,
                        GSYM gen_fn_frame_sim_at_simple_reloc_def] >>
  Induct
  >- (simp[gen_fn_sim_at_simple_reloc_def, gen_fn_frame_sim_at_simple_reloc_def,
           gen_fn_sim_at_reloc_def, gen_fn_frame_sim_at_reloc_def,
           sym_fn_sim_at_own_def, sym_fn_frame_sim_at_own_def] >>
      rpt strip_tac >> gvs[Once run_blocks_def]) >>
  metis_tac[fn_entry_block_step_reloc, fn_block_frame_step_reloc,
            sym_fn_entry_block_step_own, sym_fn_block_frame_step_own]
QED

Theorem sym_fn_sims_all:
  !fuel. gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel
Proof
  gen_tac >> qspecl_then [`F`, `fuel`] strip_assume_tac sym_fn_sims_all_own >>
  metis_tac[gen_fn_sim_at_reloc_specialize, gen_fn_frame_sim_at_reloc_specialize,
            gen_fn_sim_at_simple_def, gen_fn_frame_sim_at_simple_def,
            sym_fn_sim_at_own_canonical, sym_fn_frame_sim_at_own_canonical]
QED

Theorem sym_fn_entry_block_step:
  !fuel. gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_sim_at (SUC fuel)
Proof
  metis_tac[sym_fn_sims_all]
QED

Theorem sym_fn_block_frame_step:
  !fuel. gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_frame_sim_at (SUC fuel)
Proof
  metis_tac[sym_fn_sims_all]
QED
