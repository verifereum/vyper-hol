Theory staticAbortGeneratedStaticCut
Ancestors
  fnStaticAbortBoundary codegenSymRel staticAbortGeneratedStaticEdge
  fnBlockBodyHelpers fnPlanPrefix venomWf unitShapeDefs rich_list
  contextStaticAbortRel stackPlanGen list venomInst venomExecProps
  fnBlockPlanStatic staticAbortDefs planExec stackOpSim fnBlockBodySteps

Theorem generated_static_cut_interval_reloc:
  body_inv_abort_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 cvs cut Inv
    ra pc_ret rest mem0 /\
  (!f inst l.
    MEM f ctx.ctx_functions /\ MEM inst (fn_insts f) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (row_lo:string |-> num) l)) /\
  in_static_abort_prefix fn cvs ==>
  ?j ops qs.
    generate_context_plan unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ bb.bb_label = bb.bb_label /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops,ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (block_ops,ps_after) /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) k ps /\
    phi_prefix_length bb.bb_instructions <= k /\
    LENGTH (get_params bb.bb_instructions) <= k /\
    non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
    EVERY inst_shape_ok bb.bb_instructions /\ EVERY codegen_ready_inst bb.bb_instructions /\
    static_abort_pair bb k j /\
    generate_block_insts_prefix liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions)) (SUC j - k)
      (DROP k bb.bb_instructions) ps = SOME (ops,qs) /\
    (!q inst l. k <= q /\ q <= j /\ get_instruction bb q = SOME inst /\
       MEM (Label l) (compute_operands inst) ==>
       IS_SOME (FLOOKUP row_lo l)) /\
    asm_block_at prog cut.as_pc (execute_plan cpl.cp_initial_fmp ops) /\
    cut.as_call_ctx.cc_static /\ LENGTH cut.as_stack = LENGTH ps.ps_stack + LENGTH rest /\
    cut.as_call_ctx = cvs.vs_call_ctx /\ cut.as_requests = cvs.vs_requests
Proof
  pure_rewrite_tac[body_inv_abort_reloc_def] >> strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[EL_MEM] >>
  `codegen_ready_fn fn` by
    (fs[codegen_context_obligations_abort_def, codegen_ready_def, EVERY_MEM]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = cvs.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed bb` by fs[codegen_ready_fn_def, wf_function_def] >>
  `EVERY codegen_ready_inst bb.bb_instructions` by
    (fs[codegen_ready_fn_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (fs[unit_shape_ok_def, EVERY_MEM, fn_shape_ok_def] >>
     metis_tac[MEM_fn_insts_blocks, fn_insts_def]) >>
  `non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions))
                                   bb.bb_instructions` by
    metis_tac[non_param_insts_drop, codegen_ready_fn_def] >>
  `LENGTH (get_params bb.bb_instructions) <= k` by fs[block_plan_state_def] >>
  `cvs.vs_call_ctx.cc_static /\ static_abort_at bb k` by
    gvs[in_static_abort_prefix_def] >>
  `?j. static_abort_pair bb k j` by metis_tac[static_abort_at_def] >>
  `k <= j /\ j < LENGTH bb.bb_instructions` by fs[static_abort_pair_def] >>
  `DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb) =
   DROP k bb.bb_instructions` by simp[rich_listTheory.DROP_DROP_T] >>
  `?ops qs post.
    generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions)) (SUC j - k)
      (DROP k bb.bb_instructions) ps = SOME (ops, qs) /\
    rest_ops = ops ++ post` by
    (`SUC j - k <= LENGTH (DROP k bb.bb_instructions)` by
       (simp[] >> decide_tac) >>
     qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[] >> qpat_x_assum `SUC j - k <= LENGTH (DROP k _)` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[generate_block_insts_plan_split]) >>
  `asm_block_at prog cut.as_pc (execute_plan cpl.cp_initial_fmp ops)` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     gvs[execute_plan_append, execute_plan_def, asm_block_at_append, APPEND_ASSOC]) >>
  `!q inst l. k <= q /\ q <= j /\ get_instruction bb q = SOME inst /\
       MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP row_lo l)` by
    (rpt strip_tac >>
     `q < LENGTH bb.bb_instructions /\ EL q bb.bb_instructions = inst` by
       gvs[get_instruction_def] >>
     `inst.inst_opcode <> PHI` by
       (qpat_x_assum `EL q _ = inst` (SUBST1_TAC o SYM) >>
        irule phi_prefix_not_phi >> fs[bb_well_formed_def] >> first_assum ACCEPT_TAC) >>
     `MEM inst (fn_insts fn)` by
       (simp[fn_insts_def] >> irule MEM_fn_insts_blocks >>
        qexists `bb` >> simp[] >> metis_tac[EL_MEM]) >> metis_tac[]) >>
  drule static_abort_frame_cut >> strip_tac >>
  qexistsl [`j`, `ops`, `qs`] >> simp[] >> metis_tac[]
QED

Theorem generated_static_cut_interval:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 cvs cut Inv
    ra pc_ret rest mem0 /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps cut sc /\
  label_flow_ok ctx /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  in_static_abort_prefix fn cvs ==>
  ?j ops qs.
    generate_context_plan unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ bb.bb_label = bb.bb_label /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops,ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (block_ops,ps_after) /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) k ps /\
    phi_prefix_length bb.bb_instructions <= k /\
    LENGTH (get_params bb.bb_instructions) <= k /\
    non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
    EVERY inst_shape_ok bb.bb_instructions /\ EVERY codegen_ready_inst bb.bb_instructions /\
    static_abort_pair bb k j /\
    generate_block_insts_prefix liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions)) (SUC j - k)
      (DROP k bb.bb_instructions) ps = SOME (ops,qs) /\
    (!q inst l. k <= q /\ q <= j /\ get_instruction bb q = SOME inst /\
       MEM (Label l) (compute_operands inst) ==>
       IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    asm_block_at prog cut.as_pc (execute_plan cpl.cp_initial_fmp ops) /\
    cut.as_call_ctx.cc_static /\ LENGTH cut.as_stack = LENGTH ps.ps_stack + LENGTH rest /\
    cut.as_call_ctx = cvs.vs_call_ctx /\ cut.as_requests = cvs.vs_requests
Proof
  pure_rewrite_tac[body_inv_abort_reloc_canonical] >> strip_tac >>
  `!f inst l.
    MEM f ctx.ctx_functions /\ MEM inst (fn_insts f) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (qpat_assum `lo = SND (compute_label_offsets prog)` (SUBST1_TAC o SYM) >>
     qhdtm_assum `body_inv_abort_reloc`
       (ACCEPT_TAC o cj 14 o REWRITE_RULE [body_inv_abort_reloc_def])) >>
  irule generated_static_cut_interval_reloc >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
