(* Relocated function-level composition of the symbolic prefixes and body. *)
Theory symFnStepOwn
Ancestors
  symFnPrefixOwn symFrameBoundaryOwn symBlockBodyBranchOwn symBlockBody symFnSimSpec codegenSymRel
  codegenSymOwnRel fnEntryStep fnEntryPlan fnBlockStep fnBlockStepHelpers
  fnBlockBody fnBlockBodySteps fnSimSpec asmSymBridge asmSymSem frameRel
  contextCodegenRel codegenRel venomExecSemantics venomState planExec
  stackOpSim blockSimHelpers fnPlanLineageEntryProduction
Libs
  prefixContractLib

val _ = Theory.add_ML_dependency "prefixContractLib";
val _ = Parse.hide "base";
val _ = Parse.hide "body";

Theorem sym_nonentry_run_rest_kernel:
  !fuel ctx fn vs bb s_phi.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis vs bb.bb_instructions = OK s_phi ==>
    run_blocks (SUC fuel) ctx fn vs =
    block_rest fuel ctx fn bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >> simp[run_blocks_unfold, run_block_def, block_rest_def] >>
  Cases_on `exec_block fuel ctx bb
    (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]
QED

Theorem sym_phi_entry_inv_kernel:
  !Inv ctx fn vs bb s_phi.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_entry_inv Inv ctx fn vs /\
    eval_phis vs bb.bb_instructions = OK s_phi ==>
    !inst. active_inst fn inst
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
      Inv ctx fn inst
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  qpat_x_assum `fn_entry_inv _ _ _ _`
    (irule o REWRITE_RULE [fn_entry_inv_def]) >>
  simp[enters_block_def]
QED

Theorem sym_entry_body_inv_own:
  !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   lbl_ctr ps_end ps0 param_ops ps1 body_ops ps_after pc_bb vs as
   Inv ra pc_ret rest mem0.
    ctx = unit.cu_context /\ code_labels_agree prog lo /\
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
    body_inv_reloc rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth r.sr_spill_base lbl_ctr r.sr_plan ps_end (HD fn.fn_blocks)
      ps0 ps0.ps_cleanup_height ps0.ps_cleanup_promised ps0
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)
      ps_after ps_after param_ops body_ops
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1
      pc_bb vs as Inv ra pc_ret rest mem0
Proof
  rpt gen_tac >> strip_tac >> drule_all step_fn_shape >> strip_tac >>
  gvs[body_inv_reloc_def, stackPlanGenTheory.init_cleanup_plan_state_def,
      stackPlanTypesTheory.init_plan_state_def] >>
  `!xs L. ?prefixL prefixD core.
     xs = prefixL ++ core /\ xs = prefixD ++ core /\
     (!v. MEM v L ==> ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)` by
    (rpt gen_tac >> qexistsl_tac [`[]`, `[]`, `xs`] >> simp[]) >>
  rpt conj_tac >> metis_tac[entry_step_phi_bound,
    revert_forward_pair_past_params, fnPlanLineageTheory.lineage_state_rules,
    venomWfTheory.fn_reachable_def, relationTheory.RTC_REFL]
QED

Theorem sym_nonentry_body_inv_own:
  !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb pred ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops ps pc0 vs s_phi as
   Inv ra pc_ret rest mem0 prefixL prefixD core.
    ctx = unit.cu_context /\ code_labels_agree prog lo /\
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
    body_inv_reloc rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops
      (phi_prefix_length bb.bb_instructions) ps pc0
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      as Inv ra pc_ret rest mem0
Proof
  rpt gen_tac >> strip_tac >>
  `s_phi.vs_labels = vs.vs_labels /\
   s_phi.vs_call_ctx = vs.vs_call_ctx /\
   s_phi.vs_current_bb = vs.vs_current_bb` by
    (drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `!inst. active_inst fn inst
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
      Inv ctx fn inst
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[sym_phi_entry_inv_kernel] >>
  `get_params bb.bb_instructions = []` by
    (irule fnBlockBodyHelpersTheory.no_param_get_params >>
     gvs[callLayoutDefsTheory.no_param_insts_def,
         stackPlanGenTheory.non_param_insts_def, listTheory.FILTER_EQ_ID]) >>
  gvs[body_inv_reloc_def, fnBlockStepHelpersTheory.operand_val_frame_view_inst_idx] >>
  metis_tac[fnPlanLineageTheory.lineage_entry_lineage_state,
            fnBlockStepHelpersTheory.revert_forward_pair_past_phis]
QED

Theorem sym_phi_error_run_blocks:
  lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis vs bb.bb_instructions = Error e ==>
  run_blocks (SUC fuel) ctx fn vs = Error e
Proof
  simp[run_blocks_unfold, run_block_def, SF CONJ_ss]
QED

Theorem sym_phi_error_body_result_own:
  !allow_own own fuel ctx fn vs bb e lo o2pc prog env cp mem0 pc_ret rest srest labs0 as ss.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis vs bb.bb_instructions = Error e ==>
    sym_body_result_own allow_own lo o2pc prog env own cp ctx fn mem0 pc_ret rest srest labs0
      as ss (run_blocks (SUC fuel) ctx fn vs)
Proof
  rpt gen_tac >> strip_tac >> drule_all sym_phi_error_run_blocks >>
  simp[symBlockBodyResultOwnTheory.sym_body_result_error_own]
QED

(* Package the same returned state for either symbolic postcondition. *)
Theorem sym_entry_return_result_kernel:
  !P cp ctx fn vs as ra rest fuel rv vs' lo o2pc prog pc_ret.
    fn_entry_state_rel cp fn vs as ra rest /\
    run_blocks fuel ctx fn vs = IntRet rv vs' /\
    (?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = pc_ret /\ as'.as_stack = REVERSE rv.iret_values ++ rest /\
      context_memory_rel cp vs'.vs_memory as'.as_memory /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        read_byte b as'.as_memory = read_byte b as.as_memory) /\
      shared_state_rel vs' as' /\ P n as' ss') ==>
    ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = pc_ret /\ as'.as_stack = REVERSE rv.iret_values ++ rest /\
      fn_return_state_rel ctx cp fn vs' as as' /\ P n as' ss'
Proof
  rpt gen_tac >> strip_tac >> drule_all entry_step_return >>
  metis_tac[]
QED

Theorem sym_entry_return_result_own:
  !allow_own own lo o2pc prog env cp ctx fn pc_ret rest srest fuel vs as ss ra rv vs'.
    fn_entry_state_rel cp fn vs as ra rest /\
    sym_body_result_own allow_own lo o2pc prog env own cp ctx fn as.as_memory pc_ret rest
      srest ss.sym_mem_labels as ss (run_blocks fuel ctx fn vs) /\
    run_blocks fuel ctx fn vs = IntRet rv vs' ==>
    ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = pc_ret /\ as'.as_stack = REVERSE rv.iret_values ++ rest /\
      fn_return_state_rel ctx cp fn vs' as as' /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
      asm_sym_rel_own lo prog env own as' ss' /\
      ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
      (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac sym_entry_return_result_kernel >>
  gvs[sym_body_result_own_def] >> metis_tac[]
QED

Theorem sym_block_prefix_prepare_kernel:
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
  rpt gen_tac >> strip_tac >>
  drule_all step_fn_shape >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
   dfs_block_state liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_dfs` by
    metis_tac[] >>
  `canonical_param_prefix fn` by fs[stackPlanGenTheory.codegen_ready_fn_def] >>
  drule_all fnPlanPrefixTheory.nonentry_block_no_params >> strip_tac >>
  drule fnPlanPrefixTheory.codegen_ready_fn_no_marker >> strip_tac >>
  drule fnPlanLineageTheory.lineage_entry_lineage_state >> strip_tac >>
  drule_all fnPlanLineageTheory.lineage_state_block_plan >> strip_tac >>
  drule_all fnLineageStaticTheory.lineage_state_static >> strip_tac >>
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    generate_block_plan_nonentry >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all fnPlanPlaceDfsBlockTheory.dfs_block_plan_contained >> strip_tac >>
  drule_all dfs_block_alloc_bounded >> strip_tac >>
  drule_all context_region_fn_name >> simp[] >> strip_tac >>
  qexistsl_tac [`h`, `promised`, `ps_after`, `clean_ops`, `ps2`, `inst_ops`] >>
  conj_tac >- (qexistsl_tac [`prefixL`, `prefixD`, `core`] >> gvs[]) >>
  simp[] >>
  `r.sr_spill_base <= ps_after.ps_alloc.sa_spill_base /\
   ps_after.ps_alloc.sa_next_offset <= r.sr_spill_end` by (gvs[] >> decide_tac) >>
  gvs[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >> irule region_subplan_spill_offsets >>
  qexistsl_tac [`cpl`, `unit.cu_context`, `clean_ops ++ inst_ops`, `post`,
               `pre ++ [SOLabel vs.vs_current_bb]`, `EL i cpl.cp_regions`] >>
  gvs[]
QED

Theorem sym_block_step_prefix_own:
  !allow_own own unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth spill_base
   lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after vs as Inv
   ra rest mem0 s_phi env ret srest labs0 ss.
    ctx = unit.cu_context /\ code_labels_agree prog lo /\
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
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\ asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
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
      sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
      sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps1 as1 ss1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sym_block_prefix_prepare_kernel >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_assum `block_ops = _` (fn eq =>
    qpat_x_assum `asm_block_at _ _ _` (mp_tac o REWRITE_RULE [eq])) >>
  rewrite_tac[listTheory.APPEND] >>
  disch_then (mp_then (Pat `asm_block_at _ _ _`) mp_tac sym_label_block_steps_own) >>
  disch_then (drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`allow_own`, `o2pc`] strip_assume_tac) >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    sym_block_prefix_step_own >>
  disch_then (drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o REWRITE_RULE [fn_frame_inv_pc]) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_all o SIMP_RULE pure_ss [asmSemTheory.asm_state_accfupds, combinTheory.K_THM]) >>
  disch_then (qspec_then `allow_own` strip_assume_tac) >>
  qpat_assum `asm_steps _ _ _ 1 _ = _` (mp_tac o MATCH_MP asm_steps_add_ok) >>
  strip_tac >>
  qexistsl_tac [`h`, `promised`, `ps_after`, `clean_ops ++ phi_ops`,
                `body_ops`, `ps1`, `1 + n`, `as'`, `ss'`] >>
  conj_tac >- (qexistsl_tac [`prefixL`, `prefixD`, `core`] >> gvs[]) >>
  simp[execute_plan_label_length, Once sym_steps_mode_add] >>
  reverse conj_tac >- gvs[] >>
  rewrite_tac[fnBlockPlanStaticTheory.block_plan_state_def] >>
  qexistsl_tac [`[]`,
    `ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`,
    `clean_ops`, `ps2`, `phi_ops`] >> gvs[]
QED

Theorem sym_fn_entry_block_step_own:
  !allow_own fuel. gen_fn_sim_at_simple_reloc fuel /\ gen_fn_frame_sim_at_simple_reloc fuel /\
         sym_fn_sim_at_own allow_own fuel /\ sym_fn_frame_sim_at_own allow_own fuel ==>
         sym_fn_sim_at_own allow_own (SUC fuel)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[sym_fn_sim_at_own_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all step_fn_shape >> strip_tac >>
  drule_all region_fn_plan >> strip_tac >>
  drule_all entry_block_plan >> strip_tac >>
  rename1 `generate_context_plan ctx = SOME cplan` >>
  `asm_block_at prog as.as_pc (execute_plan cplan.cp_initial_fmp
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
   asm_block_at prog as.as_pc (execute_plan cplan.cp_initial_fmp
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))` by
    (qpat_x_assum `asm_block_at _ _ (execute_plan _ r.sr_plan)` mp_tac >>
     qpat_assum `r.sr_plan = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[execute_plan_append, asm_block_at_append] >>
     rpt strip_tac >> fs[]) >>
  `!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)` by
    (rpt strip_tac >> irule region_subplan_spill_offsets >>
     qexistsl_tac [`cplan`, `ctx`, `param_ops`, `body_ops ++ rest_ops`,
                   `[SOLabel (HD fn.fn_blocks).bb_label]`, `r`] >> simp[]) >>
  `label_flow_own_ok ctx` by
    (Cases_on `allow_own` >> fs[label_flow_ok_imp_label_flow_own_ok]) >>
  prefix_contract_tac SRULE
    (drule_at (Pat `prepare_params_plan _ _ _ = _`))
    [`ch` |-> `cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
       (fcg_analyze ctx) fn.fn_name`,
     `growth` |-> `cleanup_growth_table ctx (fcg_analyze ctx)`,
     `spill_base` |-> `r.sr_spill_base`, `lbl_ctr` |-> `lbl_ctr`]
    [] sym_entry_prefix_frame_sim_own >>
  disch_then (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_entry_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `MEM _ _.cp_regions`)) >>
  disch_then (drule_at (Pat `_.sym_stack = _`)) >> simp[] >>
  suspend "entry_prefix"
QED

Resume sym_fn_entry_block_step_own[entry_prefix]:
  disch_then (qspecl_then [`lbl_ctr`, `fuel`, `allow_own`] mp_tac) >>
  (impl_tac >- metis_tac[listTheory.MEM_EL, unitShapeDefsTheory.unit_shape_ok_def,
                         listTheory.EVERY_MEM]) >>
  strip_tac >>
  drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`) sym_entry_body_inv_own >>
  disch_then (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >>
  qpat_x_assum `ctx = unit.cu_context` SUBST_ALL_TAC >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  disch_then (qspecl_then [`i`, `as.as_pc`, `pc_ret`] mp_tac) >>
  (impl_tac >- (simp[Once arithmeticTheory.ADD_COMM] >>
                fs[fn_entry_state_rel_def] >> metis_tac[])) >>
  strip_tac >> suspend "entry_body"
QED

Resume sym_fn_entry_block_step_own[entry_body]:
  `asm_data_env_lo_ok lo prog env own /\ vs_p.vs_code = own` by
    (qpat_assum `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [sym_frame_inv_own_def, asm_sym_rel_own_def]) >>
     fs[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def]) >>
  drule_all symBlockBodyResultOwnTheory.sym_block_body_frame_sim_own >> strip_tac >>
  drule_all symBlockBodyResultOwnTheory.sym_body_result_prefix_own >> strip_tac >>
  `run_blocks (SUC fuel) unit.cu_context fn vs =
   block_rest fuel unit.cu_context fn (HD fn.fn_blocks) vs_p` by
    (irule entry_step_run_rest >> metis_tac[exec_block_def]) >>
  reverse (rpt conj_tac)
  >- (rpt gen_tac >> strip_tac >> irule sym_entry_return_result_own >> metis_tac[]) >>
  fs[sym_body_result_own_def]
QED

Finalise sym_fn_entry_block_step_own

Theorem sym_fn_block_frame_step_own:
  !allow_own fuel. gen_fn_sim_at_simple_reloc fuel /\ gen_fn_frame_sim_at_simple_reloc fuel /\
         sym_fn_sim_at_own allow_own fuel /\ sym_fn_frame_sim_at_own allow_own fuel ==>
         sym_fn_frame_sim_at_own allow_own (SUC fuel)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[sym_fn_frame_sim_at_own_def] >>
  rpt gen_tac >> strip_tac >>
  qspecl_then [`vs`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- suspend "frame_prefix"
  >> simp[run_blocks_unfold, run_block_def]
QED

Resume sym_fn_block_frame_step_own[frame_prefix]:
  `MEM fn ctx.ctx_functions /\ fn_shape_ok fn` by
    metis_tac[listTheory.MEM_EL, unitShapeDefsTheory.unit_shape_ok_def,
              listTheory.EVERY_MEM] >>
  `label_flow_own_ok ctx` by
    (Cases_on `allow_own` >> fs[label_flow_ok_imp_label_flow_own_ok]) >>
  drule_all sym_block_step_prefix_own >>
  disch_then (qspec_then `allow_own` strip_assume_tac) >>
  drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `dfs_block_state liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_dfs` by
    metis_tac[] >>
  drule_all sym_nonentry_body_inv_own >> strip_tac >>
  suspend "frame_body"
QED

Resume sym_fn_block_frame_step_own[frame_body]:
  rename1 `eval_phis vs bb.bb_instructions = OK s_phi` >>
  `asm_data_env_lo_ok lo prog env own /\
   (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_code = own` by
    (qpat_assum `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ ps1 _ _`
       (strip_assume_tac o REWRITE_RULE [sym_frame_inv_own_def, asm_sym_rel_own_def]) >>
     fs[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def]) >>
  drule_all symBlockBodyResultOwnTheory.sym_block_body_frame_sim_own >> strip_tac >>
  drule_all symBlockBodyResultOwnTheory.sym_body_result_prefix_own >> strip_tac >>
  drule_all sym_nonentry_run_rest_kernel >>
  disch_then (fn th => rewrite_tac[th]) >> fs[sym_body_result_own_def]
QED

Finalise sym_fn_block_frame_step_own
