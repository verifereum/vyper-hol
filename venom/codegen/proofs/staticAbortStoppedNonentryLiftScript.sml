Theory staticAbortStoppedNonentryLift
Ancestors
  symFnStep fnStaticAbortBoundary contextStaticAbortRel fnBlockStepHelpers
  fnPlanLineage venomExecProofs venomExecSemantics unitShapeDefs symFnSimSpec
  contextCodegenRel list

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

(* The let-bound observation is just notation, shared by the body hypothesis
   and the nonentry conclusion. In particular its return clause is the full
   nonentry clause, not the weaker function-entry return relation. *)
Theorem stopped_nonentry_lift:
  !fuel.
  let R = (\rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest
              srest labs0 ast ss res.
    (!vs'. res = Halt vs' ==>
      ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
        venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. res = Abort a vs' ==>
      (?n out. (asm_steps lo o2pc prog n ast = AsmRevert out \/
                asm_steps lo o2pc prog n ast = AsmFault out) /\
        sym_terminal (sym_steps prog env n ss) /\ out.as_requests <<= vs'.vs_requests) \/
      (?nc cut sc iC fnC rC livC dfgC cfgC chC growthC spillC ctrC fnopsC endC
        bbC pslC hC promisedC dfsC blockC dfsafterC afterC prefixC restopsC kC
        psC pcC cvsC raC pcretC restC memC retC srestC labsC.
        asm_steps lo o2pc prog nc ast = AsmOK cut /\
        sym_steps prog env nc ss = SymOK sc /\
        body_inv_abort rpolicy unit cpl prog ctx lo o2pc iC fnC rC livC dfgC cfgC
          chC growthC spillC ctrC fnopsC endC bbC pslC hC promisedC dfsC blockC
          dfsafterC afterC prefixC restopsC kC psC pcC cvsC cut Inv
          raC pcretC restC memC /\
        sym_frame_inv prog env ctx cpl fnC retC srestC labsC psC cut sc /\
        (in_static_abort_prefix fnC cvsC \/ in_revert_forward fnC cvsC) /\
        cut.as_requests = vs'.vs_requests)) /\
    (!rv vs'. res = IntRet rv vs' ==>
      ?n out sout. asm_steps lo o2pc prog n ast = AsmOK out /\
        out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
        context_memory_rel cpl vs'.vs_memory out.as_memory /\
        (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
          read_byte b out.as_memory = read_byte b mem0) /\
        shared_state_rel vs' out /\
        sym_steps prog env n ss = SymOK sout /\ asm_sym_rel prog env out sout /\
        sout.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
        (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
          FLOOKUP sout.sym_mem_labels b = FLOOKUP labs0 b) /\
        (!b. b IN FDOM sout.sym_mem_labels ==> context_spill_byte cpl b)))
  in
  (!rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
    spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv ra pc_ret rest
    mem0 env ret srest labs0 ss.
    body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0
      ast ss (block_rest fuel ctx fn bb vs)) ==>
  !rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
    spill_base lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after
    vs ast Inv ra pc_ret rest mem0 env ret srest labs0 ss.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
    EL i cpl.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
      MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
      MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label callee_name :: args /\
      lookup_function callee_name ctx.ctx_functions = SOME callee ==>
      fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations_abort Inv ctx cpl /\
    (!f inst l. MEM f ctx.ctx_functions /\ MEM inst (fn_insts f) /\
      inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP lo l)) /\
    reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn vs /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\ spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\ fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps /\
    vs.vs_prev_bb = SOME pred /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs = SOME (block_ops, ps_dfs_after) /\
    asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp block_ops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs ast /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra vs) lo at =
      operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    label_flow_ok ctx /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0
      ast ss (run_blocks (SUC fuel) ctx fn vs)
Proof
  gen_tac >> qmatch_goalsub_abbrev_tac `LET _ R` >>
  rewrite_tac[LET_THM] >> BETA_TAC >> disch_tac >> rpt gen_tac >> strip_tac >>
  qspecl_then [`vs`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- suspend "phis_ok"
  >> simp[Abbr `R`, run_blocks_unfold, run_block_def]
QED

Resume stopped_nonentry_lift[phis_ok]:
  `codegen_context_obligations (\c f i s. F) ctx cpl` by
    fs[codegen_context_obligations_abort_def, codegen_context_obligations_def,
       codegen_memory_obligations_def] >>
  `MEM fn ctx.ctx_functions /\ fn_shape_ok fn` by
    metis_tac[MEM_EL, unit_shape_ok_def, EVERY_MEM] >>
  drule_all sym_block_step_prefix >> strip_tac >>
  `s'.vs_labels = vs.vs_labels /\ s'.vs_call_ctx = vs.vs_call_ctx /\
   s'.vs_current_bb = vs.vs_current_bb` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `!inst. active_inst fn inst
      (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
      Inv ctx fn inst
        (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (rpt strip_tac >>
     qpat_x_assum `fn_entry_inv _ _ _ _` (irule o REWRITE_RULE [fn_entry_inv_def]) >>
     simp[enters_block_def]) >>
  drule lineage_entry_lineage_state >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `get_params bb.bb_instructions = []` by
    (irule fnBlockBodyHelpersTheory.no_param_get_params >>
     gvs[callLayoutDefsTheory.no_param_insts_def,
         stackPlanGenTheory.non_param_insts_def, FILTER_EQ_ID]) >>
  `body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops
    (phi_prefix_length bb.bb_instructions) ps1 ast.as_pc
    (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions) as1 Inv
    ra pc_ret rest mem0` by
    (simp[NoAsms, body_inv_abort_def] >>
     gvs[operand_val_frame_view_inst_idx] >>
     rpt conj_tac >> FIRST_PROVE
       [first_assum ACCEPT_TAC, metis_tac[revert_forward_pair_past_phis]]) >>
  qpat_x_assum `!rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv ra pc_ret rest mem0 env ret srest labs0 ss. _`
    (drule_at (Pat `body_inv_abort`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >>
  (impl_tac >- simp[]) >> disch_tac >>
  drule_all sym_nonentry_run_rest >>
  disch_then (qspecl_then [`fuel`, `ctx`] SUBST1_TAC) >>
  `!m. asm_steps lo o2pc prog (n + m) ast = asm_steps lo o2pc prog m as1` by
    metis_tac[stackOpSimTheory.asm_steps_add_ok] >>
  `!m. sym_steps prog env (n + m) ss = sym_steps prog env m ss1` by
    simp[codegenSymRelTheory.sym_steps_add] >>
  qpat_x_assum `R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ as1 ss1 _` mp_tac >>
  simp[Abbr `R`] >> strip_tac >> gvs[] >>
  conj_tac >- suspend "halt" >>
  conj_tac >- suspend "abort" >>
  suspend "return"
QED

Resume stopped_nonentry_lift[halt]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!vs'. _ = Halt vs' ==> _` drule >> strip_tac >>
  qexistsl_tac [`n' + n`, `out`] >> simp[]
QED

Resume stopped_nonentry_lift[return]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!rv vs'. _ = IntRet rv vs' ==> _` drule >> strip_tac >>
  qexistsl_tac [`n' + n`, `out`, `sout`] >> simp[]
QED

Resume stopped_nonentry_lift[abort]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!a vs'. _ = Abort a vs' ==> _` drule >>
  disch_then DISJ_CASES_TAC
  >- (disj1_tac >> pop_assum strip_assume_tac >>
      qexistsl_tac [`n' + n`, `out`] >> simp[]) >>
  disj2_tac >> pop_assum strip_assume_tac >>
  qexists_tac `nc + n` >>
  goal_assum (drule_at (Pat `body_inv_abort`)) >>
  goal_assum (drule_at (Pat `sym_frame_inv`)) >> simp[]
QED

Finalise stopped_nonentry_lift
