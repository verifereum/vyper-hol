Theory staticAbortStoppedBodyTerminator
Ancestors
  staticAbortProtectedTerminal fnFrameSymbolicPrefix fnStaticAbortBodyFacts
  fnBlockBodyClasses fnBlockBody fnBlockBodySteps fnStaticAbortBoundary symBlockBody
  stackPlanGen stepWriteFootprintForward
  contextCodegenRel contextCodegenRelProps contextStaticAbortRel codegenSymRel
  venomExecProps venomExecSemantics venomInst unitShapeDefs list rich_list

val _ = Parse.hide "cp";

(* A and R are the exact stopped observations, shared lexically only. *)
Theorem stopped_body_terminator_case:
  !A. A = (\rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs'.
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
       cut.as_requests = vs'.vs_requests)) ==>
  !R. R = (\rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss res.
    (!vs'. res = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. res = Abort a vs' ==> A rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs') /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         context_memory_rel cpl vs'.vs_memory out.as_memory /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           read_byte b out.as_memory = read_byte b mem0) /\
         shared_state_rel vs' out /\ sym_steps prog env n ss = SymOK ss' /\
         asm_sym_rel prog env out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) ==>
  ((!rpolicy unit cpl prog ctx lo o2pc Inv env ast amid ss smid n vs'.
      asm_steps lo o2pc prog n ast = AsmOK amid /\
      sym_steps prog env n ss = SymOK smid /\
      A rpolicy unit cpl prog ctx lo o2pc Inv env amid smid vs' ==>
      A rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs') /\
   (!rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0
     ast amid ss smid n res.
      asm_steps lo o2pc prog n ast = AsmOK amid /\
      sym_steps prog env n ss = SymOK smid /\
      R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 amid smid res ==>
      R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss res)) /\
  (!rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
    spill_base lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after
    vs ast Inv ra pc_ret rest mem0 env ret srest labs0 ss.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
    EL i cpl.cp_regions = r /\ MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
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
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\ ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
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
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss
      (run_blocks fuel ctx fn vs)) ==>
  !rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv ra pc_ret
   rest mem0 env ret srest labs0 ss inst.
    body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss /\
    ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ is_terminator inst.inst_opcode ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss
      (block_rest fuel ctx fn bb vs)
Proof
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  disch_then (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (mk_asm "AP") (mk_asm "RP")) (mk_asm "F")) >>
  rpt gen_tac >> strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by
    (fs[body_inv_abort_def, get_instruction_def]) >>
  `inst.inst_opcode <> RETURNDATACOPY` by
    ((qpat_assum `is_terminator inst.inst_opcode` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[is_terminator_def] >>
     rpt strip_tac >> gvs[] >> (gvs[is_terminator_def]))) >>
  `(!j. ~revert_forward_pair bb k j) /\ LENGTH (compute_operands inst) <= 16` by
    (conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `revert_forward_pair bb k j` mp_tac >>
         simp[revert_forward_pair_def, get_instruction_def] >> metis_tac[]) >>
     fs[codegen_ready_inst_def]) >>
  Cases_on `step_inst fuel ctx inst vs`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "return"
  >> suspend "error"
QED

Resume stopped_body_terminator_case[ok]:
  rename1 `step_inst fuel ctx inst vs = OK vs1` >>
  `ctx = unit.cu_context` by fs[body_inv_abort_def] >>
  `focus_s7_symbolic_context unit prog` by
    (rewrite_tac[focus_s7_symbolic_context_def] >>
     qpat_assum `ctx = unit.cu_context` (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ` by
    (drule_all fnBlockBodyHelpersTheory.step_ok_terminator_jump >>
     qpat_assum `inst_shape_ok inst` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[inst_shape_ok_def] >> metis_tac[]) >>
  `?target n ast1 off ss1.
    0 < n /\ vs1 = jump_to target vs /\ MEM target (get_successors inst) /\
    asm_steps lo o2pc prog n ast = AsmOK ast1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 ast1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo target = SOME off /\ FLOOKUP o2pc off = SOME ast1.as_pc /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after ast1 ss1` by
    (Cases_on `inst.inst_opcode = JMP`
     >- (drule_all body_plan_symbolic_jmp_step >> simp[]) >>
     `inst.inst_opcode = JNZ` by fs[] >>
     drule_all body_plan_symbolic_jnz_step >> simp[]) >>
  drule_all body_plan_jump_entry >> strip_tac >>
  `~vs1.vs_halted` by fs[frameRelTheory.fn_frame_inv_def] >>
  `Inv ctx fn inst vs` by
    (qhdtm_assum `body_inv_abort`
       (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
     first_x_assum irule >> simp[]) >>
  `fn_entry_inv Inv ctx fn vs1` by
    (qhdtm_assum `body_inv_abort`
       (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
     rw[fn_entry_inv_def] >> drule_all reachability_closed_block >> simp[]) >>
  qmatch_asmsub_abbrev_tac `lineage_entry _ _ _ _ _ _ _ pe` >>
  `sym_frame_inv prog env ctx cpl fn ret srest labs0 pe ast1 ss1` by
    (irule sym_frame_inv_plan_transport >>
     goal_assum (drule_at Any) >> simp[Abbr `pe`]) >>
  `vs1.vs_labels = vs.vs_labels /\ vs1.vs_prev_bb = SOME bb.bb_label /\
   vs1.vs_current_bb = target` by simp[venomStateTheory.jump_to_def] >>
  qpat_x_assum `vs1 = jump_to target vs` kall_tac >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  qpat_x_assum `ctx = unit.cu_context` SUBST_ALL_TAC >>
  `R rpolicy unit cpl prog unit.cu_context lo o2pc Inv env fn mem0 pc_ret
     rest srest labs0 ast1 ss1 (run_blocks fuel unit.cu_context fn vs1)` by
    (asm "F" irule >>
     goal_assum (drule_at Any) >>
     qpat_assum `sym_frame_inv _ _ _ _ _ _ _ _ pe _ _` (irule_at Any) >>
     qpat_assum `generate_block_plan _ _ _ _ tbb _ = _` (irule_at Any) >>
     qpat_assum `tbb.bb_label = target` (fn th => rewrite_tac[th]) >>
     qpat_assum `lineage_entry _ _ _ _ _ _ _ pe` (irule_at Any) >>
     qpat_assum `fn_frame_inv _ _ _ _ _ _ _ pe vs1 ast1` (irule_at Any) >>
     qpat_assum `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _`
       (irule_at Any) >>
     qpat_assum `EL i cpl.cp_regions = r` (irule_at Any) >>
     qpat_assum `vs1.vs_current_bb = target` (fn th => rewrite_tac[th]) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (simp[Abbr `pe`, NoAsms] >> first_assum ACCEPT_TAC), simp[]]) >>
  drule_all block_rest_jump >> disch_then (qspec_then `fn` SUBST1_TAC) >>
  asm "RP" irule >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED
Resume stopped_body_terminator_case[error]:
  (* drule_all left the non-OK side condition unresolved. *)
  drule block_rest_other >> disch_then drule >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `fn` SUBST1_TAC) >> simp[Abbr `R`]
QED
Resume stopped_body_terminator_case[halt]:
  (* drule_all left the non-OK side condition unresolved. *)
  drule block_rest_other >> disch_then drule >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `fn` SUBST1_TAC) >>
  drule_all sym_abort_protected_halt_step >>
  simp[sym_body_result_def, Abbr `R`]
QED
Resume stopped_body_terminator_case[abort]:
  (* drule_all left the non-OK side condition unresolved. *)
  drule block_rest_other >> disch_then drule >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `fn` SUBST1_TAC) >>
  drule_all sym_abort_protected_abort_step >>
  asm_x "AP" kall_tac >> asm_x "RP" kall_tac >> asm_x "F" kall_tac >>
  simp[sym_body_result_def, Abbr `R`, Abbr `A`] >> strip_tac >>
  disj1_tac >> goal_assum (drule_at Any) >>
  fs[codegenRelTheory.venom_asm_terminal_rel_def]
QED
Resume stopped_body_terminator_case[return]:
  (* drule_all left the non-OK side condition unresolved. *)
  drule block_rest_other >> disch_then drule >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `fn` SUBST1_TAC) >>
  drule_all sym_abort_protected_ret_step >>
  simp[sym_body_result_def, Abbr `R`]
QED

Finalise stopped_body_terminator_case
