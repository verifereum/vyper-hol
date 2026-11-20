Theory staticAbortStoppedEntryLift
Ancestors
  staticAbortStoppedInvokeCut symFrameBoundary fnEntryPlan fnEntryStep
  fnEntryParams fnBlockStepHelpers fnStaticAbortBoundary symFnStep
  fnPlanPlaceFnRegion fnPlanLineage contextStaticAbortRel unitShapeDefs
  venomExecProps venomExecSemantics venomWf relation list rich_list
  contextCodegenRel frameRel stackOpSim stackPlanGen codegenSymRel
  symFrameBoundaryOwn symFrameBoundaryPairing asmSymOwnStep fnPlanPlaceRevertPostamble
  codegenSymOwnRel

val _ = Parse.hide "cp";

(* Conditional on the stopped body statement, not on an ordinary recursive
   simulation.  Normal observations are the full symbolic body observations. *)
Theorem stopped_entry_lift_mode:
  !allow_own own.
  (!rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
    spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv ra pc_ret
    rest mem0 env ret srest labs0 ss.
    (if allow_own then body_inv_abort_reloc else body_inv_abort) rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env) ctx cpl fn ret srest labs0 ps ast ss ==>
    (!vs'. block_rest fuel ctx fn bb vs = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. block_rest fuel ctx fn bb vs = Abort a vs' ==>
       (?n out. (asm_steps lo o2pc prog n ast = AsmRevert out \/
                 asm_steps lo o2pc prog n ast = AsmFault out) /\
          sym_terminal (sym_steps_mode allow_own prog env own n ss) /\ out.as_requests <<= vs'.vs_requests) \/
       (?nc cut sc iC fnC rC livC dfgC cfgC chC growthC spillC ctrC fnopsC endC
         bbC pslC hC promisedC dfsC blockC dfsafterC afterC prefixC restopsC kC
         psC pcC cvsC raC pcretC restC memC retC srestC labsC.
          asm_steps lo o2pc prog nc ast = AsmOK cut /\
          sym_steps_mode allow_own prog env own nc ss = SymOK sc /\
          (if allow_own then body_inv_abort_reloc else body_inv_abort) rpolicy unit cpl prog ctx lo o2pc iC fnC rC livC dfgC cfgC
            chC growthC spillC ctrC fnopsC endC bbC pslC hC promisedC dfsC blockC
            dfsafterC afterC prefixC restopsC kC psC pcC cvsC cut Inv
            raC pcretC restC memC /\
          (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env) ctx cpl fnC retC srestC labsC psC cut sc /\
          (in_static_abort_prefix fnC cvsC \/ in_revert_forward fnC cvsC) /\
          cut.as_requests = vs'.vs_requests)) /\
    (!rv vs'. block_rest fuel ctx fn bb vs = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         context_memory_rel cpl vs'.vs_memory out.as_memory /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           read_byte b out.as_memory = read_byte b mem0) /\
         shared_state_rel vs' out /\
         sym_steps_mode allow_own prog env own n ss = SymOK ss' /\ (if allow_own then asm_sym_rel_own lo prog env own else asm_sym_rel prog env) out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) ==>
  !rpolicy unit cpl prog ctx lo o2pc i r fn vs ast Inv ra pc_ret rest
    env ret srest ss.
    ctx = unit.cu_context /\
    (if allow_own then code_labels_agree prog lo else lo = SND (compute_label_offsets prog)) /\ o2pc = build_offset_to_pc prog /\
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
    asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp r.sr_plan) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cpl fn vs ast ra rest /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    (if allow_own then asm_sym_rel_own lo prog env own else asm_sym_rel prog env) ast ss /\
    ss.sym_stack = (if fn_has_retpc fn then [Lab ret 0] else []) ++
      MAP Val (REVERSE vs.vs_params) ++ srest /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cpl b) ==>
    (!vs'. run_blocks (SUC fuel) ctx fn vs = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. run_blocks (SUC fuel) ctx fn vs = Abort a vs' ==>
       (?n out. (asm_steps lo o2pc prog n ast = AsmRevert out \/
                 asm_steps lo o2pc prog n ast = AsmFault out) /\
          sym_terminal (sym_steps_mode allow_own prog env own n ss) /\ out.as_requests <<= vs'.vs_requests) \/
       (?nc cut sc iC fnC rC livC dfgC cfgC chC growthC spillC ctrC fnopsC endC
         bbC pslC hC promisedC dfsC blockC dfsafterC afterC prefixC restopsC kC
         psC pcC cvsC raC pcretC restC memC retC srestC labsC.
          asm_steps lo o2pc prog nc ast = AsmOK cut /\
          sym_steps_mode allow_own prog env own nc ss = SymOK sc /\
          (if allow_own then body_inv_abort_reloc else body_inv_abort) rpolicy unit cpl prog ctx lo o2pc iC fnC rC livC dfgC cfgC
            chC growthC spillC ctrC fnopsC endC bbC pslC hC promisedC dfsC blockC
            dfsafterC afterC prefixC restopsC kC psC pcC cvsC cut Inv
            raC pcretC restC memC /\
          (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env) ctx cpl fnC retC srestC labsC psC cut sc /\
          (in_static_abort_prefix fnC cvsC \/ in_revert_forward fnC cvsC) /\
          cut.as_requests = vs'.vs_requests)) /\
    (!rv vs'. run_blocks (SUC fuel) ctx fn vs = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         fn_return_state_rel ctx cpl fn vs' ast out /\
         sym_steps_mode allow_own prog env own n ss = SymOK ss' /\ (if allow_own then asm_sym_rel_own lo prog env own else asm_sym_rel prog env) out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))
Proof
  ntac 2 gen_tac >> disch_then (mk_asm "body") >> rpt gen_tac >> strip_tac >>
  `codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\ fn_shape_ok fn /\
   MEM fn ctx.ctx_functions` by
    (fs[unit_shape_ok_def, codegen_context_obligations_abort_def,
        codegen_ready_def, EVERY_EL, fn_shape_ok_def] >> gvs[EL_MEM]) >>
  drule_all region_fn_plan >> strip_tac >>
  drule_all entry_block_plan >> strip_tac >>
  `!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)` by
    (rpt strip_tac >> irule region_subplan_spill_offsets >>
     qrefinel [`_`, `_`, `param_ops`, `body_ops ++ rest_ops`,
                `[SOLabel (HD fn.fn_blocks).bb_label]`, `_`] >>
     qexistsl_tac [`cpl`, `ctx`, `r`] >> simp[APPEND_ASSOC]) >>
  `asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
   asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))` by
    (qpat_x_assum `asm_block_at _ _ (execute_plan _ r.sr_plan)` mp_tac >>
     qpat_assum `r.sr_plan = _` (fn th => rewrite_tac[th]) >>
     simp[execute_plan_append, asm_block_at_append]) >>
  `ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  `r.sr_spill_base <= r.sr_spill_base` by simp[] >>
  `code_labels_agree prog lo /\ label_flow_own_ok ctx` by
    (Cases_on `allow_own` >>
     gvs[code_labels_agree_refl, label_flow_ok_imp_label_flow_own_ok]) >>
  qabbrev_tac `fixed = if allow_own then own else ast.as_code` >>
  `asm_sym_rel_own lo prog env fixed ast ss` by
    (Cases_on `allow_own` >> gvs[Abbr `fixed`, asm_sym_rel_own_canonical]) >>
  drule_all (SRULE [] (Q.SPECL [`allow_own`, `fixed`]
    symFrameBoundaryOwnTheory.sym_entry_prefix_frame_sim_own)) >>
  disch_then (qspecl_then [`allow_own`, `fuel`] strip_assume_tac) >>
  `sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
   (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env)
     ctx cpl fn ret srest ss.sym_mem_labels ps1 as' ss'` by
    (Cases_on `allow_own` >>
     gvs[Abbr `fixed`, sym_steps_mode_def, sym_frame_inv_canonical_own]) >>
  `run_blocks (SUC fuel) ctx fn vs =
   block_rest fuel ctx fn (HD fn.fn_blocks) vs_p` by
    (asm_x "body" kall_tac >> irule entry_step_run_rest >> metis_tac[exec_block_def]) >>
  `fn_reachable fn (HD fn.fn_blocks).bb_label` by
    (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  qmatch_asmsub_abbrev_tac `dfs_block_state _ _ _ _ ps0 _ ps0` >>
  `lineage_state (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
     ps0 (HD fn.fn_blocks).bb_label ps0` by
    (irule (cj 1 lineage_state_rules) >> first_assum ACCEPT_TAC) >>
  `phi_prefix_length (HD fn.fn_blocks).bb_instructions <=
   LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (simp[entry_step_phi_bound]) >>
  `!i j. revert_forward_pair (HD fn.fn_blocks) i j ==>
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <= i \/
    j < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (rpt strip_tac >> disj1_tac >>
     irule revert_forward_pair_past_params >> goal_assum (drule_at Any)) >>
  `(if allow_own then body_inv_abort_reloc else body_inv_abort)
     rpolicy unit cpl prog ctx lo o2pc i fn r
     (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn)
     (cleanup_caller_height (LENGTH ctx.ctx_functions) ctx (fcg_analyze ctx) fn.fn_name)
     (cleanup_growth_table ctx (fcg_analyze ctx)) r.sr_spill_base lbl_ctr
     r.sr_plan ps_end (HD fn.fn_blocks) ps0 ps0.ps_cleanup_height
     ps0.ps_cleanup_promised ps0
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)
     ps_after ps_after param_ops body_ops
     (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1 ast.as_pc
     vs_p as' Inv ra pc_ret rest ast.as_memory` by
    (asm_x "body" kall_tac >>
     Cases_on `allow_own` >> simp[NoAsms, body_inv_abort_def, body_inv_abort_reloc_def] >>
     gvs[Abbr `ps0`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (fs[fn_entry_state_rel_def] >> NO_TAC) >>
     qexistsl_tac [`[]`, `[]`, `ps_after.ps_stack`] >> simp[]) >>
  asm_x "body" drule >> disch_then drule_all >> strip_tac >>
  qpat_assum `run_blocks (SUC fuel) ctx fn vs = _`
    (fn th => PURE_REWRITE_TAC [th]) >>
  map_every (fn q => qpat_assum q (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]))
    [`o2pc = build_offset_to_pc prog`, `ctx = unit.cu_context`] >>
  conj_tac >- suspend "halt" >>
  conj_tac >- suspend "abort" >>
  suspend "return"
QED

Resume stopped_entry_lift_mode[halt]:
  rpt strip_tac >>
  qpat_x_assum `!v. block_rest _ _ _ _ _ = Halt v ==> _` drule >>
  strip_tac >> rename1 `asm_steps _ _ _ m as' = AsmHalt out` >>
  qexistsl_tac [`n + m`, `out`] >>
  simp[asm_steps_add, sym_steps_mode_add]
QED

Resume stopped_entry_lift_mode[abort]:
  rpt strip_tac >>
  qpat_x_assum `!a v. block_rest _ _ _ _ _ = Abort a v ==> _` drule >>
  disch_then (DISJ_CASES_THEN assume_tac)
  >- (pop_assum strip_assume_tac >> disj1_tac >>
      rename1 `sym_terminal (sym_steps_mode allow_own prog env own m ss')` >>
      qexistsl_tac [`n + m`, `out`] >> simp[asm_steps_add, sym_steps_mode_add]) >>
  pop_assum strip_assume_tac >>
  disj2_tac >> qexistsl_tac [`n + nc`, `cut`, `sc`] >>
  simp[asm_steps_add, sym_steps_mode_add] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Resume stopped_entry_lift_mode[return]:
  rpt strip_tac >>
  qpat_x_assum `!rv v. block_rest _ _ _ _ _ = IntRet rv v ==> _` drule >>
  strip_tac >> rename1 `asm_steps _ _ _ m as' = AsmOK out` >>
  qexistsl_tac [`n + m`, `out`, `ss''`] >>
  simp[asm_steps_add, sym_steps_mode_add] >>
  irule entry_step_return >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> qexistsl_tac [`SUC fuel`, `rv`] >> simp[]
QED

Finalise stopped_entry_lift_mode

Theorem stopped_entry_lift:
  (!rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
    spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv ra pc_ret
    rest mem0 env ret srest labs0 ss.
    body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss ==>
    (!vs'. block_rest fuel ctx fn bb vs = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. block_rest fuel ctx fn bb vs = Abort a vs' ==>
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
    (!rv vs'. block_rest fuel ctx fn bb vs = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         context_memory_rel cpl vs'.vs_memory out.as_memory /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           read_byte b out.as_memory = read_byte b mem0) /\
         shared_state_rel vs' out /\
         sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) ==>
  !rpolicy unit cpl prog ctx lo o2pc i r fn vs ast Inv ra pc_ret rest
    env ret srest ss.
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
    asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp r.sr_plan) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cpl fn vs ast ra rest /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    label_flow_ok ctx /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_sym_rel prog env ast ss /\
    ss.sym_stack = (if fn_has_retpc fn then [Lab ret 0] else []) ++
      MAP Val (REVERSE vs.vs_params) ++ srest /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cpl b) ==>
    (!vs'. run_blocks (SUC fuel) ctx fn vs = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. run_blocks (SUC fuel) ctx fn vs = Abort a vs' ==>
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
    (!rv vs'. run_blocks (SUC fuel) ctx fn vs = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         fn_return_state_rel ctx cpl fn vs' ast out /\
         sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))
Proof
  ACCEPT_TAC (Q.SPECL [`F`, `[]`] stopped_entry_lift_mode |>
    PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
