Theory staticAbortStoppedInvokeReturn
Ancestors
  staticAbortStoppedInvokeEntry symFnSimSpec fnStaticAbortInvoke
  symFrameInvoke fnFrameBoundaryInvoke fnFrameDeepInvoke
  contextStaticAbortRel fnStaticAbortBodyFacts fnBlockBodySteps
  contextCodegenRelProps venomExecProps unitShapeDefs list
  fnStaticAbortBoundary venomExecSemantics
  symFrameInvokeSupport asmSymModeOwn asmOwnCodeInvariant asmSymOwnStep
  symFrameBoundaryPairing codegenSymRel

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

Theorem stopped_invoke_normal_return_mode:
  !allow_own own.
  (!rpolicy unit cpl prog ctx lo o2pc i r fn vs ast Inv ra pc_ret rest
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
    (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n ast = AsmHalt as' /\
         venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
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
    (!rv vs'. run_blocks fuel ctx fn vs = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n ast = AsmOK as' /\
         as'.as_pc = pc_ret /\ as'.as_stack = REVERSE rv.iret_values ++ rest /\
         fn_return_state_rel ctx cpl fn vs' ast as' /\
         sym_steps_mode allow_own prog env own n ss = SymOK ss' /\ (if allow_own then asm_sym_rel_own lo prog env own else asm_sym_rel prog env) as' ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) /\
  (if allow_own then body_inv_abort_reloc else body_inv_abort) rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = OK vs1 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env) ctx cpl fn ret srest labs0 ps ast ss ==>
  ?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n ast = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env) ctx cpl fn ret srest labs0 ps' as1 ss1
Proof
  ntac 2 gen_tac >> strip_tac >> drule_all invoke_source_ok >> strip_tac >>
  drule_all stopped_invoke_paired_entry_mode >> strip_tac >>
  `body_inv_abort_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0` by
    (Cases_on `allow_own` >> gvs[body_inv_abort_reloc_canonical]) >>
  `(if allow_own then code_labels_agree prog lo else lo = SND (compute_label_offsets prog))` by
    (Cases_on `allow_own` >>
     RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES]) >>
     PURE_REWRITE_TAC [COND_CLAUSES]
     >- qhdtm_assum `body_inv_abort_reloc`
          (ACCEPT_TAC o cj 2 o REWRITE_RULE [body_inv_abort_reloc_def]) >>
     qhdtm_assum `body_inv_abort`
       (ACCEPT_TAC o cj 2 o REWRITE_RULE [body_inv_abort_def])) >>
  qhdtm_assum `body_inv_abort_reloc`
    (fn th => assume_tac th >> strip_assume_tac (REWRITE_RULE [body_inv_abort_reloc_def] th)) >>
  `cvs.vs_params = args /\ cvs.vs_labels = vs.vs_labels` by
    (gvs[setup_callee_def, AllCaseEqs()] >> simp[]) >>
  qpat_x_assum `!rp u cp p c lo o2pc i r f v a Inv ra pc rest env ret srest ss. _`
    (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`) o cj 3) >>
  disch_then (drule_at (Pat `run_blocks _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `(if allow_own then asm_sym_rel_own _ _ _ _ else asm_sym_rel _ _) _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `EL _ _.ctx_functions = _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations_abort _ _ _`)) >>
  disch_then (drule_at (Pat `if allow_own then code_labels_agree _ _ else _ = SND (compute_label_offsets _)`)) >>
  disch_then (drule_at (Pat `o2pc = build_offset_to_pc _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  disch_then (qspecl_then
    [`ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3`,
     `ret_lbl`, `saved_sym ++ srest`] mp_tac) >>
  (impl_tac >-
    (simp[APPEND_ASSOC] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `ctx = unit.cu_context` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC)) >> strip_tac >>
  drule body_inv_abort_plan_reloc >> strip_tac >>
  drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule_all body_plan_inv_static_reloc >> strip_tac >>
  drule_all body_plan_inv_step_reloc >> strip_tac >>
  drule_all invoke_plan_decompose >> strip_tac >>
  `codegen_context_obligations (\_ _ _ _. F) ctx cpl /\
   MEM fn.fn_name (fcg_analyze ctx).fcg_reachable` by
    fs[body_plan_inv_reloc_def] >>
  `~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name` by
    (drule_all invoke_context_no_cycle >> simp[]) >>
  `ordered_spill_regions cpl.cp_regions /\ ctx_wf ctx` by
    fs[contextCodegenRelTheory.codegen_context_obligations_def,
       stackPlanTypesTheory.context_plan_layout_wf_def] >>
  `fn_directly_calls ctx fn.fn_name callee.fn_name` by
    metis_tac[invoke_direct_call] >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`EL k bb.bb_instructions = inst`, `EL j ctx.ctx_functions = callee`,
     `EL i ctx.ctx_functions = fn`, `EL i cpl.cp_regions = r`,
     `vs.vs_inst_idx = k`, `ast.as_pc = _`] >>
  qpat_x_assum `ctx = _` kall_tac >>
  `ops' = ops /\ ps'' = ps'` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME (ops,ps')`,
        `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME (ops',ps'')`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  pop_assum strip_assume_tac >>
  `iops' = iops /\ prepared' = prepared` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`emit_input_plan INVOKE _ _ _ = (iops,prepared)`,
        `emit_input_plan INVOKE _ _ _ = (iops',prepared')`,
        `compute_operands inst = arg_ops`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[pairTheory.PAIR_EQ]) >>
  pop_assum strip_assume_tac >>
  `rops' = rops /\ arranged' = arranged` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`reorder_plan _ _ _ = (rops,arranged)`,
        `reorder_plan _ _ _ = (rops',arranged')`,
        `compute_operands inst = arg_ops`, `prepared' = prepared`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[pairTheory.PAIR_EQ]) >>
  pop_assum strip_assume_tac >>
  `ret_lbl' = ret_lbl /\ post = pops ++ opts` by
    (qpat_assum `ops' = _ ++ _` mp_tac >>
     qpat_assum `ops = _ ++ _` mp_tac >>
     map_every (fn q => qpat_assum q (fn th => PURE_REWRITE_TAC [th]))
       [`ops' = ops`, `iops' = iops`, `rops' = rops`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  pop_assum strip_assume_tac >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`ops' = ops`, `ps'' = ps'`, `iops' = iops`, `prepared' = prepared`,
     `rops' = rops`, `arranged' = arranged`, `ret_lbl' = ret_lbl`, `post = pops ++ opts`,
     `pushed = _`, `consumed = _`] >>
  qpat_x_assum `callee.fn_name = nm` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `compute_operands inst = arg_ops`
    (fn th => SUBST_ALL_TAC th >> assume_tac th) >>
  `LENGTH arg_ops <= LENGTH prepared.ps_stack` by
    (qpat_assum `LENGTH arg_ops <= LENGTH (SND _).ps_stack` mp_tac >>
     map_every (fn q => qpat_assum q (fn th => PURE_REWRITE_TAC [th]))
       [`inst.inst_opcode = INVOKE`, `emit_input_plan INVOKE _ _ _ = (iops,prepared)`] >>
     simp[]) >>
  qpat_assum `compute_operands inst = arg_ops` (fn th =>
    drule_all (Q.INST [`inst` |-> `inst`] (SPEC_ALL invoke_entry_structural_marked)
      |> PURE_REWRITE_RULE [th])) >> strip_tac >>
  `ALL_DISTINCT inst.inst_outputs` by
    metis_tac[genBlockSimTheory.codegen_ready_inst_outputs_distinct] >>
  `EVERY (\x. ~retpc_var fn x) inst.inst_outputs` by
    (simp[EVERY_MEM] >> rpt gen_tac >> disch_tac >>
     irule frameViewFactsTheory.noncopy_output_not_retpc >>
     conj_tac >- fs[stackPlanGenTheory.codegen_ready_fn_def] >>
     qexists `inst` >> simp[]) >>
  `ssa_form fn` by fs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `LENGTH ret'.iret_values = LENGTH inst.inst_outputs` by
    (qpat_x_assum `bind_outputs _ _ _ = SOME _` mp_tac >>
     rw[bind_outputs_def]) >>
  `ss'.sym_stack = MAP Val (REVERSE ret'.iret_values) ++ (saved_sym ++ srest)` by
    simp[APPEND_ASSOC] >>
  `!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl callee.fn_name b ==>
    FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b` by simp[] >>
  qabbrev_tac `fixed = if allow_own then own else ast.as_code` >>
  `as'.as_code = ast.as_code /\ mid.as_code = ast.as_code` by
    metis_tac[asm_steps_code_preserved] >>
  `asm_sym_rel_own lo prog env fixed as' ss' /\
   sym_frame_inv_own lo prog env fixed ctx cpl fn ret srest labs0 arranged mid sms` by
    (Cases_on `allow_own` >>
     gvs[Abbr `fixed`, asm_sym_rel_own_canonical, sym_frame_inv_canonical_own]) >>
  drule_at (Pat `fresh_label _ _ = _`)
    symFrameInvokeSupportTheory.sym_invoke_return_frame_from_callee_own >>
  disch_then drule_all >> strip_tac >>
  `fn_return_state_rel ctx cpl callee rvs mid as'` by
    (qpat_x_assum `fn_return_state_rel _ _ _ _ _ as'` mp_tac >>
     simp[frameRelTheory.fn_return_state_rel_def]) >>
  `asm_block_at prog as'.as_pc
    (execute_plan cpl.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))` by
    (qpat_assum `as'.as_pc = _` SUBST1_TAC >>
     qspecl_then [`prog`, `ast.as_pc`, `cpl.cp_initial_fmp`, `iops`, `rops`,
       `ret_lbl`, `callee.fn_name`, `pops`, `opts`] mp_tac invoke_return_block >>
     impl_tac >- (
       qpat_assum `ops = _` (fn th =>
         qpat_assum `asm_block_at prog ast.as_pc (execute_plan _ ops)`
           (mp_tac o PURE_REWRITE_RULE [th])) >>
       simp_tac bool_ss [GSYM APPEND_ASSOC]) >>
     simp[]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts)` by
    (qpat_assum `ops = _` (fn th =>
       qpat_assum `EVERY _ ops` (mp_tac o PURE_REWRITE_RULE [th])) >>
     simp_tac bool_ss [EVERY_APPEND] >> simp[]) >>
  drule invoke_called_plan_fields >> strip_tac >>
  `spill_alloc_layout_wf called.ps_alloc called.ps_spilled` by gvs[] >>
  qspecl_then [
    `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `fn`, `ra`, `rest`, `mem0`,
    `arranged`, `arg_ops`, `args`, `vs`, `mid`, `saved`, `ret'.iret_values`,
    `callee`, `rvs`, `ret'`, `vs1`, `as'`, `r`, `inst.inst_outputs`,
    `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`, `dfg`,
    `inst`, `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`, `ret_lbl`,
    `called`, `pops`, `popped`, `opts`, `swapped`, `ps'`]
    mp_tac invoke_return_frame_numeric_exact >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    simp[])) >> strip_tac >>
  `!n cs now next. asm_sym_rel_own lo prog env fixed cs now /\
      sym_steps_mode allow_own prog env fixed n now = SymOK next ==>
      ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
        asm_sym_rel_own lo prog env fixed cs' next` by
    (rpt gen_tac >> strip_tac >> metis_tac[asm_sym_steps_mode_sim]) >>
  mp_tac (Q.INST [
    `allow_own` |-> `allow_own`, `p` |-> `prog`, `own` |-> `fixed`,
    `cplan` |-> `cpl`, `asr` |-> `as'`, `ssr` |-> `ss'`,
    `final` |-> `ps'`, `outs` |-> `inst.inst_outputs`,
    `nl` |-> `live_vars_at liveness bb.bb_label (k + 1)`,
    `halting` |-> `bb_is_halting bb`,
    `term` |-> `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
    `vs'` |-> `vs1`]
    symFrameInvokeSupportTheory.sym_invoke_return_frame_numeric_own) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    simp[] >>
    qpat_assum `o2pc = build_offset_to_pc prog` (SUBST1_TAC o SYM) >>
    qpat_assum `asm_steps lo o2pc prog (1 + _) as' = AsmOK fin`
      (ACCEPT_TAC o ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]))) >>
  disch_then (qx_choose_then `sfin` strip_assume_tac) >>
  `fin.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
    (iops ++ rops ++ [SOPushLabel ret_lbl; SOPushLabel callee.fn_name;
       SOEmit "JUMP"; SOLabel ret_lbl] ++ pops ++ opts))` by
    (simp[stackOpSimTheory.execute_plan_append,
      planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def] >>
     decide_tac) >>
  `!k st. sym_steps_mode allow_own prog env fixed k st =
           sym_steps_mode allow_own prog env own k st` by
    (Cases_on `allow_own` >> simp[NoAsms, Abbr `fixed`, sym_steps_mode_def]) >>
  qexistsl_tac [`ops`, `ps'`, `rest'`,
    `(LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3) +
      (n + (1 + LENGTH (execute_plan cpl.cp_initial_fmp (pops ++ opts))))`,
    `fin`, `sfin`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (ONCE_REWRITE_TAC [stackOpSimTheory.asm_steps_add] >>
      qpat_assum `asm_steps lo o2pc prog (_ + 3) ast = _`
        (fn th => simp_tac (srw_ss()) [th]) >>
      ONCE_REWRITE_TAC [stackOpSimTheory.asm_steps_add] >>
      qpat_assum `asm_steps lo o2pc prog n cas = _`
        (fn th => simp_tac (srw_ss()) [th]) >>
      first_assum ACCEPT_TAC)
  >- (qpat_assum `ops = _` SUBST1_TAC >>
      qpat_assum `fin.as_pc = ast.as_pc + _` mp_tac >>
      simp_tac bool_ss [GSYM APPEND_ASSOC])
  >- (ONCE_REWRITE_TAC [sym_steps_mode_add] >>
      qpat_assum `sym_steps_mode allow_own prog env own (_ + 3) ss = _`
        (fn th => simp_tac (srw_ss()) [th]) >>
      ONCE_REWRITE_TAC [sym_steps_mode_add] >>
      qpat_assum `sym_steps_mode allow_own prog env own n scas = _`
        (fn th => simp_tac (srw_ss()) [th]) >>
      qpat_assum `!k st. sym_steps_mode _ _ _ fixed k st = _`
        (fn th => PURE_REWRITE_TAC [GSYM th]) >>
      first_assum ACCEPT_TAC)
  >- (qpat_assum `sym_frame_inv_own lo prog env fixed _ _ _ _ _ _ ps' fin sfin` mp_tac >>
      Cases_on `allow_own` >>
      simp[NoAsms, Abbr `fixed`, sym_frame_inv_canonical_own] >>
      `lo = SND (compute_label_offsets prog)` by
        (qpat_assum `(if F then code_labels_agree prog lo else _) `
          (ACCEPT_TAC o PURE_REWRITE_RULE [COND_CLAUSES])) >>
      `fin.as_code = ast.as_code` by metis_tac[asm_steps_code_preserved] >>
      simp[sym_frame_inv_canonical_own])

QED

Theorem stopped_invoke_normal_return:
  (!rpolicy unit cpl prog ctx lo o2pc i r fn vs ast Inv ra pc_ret rest
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
    (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n ast = AsmHalt as' /\
         venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
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
    (!rv vs'. run_blocks fuel ctx fn vs = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n ast = AsmOK as' /\
         as'.as_pc = pc_ret /\ as'.as_stack = REVERSE rv.iret_values ++ rest /\
         fn_return_state_rel ctx cpl fn vs' ast as' /\
         sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = OK vs1 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  label_flow_ok ctx /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss ==>
  ?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n ast = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1
Proof
  ACCEPT_TAC (Q.SPECL [`F`, `[]`] stopped_invoke_normal_return_mode |>
    PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
