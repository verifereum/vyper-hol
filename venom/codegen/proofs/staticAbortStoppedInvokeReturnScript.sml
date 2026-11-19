Theory staticAbortStoppedInvokeReturn
Ancestors
  staticAbortStoppedInvokeEntry symFnSimSpec fnStaticAbortInvoke
  symFrameInvoke fnFrameBoundaryInvoke fnFrameDeepInvoke
  contextStaticAbortRel fnStaticAbortBodyFacts fnBlockBodySteps
  contextCodegenRelProps venomExecProps unitShapeDefs list
  fnStaticAbortBoundary venomExecSemantics

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

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
  strip_tac >> drule_all invoke_source_ok >> strip_tac >>
  drule_all stopped_invoke_paired_entry >> strip_tac >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  `cvs.vs_params = args /\ cvs.vs_labels = vs.vs_labels` by
    (gvs[setup_callee_def, AllCaseEqs()] >> simp[]) >>
  qpat_x_assum `!rp u cp p c lo o2pc i r f v a Inv ra pc rest env ret srest ss. _`
    (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`) o cj 3) >>
  disch_then (drule_at (Pat `run_blocks _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `asm_sym_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `EL _ _.ctx_functions = _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations_abort _ _ _`)) >>
  disch_then (drule_at (Pat `lo = SND (compute_label_offsets _)`)) >>
  disch_then (drule_at (Pat `o2pc = build_offset_to_pc _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  disch_then (qspecl_then
    [`ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3`,
     `ret_lbl`, `saved_sym ++ srest`] mp_tac) >>
  (impl_tac >-
    (simp[APPEND_ASSOC] >> conj_tac
     >- (qpat_assum `ctx = unit.cu_context` (SUBST1_TAC o SYM) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `ctx = unit.cu_context` (SUBST1_TAC o SYM) >>
     qpat_assum `lo = SND (compute_label_offsets prog)` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC)) >> strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all invoke_plan_decompose >> strip_tac >>
  `codegen_context_obligations (\_ _ _ _. F) ctx cpl /\
   MEM fn.fn_name (fcg_analyze ctx).fcg_reachable` by
    fs[body_plan_inv_def] >>
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
  qpat_x_assum `lo = _` (fn loeq =>
    qpat_x_assum `o2pc = _` (fn pceq =>
      gvs[] >> assume_tac loeq >> assume_tac pceq)) >>
  drule_all invoke_entry_structural_marked >> strip_tac >>
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
  drule_at (Pat `fresh_label _ _ = _`) sym_invoke_return_frame_from_callee >>
  disch_then drule_all >> strip_tac >>
  `fn_return_state_rel ctx cpl callee rvs mid as'` by
    (qpat_x_assum `fn_return_state_rel _ _ _ _ _ as'` mp_tac >>
     simp[frameRelTheory.fn_return_state_rel_def]) >>
  `asm_block_at prog as'.as_pc
    (execute_plan cpl.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))` by
    (qpat_x_assum `as'.as_pc = _` SUBST1_TAC >>
     drule invoke_return_block >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts)` by
    simp[EVERY_APPEND] >>
  drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ called _ _`)
    (sym_invoke_return_frame_numeric
      |> Q.INST [`final` |-> `release_dead_spills nl swapped`]
      |> PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >>
  disch_then drule_all >> strip_tac >>
  `fin.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
    (iops ++ rops ++ [SOPushLabel ret_lbl; SOPushLabel callee.fn_name;
       SOEmit "JUMP"; SOLabel ret_lbl] ++ pops ++ opts))` by
    (simp[stackOpSimTheory.execute_plan_append,
      planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def] >>
     decide_tac) >>
  qpat_assum `sym_steps _ _ (_ + 3) _ = _`
    (mp_then (Pat `sym_steps _ _ _ _ = _`) mp_tac sym_invoke_ok_compose) >>
  disch_then drule_all >> strip_tac >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  rpt conj_tac >> FIRST_PROVE [first_assum ACCEPT_TAC, decide_tac]
QED
