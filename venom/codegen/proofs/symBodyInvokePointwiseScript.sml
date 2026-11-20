(* Body INVOKE planning over the installed callee's two local contracts. *)
Theory symBodyInvokePointwise
Ancestors
  symFrameInvokeCalleePointwise asmSymModeOwn fnBlockBodyClasses fnBlockBodySteps
  symFnSimSpec codegenSymRel unitShapeDefs stackPlanCfgIrrelevance

Theorem sym_body_invoke_step_pointwise:
  (!j callee rj cvs cas cra crest cpc.
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    EL j cpl.cp_regions = rj /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!l. FLOOKUP cvs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cpl.cp_initial_fmp rj.sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cpl callee cvs cas cra crest /\
    (fn_has_retpc callee ==> FLOOKUP o2pc (w2n cra) = SOME cpc) ==>
    (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
        venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
               (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
        venom_asm_terminal_rel vs' as') /\
    (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
      ?n as'. asm_steps lo o2pc prog n cas = AsmOK as' /\
        as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ crest /\
        fn_return_state_rel ctx cpl callee vs' cas as')) /\
  (!j callee rj cvs args cas cra crest cpc scas ret_lbl csrest.
    ctx = unit.cu_context /\
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\ codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    EL j cpl.cp_regions = rj /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
      MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
      MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label callee_name :: args /\
      lookup_function callee_name ctx.ctx_functions = SOME callee ==>
      fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cpl /\ reachability_closed Inv ctx /\
    fn_entry_inv Inv ctx callee cvs /\
    setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
    asm_block_at prog cas.as_pc (execute_plan cpl.cp_initial_fmp rj.sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cpl callee cvs cas cra crest /\
    FLOOKUP o2pc (w2n cra) = SOME cpc /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
    asm_sym_rel_own lo prog env own cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ csrest /\
    MEM (AsmLabel ret_lbl) prog /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cpl b) ==>
    (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps_mode allow_own prog env own n scas)) /\
    (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
               (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps_mode allow_own prog env own n scas)) /\
    (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
      ?n as' ss'. asm_steps lo o2pc prog n cas = AsmOK as' /\
        as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ crest /\
        fn_return_state_rel ctx cpl callee vs' cas as' /\
        sym_steps_mode allow_own prog env own n scas = SymOK ss' /\
        asm_sym_rel_own lo prog env own as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ csrest /\
        (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl callee.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
  (?nm arg_ops. inst.inst_operands = Label nm :: arg_ops) /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest'.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    (!vs1. step_inst fuel ctx inst vs = OK vs1 ==>
      ?n as1 ss1.
        asm_steps lo o2pc prog n as = AsmOK as1 /\
        fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
        as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
        sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
        sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
      ?n as1. asm_steps lo o2pc prog n as = AsmHalt as1 /\
        venom_asm_terminal_rel vs1 as1 /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
      ?n as1. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as1) \/
               (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as1)) /\
        venom_asm_terminal_rel vs1 as1 /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss))
Proof
  strip_tac >>
  drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all body_inv_step_reloc >> strip_tac >>
  drule_all body_inv_static_reloc >> strip_tac >>
  drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >>
  disch_then assume_tac >>
  qhdtm_assum `body_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  qexistsl_tac [`ops`, `ps'`, `rest'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule sym_invoke_frame_sim_deep_pointwise >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  conj_tac >- metis_tac[asm_sym_steps_mode_sim] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> irule body_callee_placed_reloc >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexistsl_tac [`Inv`, `rpolicy`, `unit`] >> gvs[]) >>
  conj_tac >- (qexists_tac `r` >> simp[]) >>
  conj_tac >-
    (qexistsl_tac [`Inv`, `rpolicy`, `unit`] >> gvs[] >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  gvs[] >> rpt (goal_assum (drule_at Any)) >> simp[] >>
  qpat_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[generate_inst_plan_cfg_unit] >> metis_tac[]
QED
