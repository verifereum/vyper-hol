Theory staticAbortStoppedBodyInvoke
Ancestors
  staticAbortStoppedInvokeCut staticAbortStoppedInvokeReturn
  fnBlockBody fnBlockBodySteps fnStaticAbortBodyFacts fnBlockBodyClasses
  fnStaticAbortBoundary symBlockBody contextStaticAbortRel
  venomExecSemantics venomExecProps venomInst unitShapeDefs
  asmSem asmSymSem asmSplice codegenSymRel rich_list list

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

Theorem stopped_body_invoke_case:
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
  (!rpolicy unit cpl prog ctx lo o2pc Inv env n ast0 ast1 ss0 ss1 vs'.
     asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
     sym_steps prog env n ss0 = SymOK ss1 /\
     A rpolicy unit cpl prog ctx lo o2pc Inv env ast1 ss1 vs' ==>
     A rpolicy unit cpl prog ctx lo o2pc Inv env ast0 ss0 vs') /\
  (!rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0
    n ast0 ast1 ss0 ss1 res.
     asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
     sym_steps prog env n ss0 = SymOK ss1 /\
     R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1 res ==>
     R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast0 ss0 res) /\
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
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
       A rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs') /\
    (!rv vs'. run_blocks fuel ctx fn vs = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         fn_return_state_rel ctx cpl fn vs' ast out /\
         sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) /\
  (!rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
    spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv ra pc_ret
    rest mem0 env ret srest labs0 ss.
    LENGTH bb.bb_instructions - k < m /\
    body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss
      (block_rest fuel ctx fn bb vs)) ==>
  !rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv ra pc_ret
   rest mem0 env ret srest labs0 ss inst.
    m = LENGTH bb.bb_instructions - k /\
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
    inst.inst_opcode = INVOKE ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss
      (block_rest fuel ctx fn bb vs)
Proof
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  `vs.vs_inst_idx = k` by fs[body_inv_abort_def] >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by simp[get_instruction_def] >>
  `LENGTH (compute_operands inst) <= 16` by
    (irule body_operands_le_16 >> conj_tac >- simp[] >>
     qexists `fn` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `?nm arg_ops. inst.inst_operands = Label nm :: arg_ops` by
    (qpat_x_assum `codegen_ready_inst inst` mp_tac >>
     qpat_x_assum `inst.inst_opcode = INVOKE` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[stackPlanGenTheory.codegen_ready_inst_def,
        stackPlanGenTheory.invoke_operands_wf_def] >>
     BasicProvers.every_case_tac >> gvs[]) >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  Cases_on `step_inst fuel ctx inst vs`
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "abort"
  >- suspend "intret"
  >> suspend "error"
QED

Resume stopped_body_invoke_case[ok]:
  (* Failed E0106 route: drule_at body_inv_abort then impl_tac left
     universally quantified arguments. Moving E through simp[Abbr A]
     left beta-redexes in the other hypotheses, so drule_all failed. *)
  Q.UNABBREV_TAC `A` >> rule_assum_tac BETA_RULE >> BETA_TAC >>
  drule stopped_invoke_normal_return >>
  disch_then drule_all >> strip_tac >>
  `!j. ~revert_forward_pair bb k j` by
    (rpt strip_tac >>
     qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
     simp[contextCodegenRelTheory.revert_forward_pair_def]) >>
  drule_all body_inv_abort_advance >> strip_tac >>
  drule_all block_rest_advance >> disch_then (qspec_then `fn` SUBST1_TAC) >>
  qpat_assum `!rp u cp p c lo o2pc i f r liv dfg cfg ch g sb lc fo pe b pl h pr dfs bo da pa po ro k ps pc v a Inv ra pc_ret rest mem env ret srest labs ss. _`
    (drule_at (Pat `body_inv_abort`)) >>
  disch_then (qspecl_then [`env`, `ret`, `srest`, `labs0`, `ss1`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qpat_assum `!rp u cp p c lo o2pc Inv env fn mem pc rest sr labs n a0 a1 s0 s1 res. _`
    (drule_all_then mp_tac) >>
  simp[]
QED
Resume stopped_body_invoke_case[halt]:
  Q.UNABBREV_TAC `A` >> rule_assum_tac BETA_RULE >> BETA_TAC >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_halt >> strip_tac >>
  drule_all staticAbortStoppedInvokeProbeTheory.stopped_invoke_paired_entry >> strip_tac >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  `cvs.vs_params = args /\ cvs.vs_labels = vs.vs_labels` by
    (gvs[setup_callee_def, AllCaseEqs()] >> simp[]) >>
  qpat_assum `!rp u cp p c lo o2pc i r f v a Inv ra pc rest env ret srest ss. _`
    (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`) o cj 1) >>
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
  drule block_rest_other >> disch_then drule >>
  disch_then (qspec_then `fn` (SUBST1_TAC o SRULE [])) >>
  (* E0113: contextual simp[Abbr R] timed out over E/K hypotheses. *)
  Q.UNABBREV_TAC `R` >> BETA_TAC >> simp[NoAsms] >>
  (* Backward irule left existential prefix witnesses, not conjuncts. *)
  drule_all symFrameInvokeTheory.sym_invoke_halt_compose >>
  disch_then ACCEPT_TAC
QED
Resume stopped_body_invoke_case[abort]:
  Q.UNABBREV_TAC `A` >> rule_assum_tac BETA_RULE >> BETA_TAC >>
  drule stopped_invoke_abort_boundary >> disch_then drule_all >> disch_tac >>
  drule block_rest_other >> disch_then drule >>
  disch_then (qspec_then `fn` (SUBST1_TAC o SRULE [])) >>
  (* Contextual simp[Abbr R] also timed out here. *)
  Q.UNABBREV_TAC `R` >> BETA_TAC >> simp[NoAsms] >>
  first_assum ACCEPT_TAC
QED
Resume stopped_body_invoke_case[intret]:
  metis_tac[step_inst_invoke_not_intret]
QED
Resume stopped_body_invoke_case[error]:
  drule block_rest_other >> disch_then drule >>
  disch_then (qspec_then `fn` (SUBST1_TAC o SRULE [])) >>
  Q.UNABBREV_TAC `R` >> BETA_TAC >> simp[NoAsms]
QED
Finalise stopped_body_invoke_case
