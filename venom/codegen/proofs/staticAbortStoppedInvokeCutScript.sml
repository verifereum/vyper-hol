Theory staticAbortStoppedInvokeCut
Ancestors
  staticAbortStoppedInvokeEntry symFnSimSpec fnStaticAbortInvoke
  symFrameInvoke fnFrameBoundaryInvoke fnFrameDeepInvoke
  contextStaticAbortRel fnStaticAbortBodyFacts fnBlockBodySteps
  contextCodegenRelProps venomExecProps unitShapeDefs list
  fnStaticAbortBoundary venomExecSemantics blockSimHelpers codegenSymRel

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

Theorem stopped_invoke_abort_boundary_mode:
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
  step_inst fuel ctx inst vs = Abort a vs1 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  (if allow_own then sym_frame_inv_own lo prog env own else sym_frame_inv prog env) ctx cpl fn ret srest labs0 ps ast ss ==>
  (?n out. (asm_steps lo o2pc prog n ast = AsmRevert out \/
            asm_steps lo o2pc prog n ast = AsmFault out) /\
     sym_terminal (sym_steps_mode allow_own prog env own n ss) /\ out.as_requests <<= vs1.vs_requests) \/
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
     cut.as_requests = vs1.vs_requests)
Proof
  ntac 2 gen_tac >> strip_tac >> drule_all invoke_source_abort >> strip_tac >>
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
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_reloc_def]) >>
  `cvs.vs_params = args /\ cvs.vs_labels = vs.vs_labels` by
    (gvs[setup_callee_def, AllCaseEqs()] >> simp[]) >>
  qpat_x_assum `!rp u cp p c lo o2pc i r f v a Inv ra pc rest env ret srest ss. _`
    (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`) o cj 2) >>
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
     first_assum ACCEPT_TAC)) >>
  disch_then DISJ_CASES_TAC
  >- (disj1_tac >> pop_assum strip_assume_tac >>
      (qexistsl_tac
        [`LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3 + n`, `out`] >>
       conj_tac
       >- metis_tac[asm_steps_compose_revert, asm_steps_compose_fault] >>
       conj_tac >- simp[Once sym_steps_mode_add] >>
       first_assum ACCEPT_TAC)) >>
  disj2_tac >> pop_assum strip_assume_tac >>
  (`asm_steps lo o2pc prog
      (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3 + nc) ast =
      AsmOK cut` by metis_tac[asm_steps_compose_ok] >>
   `sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3 + nc) ss =
      SymOK sc` by metis_tac[sym_steps_mode_compose] >>
   goal_assum (drule_at (Pat `asm_steps`)) >>
   goal_assum (drule_at (Pat `sym_steps_mode`)) >>
   goal_assum (drule_at (Pat `(if allow_own then body_inv_abort_reloc else body_inv_abort)`)) >>
   goal_assum (drule_at (Pat `(if allow_own then sym_frame_inv_own _ _ _ _ else sym_frame_inv _ _)`)) >>
   rpt conj_tac >> FIRST_PROVE [first_assum ACCEPT_TAC, metis_tac[]])
QED

Theorem stopped_invoke_abort_boundary:
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
  step_inst fuel ctx inst vs = Abort a vs1 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  label_flow_ok ctx /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss ==>
  (?n out. (asm_steps lo o2pc prog n ast = AsmRevert out \/
            asm_steps lo o2pc prog n ast = AsmFault out) /\
     sym_terminal (sym_steps prog env n ss) /\ out.as_requests <<= vs1.vs_requests) \/
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
     cut.as_requests = vs1.vs_requests)
Proof
  ACCEPT_TAC (Q.SPECL [`F`, `[]`] stopped_invoke_abort_boundary_mode |>
    PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
