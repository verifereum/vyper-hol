Theory codegenStaticAbortCutSim
Ancestors
  staticAbortStoppedBody staticAbortStoppedEntryLift staticAbortStoppedNonentryLift
  codegenLabelDisciplined codegenEntrySim codegenEntryFacts contextStaticAbortRel
  fnStaticAbortBoundary symFnSimSpec venomExecSemantics list
  venomExecProps venomExecProofs venomWf venomInst fragExec
  unitShapeDefs contextCodegenRel codegenAsmStaticWf

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

(* Statement-local observations preserve both normal clauses and the complete
   provenance of a stopped abort, including a cut in an invoked function. *)
Theorem stopped_fn_simulations:
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
  !fuel.
  (!rpolicy unit cpl prog ctx lo o2pc i r fn vs ast Inv ra pc_ret rest env ret srest ss.
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
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
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
      (run_blocks fuel ctx fn vs))
Proof
  qx_gen_tac `aobs` >>
  disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qx_gen_tac `robs` >>
  disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  Induct
  >- simp[Abbr `robs`, run_blocks_def] >>
  qspec_then `aobs` mp_tac stopped_block_body_from_lower_fuel >>
  (impl_tac >- simp[Abbr `aobs`]) >>
  disch_then (qspec_then `robs` mp_tac) >>
  (impl_tac >- simp[Abbr `robs`]) >>
  (impl_tac >- (first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "body") >> conj_tac
  >- (mp_tac stopped_entry_lift >> markerLib.REABBREV_TAC >>
      (impl_tac >- (asm_x "body" mp_tac >> simp[Abbr `robs`])) >>
      simp[]) >>
  qspecl_then [`fuel`, `robs`] mp_tac stopped_nonentry_lift >>
  (impl_tac >- simp[Abbr `robs`, Abbr `aobs`]) >>
  (impl_tac >- (asm_x "body" ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Theorem codegen_entry_abort_stopped:
  !fuel rpolicy unit cp prog Inv vs s env a vs'.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations_abort Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    (!fn inst l.
      MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    label_flow_ok unit.cu_context /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      unit.cu_context /\ sym_unit_static_ok unit /\
    vs.vs_code = assemble prog ++ vs.vs_data_section /\
    s.as_code = assemble prog ++ vs.vs_data_section /\
    codegen_asm_entry_rel cp prog vs s /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_ok prog env vs.vs_code /\
    run_context fuel unit.cu_context vs = Abort a vs' ==>
    (?n out.
      (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n s = AsmRevert out \/
       asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n s = AsmFault out) /\
      sym_terminal (sym_steps prog env n (sym_init s)) /\
      out.as_requests <<= vs'.vs_requests) \/
    (?nc cut sc iC fnC rC livC dfgC cfgC chC growthC spillC ctrC fnopsC endC
      bbC pslC hC promisedC dfsC blockC dfsafterC afterC prefixC restopsC kC
      psC pcC cvsC raC pcretC restC memC retC srestC labsC.
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog nc s = AsmOK cut /\
      sym_steps prog env nc (sym_init s) = SymOK sc /\
      body_inv_abort rpolicy unit cp prog unit.cu_context
        (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        iC fnC rC livC dfgC cfgC chC growthC spillC ctrC fnopsC endC bbC pslC
        hC promisedC dfsC blockC dfsafterC afterC prefixC restopsC kC psC pcC
        cvsC cut Inv raC pcretC restC memC /\
      sym_frame_inv prog env unit.cu_context cp fnC retC srestC labsC psC cut sc /\
      (in_static_abort_prefix fnC cvsC \/ in_revert_forward fnC cvsC) /\
      cut.as_requests = vs'.vs_requests)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all codegen_entry_selection >> strip_tac >>
  `lookup_function fe.fn_name unit.cu_context.ctx_functions = SOME fe` by
    simp[lookup_function_def, FIND_thm] >>
  `run_blocks fuel unit.cu_context fe
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) =
    Abort a vs'` by metis_tac[run_context_run_blocks] >>
  drule_all codegen_entry_layout >> strip_tac >>
  `fn_entry_state_rel cp fe
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    s 0w []` by (irule codegen_asm_entry_fn_state_rel >> metis_tac[]) >>
  `MEM fe.fn_name (fcg_analyze unit.cu_context).fcg_reachable` by
    (irule codegen_entry_reachable >>
     gvs[unit_shape_ok_def, entry_fn_first_def, codegen_context_obligations_abort_def]) >>
  `codegen_context_obligations (\c f i s. F) unit.cu_context cp` by
    fs[codegen_context_obligations_abort_def, codegen_context_obligations_def,
       codegen_memory_obligations_def] >>
  mp_tac (Q.INST [`Inv` |-> `\c f i s. F`] codegen_invoke_targets_retpc) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all codegen_asm_entry_sym_init >> strip_tac >>
  `asm_static_wf prog` by metis_tac[codegen_asm_static_wf, codegen_context_obligations_def] >>
  (* Earlier resisting specialization used mp_tac followed by DISCH_THEN:
     its assumed theorem had free variables in its hypotheses, so matching
     could not instantiate the fn_entry_state_rel arguments. *)
  drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`)
    (stopped_fn_simulations |> Unwind.UNWIND_FORALL_RULE
       |> Unwind.UNWIND_FORALL_RULE |> BETA_RULE
       |> Q.SPEC `fuel` |> CONJUNCT1 |> BETA_RULE |> SPEC_ALL
       |> Q.INST [`i` |-> `0`, `pc_ret` |-> `0`,
                  `ret` |-> `""`, `srest` |-> `[]`]) >>
  disch_then (drule_at (Pat `asm_sym_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations_abort _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  simp[frameRelTheory.fn_has_retpc_def, codegen_asm_entry_rel_def] >>
  disch_then (qspec_then `fuel` mp_tac) >>
  (impl_tac >-
    (gvs[codegen_asm_entry_rel_def, frameRelTheory.fn_has_retpc_def] >>
     conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (drule o CONJUNCT1 o CONJUNCT2) >>
  simp[]
QED
