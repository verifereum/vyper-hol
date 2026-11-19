Theory staticAbortStoppedBody
Ancestors
  staticAbortStoppedBodyCut staticAbortStoppedObservationPrefix
  staticAbortStoppedBodySequential staticAbortStoppedBodyInvoke staticAbortStoppedBodyTerminator
  staticAbortStoppedInvokeCut staticAbortStoppedInvokeReturn
  staticAbortProtectedOrdinary staticAbortProtectedGas staticAbortProtectedTerminal
  fnFrameSymbolicPrefix fnStaticAbortBodyFacts fnBlockBodyClasses
  fnBlockBody fnBlockBodySteps fnStaticAbortBoundary symBlockBody contextStaticAbortRel
  staticAbortExec staticAbortDefs contextCodegenRel asmSem asmSymSem asmSplice codegenSymRel
  venomExecSemantics venomExecProps venomInst unitShapeDefs
  o1LowerDloadRequestForward stepWriteFootprintForward list rich_list

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

(* A and R below are statement-local lambdas, not new HOL constants.
   A retains the complete provenance of a cut, including callee cuts. *)
Theorem stopped_block_body_from_lower_fuel:
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
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss
      (block_rest fuel ctx fn bb vs)
Proof
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qspec_then `A` mp_tac stopped_abort_observation_prefix >>
  (impl_tac >- simp[Abbr `A`]) >> disch_then (mk_asm "AP") >>
  qspec_then `R` mp_tac stopped_result_observation_prefix >>
  (impl_tac >- simp[Abbr `R`, Abbr `A`]) >> disch_then (mk_asm "RP") >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "E") (mk_asm "F")) >>
  rpt gen_tac >>
  map_every qid_spec_tac
    [`ss`, `labs0`, `srest`, `ret`, `env`, `mem0`, `rest`, `pc_ret`, `ra`,
     `Inv`, `ast`, `vs`, `pc0`, `ps`, `rest_ops`, `prefix_ops`, `ps_after`,
     `ps_dfs_after`, `block_ops`, `ps_dfs`, `promised`, `h`, `ps_l`,
     `ps_end`, `fn_ops`, `lbl_ctr`, `spill_base`, `growth`, `ch`, `cfg`,
     `dfg`, `liveness`, `r`, `fn`, `i`, `o2pc`, `lo`, `ctx`, `prog`,
     `cpl`, `unit`, `rpolicy`] >>
  measureInduct_on `(\(bb,k). LENGTH bb.bb_instructions - k) (bb,k)` >>
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  rpt gen_tac >> strip_tac >>
  Cases_on `in_static_abort_prefix fn vs \/ in_revert_forward fn vs`
  >- suspend "cut"
  >> suspend "protected"
QED

Resume stopped_block_body_from_lower_fuel[cut]:
  mp_tac stopped_body_cut_observation >>
  disch_then drule_all >> simp[Abbr `R`, Abbr `A`]
QED

Resume stopped_block_body_from_lower_fuel[protected]:
  qpat_x_assum `~(_ \/ _)`
    (strip_assume_tac o REWRITE_RULE[DE_MORGAN_THM]) >>
  `vs.vs_inst_idx = k` by fs[body_inv_abort_def] >>
  Cases_on `k < LENGTH bb.bb_instructions`
  >- (Cases_on `(EL k bb.bb_instructions).inst_opcode = INVOKE`
      >- suspend "invoke"
      >> Cases_on `is_terminator (EL k bb.bb_instructions).inst_opcode`
      >- suspend "terminator"
      >> suspend "sequential") >>
  `exec_block fuel ctx bb vs = Error "block not terminated"` by
    (once_rewrite_tac[exec_block_def] >> simp[get_instruction_def]) >>
  pure_rewrite_tac[block_rest_def] >>
  qpat_x_assum `exec_block fuel ctx bb vs = _` (fn th => rewrite_tac[th]) >>
  simp[NoAsms, Abbr `R`]
QED

Resume stopped_block_body_from_lower_fuel[invoke]:
  qspec_then `A` mp_tac (Q.INST [`m` |-> `LENGTH bb.bb_instructions - k`]
    stopped_body_invoke_case) >>
  (impl_tac >- simp[Abbr `A`]) >>
  disch_then (qspec_then `R` mp_tac) >>
  (impl_tac >- simp[Abbr `R`]) >>
  impl_tac >- (rpt conj_tac >- (asm "AP" ACCEPT_TAC)
              >- (asm "RP" ACCEPT_TAC)
              >- (asm "E" ACCEPT_TAC) >>
              rpt gen_tac >> strip_tac >>
              qpat_x_assum `!y. _ < _ ==> _`
                (qspec_then `(bb',k')` mp_tac) >>
              simp[] >> disch_then drule_all >> simp[]) >>
  disch_then (drule_at (Pat `body_inv_abort`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >>
  simp[]
QED

Resume stopped_block_body_from_lower_fuel[terminator]:
  qspec_then `A` mp_tac stopped_body_terminator_case >>
  (impl_tac >- simp[Abbr `A`]) >>
  disch_then (qspec_then `R` mp_tac) >>
  (impl_tac >- simp[Abbr `R`]) >>
  (impl_tac >-
    (conj_tac >-
      (conj_tac >-
        (rpt gen_tac >> strip_tac >> asm "AP" drule_all >> simp[]) >>
       rpt gen_tac >> strip_tac >> asm "RP" drule_all >> simp[]) >>
     asm "F" ACCEPT_TAC)) >>
  disch_then (drule_at (Pat `body_inv_abort`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >>
  simp[]
QED

Resume stopped_block_body_from_lower_fuel[sequential]:
  qspec_then `A` mp_tac (Q.INST [`inst` |-> `EL k bb.bb_instructions`]
    stopped_body_sequential_case) >>
  (impl_tac >- simp[Abbr `A`]) >>
  disch_then (qspec_then `R` mp_tac) >>
  (impl_tac >- simp[Abbr `R`]) >>
  disch_then (drule_at (Pat `body_inv_abort`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >>
  simp[] >>
  (impl_tac >-
    (conj_tac >-
      (rpt gen_tac >> strip_tac >> asm "AP" drule_all >> simp[]) >>
     conj_tac >-
      (rpt gen_tac >> strip_tac >> asm "RP" drule_all >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!y. _ < _ ==> _`
       (qspec_then `(bb,k1)` mp_tac) >>
     simp[] >> disch_then drule_all >> simp[])) >>
  simp[]
QED
Finalise stopped_block_body_from_lower_fuel
