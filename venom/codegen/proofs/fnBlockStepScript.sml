(*
 * The step of the fuel induction behind
 * venomToAsmProps$gen_fn_frame_simulation: one non-entry block, run from
 * a block boundary where fn_frame_inv holds, simulated by its DFS code.
 *
 * TOP-LEVEL (proved from the admitted block pieces of fnBlockBody,
 *            fnFrameSteps, fnFrameSinglePred, fnLineageStatic, fnPlanLineage):
 *   fn_block_frame_step - gen_fn_frame_sim_at_simple (SUC fuel) from both
 *                         function theorems at fuel
 *)

Theory fnBlockStep
Ancestors
  fnBlockBody fnFrameSinglePred fnSimSpec fnFrameSteps fnFrameBoundary fnFrameTerminal gasFrameSim
  genFrameSim fnPlanPlace fnPlanCover fnAliasInv fnPlanLineage frameRel
  venomExecSemantics fnBlockStepHelpers contextCodegenRel venomExecProofs
  stackOpSim fnBlockBodySteps stackPlanGen blockSimHelpers asmRunBounded

(* run_blocks (SUC fuel) runs the current block with run_block fuel and
   continues with run_blocks fuel from its OK result (run_blocks_unfold);
   an INVOKE inside the block runs its callee with run_function fuel.  So
   the hypotheses are the callee simulation (gen_fn_sim_at_simple fuel) and the
   rest of the run from the successor (gen_fn_frame_sim_at_simple fuel).

   Why it should hold: the block's code is its DFS plan (dfs_block_code_placed),
   and the lineage state the run arrived with regenerates that code
   (lineage_state_block_plan).  The block runs as its PHI prefix
   (phi_prefix_frame_sim), then one instruction at a time against
   fn_frame_inv: gen_inst_frame_sim and gas_inst_frame_sim for ordinary
   steps, gen_invoke_frame_sim with the callee hypothesis for INVOKE, and
   at the end gen_jmp_frame_sim / gen_jnz_frame_sim (successor), the halt
   and abort steps (fnFrameTerminal), revert_forward_frame_sim, or
   gen_ret_frame_sim (IntRet).  At a successor the step re-establishes the
   block-boundary premises of gen_fn_frame_sim_at_simple for it (lineage_entry
   from this block, dfs_block_state, the alias premise by
   lineage_alias_successor), and the successor run's assembly steps are
   added to the block's (asm_steps_add_ok). *)
Theorem fn_block_frame_step_resource_at_lo:
  !safe q fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after
   vs as Inv ra pc_ret rest mem0.
    (gen_fn_sim_at_reloc safe q fuel \/
     (lo = SND (compute_label_offsets prog) /\ gen_fn_sim_at safe q fuel)) /\
    (gen_fn_frame_sim_at_reloc safe q fuel \/
     (lo = SND (compute_label_offsets prog) /\ gen_fn_frame_sim_at safe q fuel)) /\
    ctx = unit.cu_context /\ code_labels_agree prog lo /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn vs /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\ ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps /\
    vs.vs_prev_bb = SOME pred /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp block_ops) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s)
    ==>
    body_result safe (OPTION_MAP (\F.
      fn_sim_coefficient unit.cu_context prog * (F unit cp prog + 1)) q)
      lo o2pc prog cp ctx fn mem0 pc_ret rest as (run_blocks (SUC fuel) ctx fn vs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[body_result_def] >>
  rename1 `generate_context_plan ctx = SOME cpl` >>
  qspecl_then [`vs`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- suspend "ok"
  >> simp[run_blocks_unfold, run_block_def]
QED

Resume fn_block_frame_step_resource_at_lo[ok]:
  `run_blocks (SUC fuel) ctx fn vs =
   block_rest fuel ctx fn bb
     (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[run_blocks_unfold, run_block_def, block_rest_def] >>
     Cases_on `exec_block fuel ctx bb
       (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
     simp[]) >>
  pop_assum SUBST1_TAC >>
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
  `dfs_block_state liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr)
     bb.bb_label ps_dfs` by
    (qpat_x_assum `bb.bb_label = _` (fn th => REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all block_step_prefix_reloc >> strip_tac >> suspend "body"
QED

Resume fn_block_frame_step_resource_at_lo[body]:
  Q.SUBGOAL_THEN `?prefixL prefixD core.
     ps_after.ps_stack = prefixL ++ core /\
     ps_dfs_after.ps_stack = prefixD ++ core /\
     (!v. MEM v (live_vars_at liveness bb.bb_label
                   (LENGTH bb.bb_instructions)) ==>
        ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)` ASSUME_TAC
  >- (qexistsl_tac [`prefixL`, `prefixD`, `core`] >> rpt conj_tac >>
      first_assum ACCEPT_TAC) >>
  `!i j. revert_forward_pair bb i j ==>
         phi_prefix_length bb.bb_instructions <= i \/
         j < phi_prefix_length bb.bb_instructions` by
    metis_tac[revert_forward_pair_past_phis] >>
  `n <= LENGTH prog` by
    (drule asmSemTheory.asm_block_at_length >>
     qpat_assum `block_ops = _` (fn th => rewrite_tac[th]) >>
     simp[execute_plan_append] >> decide_tac) >>
  `LENGTH bb.bb_instructions <= context_inst_count ctx` by
    (irule context_inst_count_block >> qexists_tac `fn` >>
     conj_tac
     >- (drule livenessTransferProofsTheory.lookup_block_mem >> simp[]) >>
     metis_tac[listTheory.EL_MEM]) >>
  mp_tac (Q.SPECL [`safe`, `q`, `fuel`, `rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`,
    `o2pc`, `i`, `fn`, `r`, `liveness`, `dfg`, `cfg`, `ch`, `growth`,
    `spill_base`, `lbl_ctr`, `fn_ops`, `ps_end`, `bb`, `ps`, `h`, `promised`,
    `ps_dfs`, `block_ops`, `ps_dfs_after`, `ps_after`, `prefix_ops`,
    `rest_ops`, `phi_prefix_length bb.bb_instructions`, `ps1`, `as.as_pc`,
    `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `as1`,
    `Inv`, `ra`, `pc_ret`, `rest`, `mem0`] block_body_frame_sim_resource_at_lo) >>
  impl_tac >- (gvs[] >> rpt conj_tac >> gvs[] >> metis_tac[]) >>
  simp_tac std_ss [body_result_def] >> strip_tac >> suspend "outcomes"
QED

Resume fn_block_frame_step_resource_at_lo[outcomes]:
  `!m. cost_le (OPTION_MAP (\F.
      (LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions + 1) *
      (LENGTH prog + F unit cpl prog + 8)) q) m ==>
    cost_le (OPTION_MAP (\F.
      fn_sim_coefficient unit.cu_context prog * (F unit cpl prog + 1)) q) (n + m)` by
    (Cases_on `q` >> simp[cost_le_def] >> rpt strip_tac >>
     rename1 `gen_fn_sim_at_reloc safe (SOME budget) fuel \/ _` >>
     qspecl_then [`LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions`,
       `context_inst_count ctx`, `LENGTH prog`, `budget unit cpl prog`, `7`]
       mp_tac fn_sim_budget_absorb >>
     gvs[fn_sim_coefficient_def] >> decide_tac) >>
  simp_tac std_ss [optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `!vs'. block_rest _ _ _ _ _ = Halt _ ==> _`
        (qspec_then `vs'` mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      metis_tac[asm_steps_compose_halt, create_safe_prefix_compose])
  >- (qpat_x_assum `!a vs'. block_rest _ _ _ _ _ = Abort _ _ ==> _`
        (qspecl_then [`a`, `vs'`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      metis_tac[asm_steps_compose_revert, asm_steps_compose_fault,
                create_safe_prefix_compose])
  >- (qpat_x_assum `!ret vs'. block_rest _ _ _ _ _ = IntRet _ _ ==> _`
        (qspecl_then [`ret`, `vs'`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      rename1 `asm_steps _ _ _ m as1 = AsmOK as2` >>
      qexistsl_tac [`n + m`, `as2`] >>
      rpt conj_tac
      >- metis_tac[]
      >- (strip_tac >>
          MATCH_MP_TAC (Q.SPECL [`n`, `m`, `as`, `as1`] create_safe_prefix_compose) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qpat_x_assum `safe ==> create_safe_prefix _ _ _ m as1` MATCH_MP_TAC >>
          first_assum ACCEPT_TAC)
      >- metis_tac[asm_steps_compose_ok]
      >> first_assum ACCEPT_TAC)
QED

Finalise fn_block_frame_step_resource_at_lo

Theorem fn_block_frame_step_resource_reloc:
  !safe q fuel. gen_fn_sim_at_reloc safe q fuel /\
    gen_fn_frame_sim_at_reloc safe q fuel ==>
    gen_fn_frame_sim_at_reloc safe (OPTION_MAP (\F unit cp prog.
      fn_sim_coefficient unit.cu_context prog * (F unit cp prog + 1)) q) (SUC fuel)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[gen_fn_frame_sim_at_reloc_def] >>
  rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `gen_fn_sim_at_reloc safe q fuel \/
   (lo = SND (compute_label_offsets prog) /\ gen_fn_sim_at safe q fuel)` ASSUME_TAC
  >- simp[] >>
  Q.SUBGOAL_THEN `gen_fn_frame_sim_at_reloc safe q fuel \/
   (lo = SND (compute_label_offsets prog) /\ gen_fn_frame_sim_at safe q fuel)` ASSUME_TAC
  >- simp[] >>
  `code_labels_agree prog lo` by simp[] >>
  drule_all fn_block_frame_step_resource_at_lo >>
  simp[body_result_def, optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF]
QED

Theorem fn_block_frame_step_resource:
  !safe q fuel. gen_fn_sim_at safe q fuel /\ gen_fn_frame_sim_at safe q fuel ==>
    gen_fn_frame_sim_at safe (OPTION_MAP (\F unit cp prog.
      fn_sim_coefficient unit.cu_context prog * (F unit cp prog + 1)) q) (SUC fuel)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[gen_fn_frame_sim_at_def] >>
  rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `gen_fn_sim_at_reloc safe q fuel \/
   (lo = SND (compute_label_offsets prog) /\ gen_fn_sim_at safe q fuel)` ASSUME_TAC
  >- simp[] >>
  Q.SUBGOAL_THEN `gen_fn_frame_sim_at_reloc safe q fuel \/
   (lo = SND (compute_label_offsets prog) /\ gen_fn_frame_sim_at safe q fuel)` ASSUME_TAC
  >- simp[] >>
  `code_labels_agree prog lo` by simp[] >>
  drule_all fn_block_frame_step_resource_at_lo >>
  simp[body_result_def, optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF]
QED

Theorem fn_block_frame_step_reloc:
  !fuel. gen_fn_sim_at_simple_reloc fuel /\ gen_fn_frame_sim_at_simple_reloc fuel ==>
         gen_fn_frame_sim_at_simple_reloc (SUC fuel)
Proof
  mp_tac (Q.SPECL [`F`, `NONE`] fn_block_frame_step_resource_reloc) >>
  simp[GSYM gen_fn_sim_at_simple_reloc_def, GSYM gen_fn_frame_sim_at_simple_reloc_def]
QED


Theorem fn_block_frame_step:
  !fuel. gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel ==>
         gen_fn_frame_sim_at_simple (SUC fuel)
Proof
  mp_tac (Q.SPECL [`F`, `NONE`] fn_block_frame_step_resource) >>
  simp[GSYM gen_fn_sim_at_simple_def, GSYM gen_fn_frame_sim_at_simple_def]
QED
