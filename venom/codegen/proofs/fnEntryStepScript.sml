(*
 * The step of the fuel induction behind venomToAsmProps$gen_fn_simulation:
 * the entry block, run from fn_entry_state_rel, simulated by the code at
 * the start of the function's region.
 *
 * TOP-LEVEL:
 *   fn_entry_block_step - gen_fn_sim_at (SUC fuel) from both function
 *                         theorems at fuel
 *)

Theory fnEntryStep
Ancestors
  fnSimSpec fnFrameSteps fnFrameBoundary fnFrameTerminal gasFrameSim
  genFrameSim fnPlanPlace fnPlanCover fnAliasInv fnPlanLineage frameRel
  venomExecSemantics fnBlockBody fnBlockPlanStatic fnEntryPlan fnEntryParams fnRunFields
  unitShapeDefs contextPlanLayoutProps planSpillBounds contextCodegenRel stackPlanGen
  stackPlanTypes stackOpSim blockSimHelpers

Theorem entry_step_shape[local]:
  !ctx unit Inv cp i fn.
  ctx = unit.cu_context /\ unit_shape_ok unit /\
  codegen_context_obligations Inv ctx cp /\
  i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn ==>
  codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn
Proof
  simp[unit_shape_ok_def, codegen_context_obligations_def, codegen_ready_def,
       listTheory.EVERY_EL, fn_shape_ok_def] >>
  metis_tac[]
QED

Theorem entry_step_spill_bound[local]:
  !ctx cp r lbl param_ops body_ops tail.
  generate_context_plan ctx = SOME cp /\ MEM r cp.cp_regions /\
  r.sr_plan = SOLabel lbl :: param_ops ++ body_ops ++ tail ==>
  !off. MEM (SOSpill off) param_ops ==> off < dimword (:256)
Proof
  rpt strip_tac >>
  drule generate_context_plan_access_bounded >>
  simp[listTheory.EVERY_MEM] >> strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  `region_spill_access r off` by
    simp[region_spill_access_def] >>
  `off + 32 <= r.sr_spill_end` by metis_tac[] >>
  qpat_x_assum `!r. MEM r _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  decide_tac
QED

Theorem entry_step_reachable[local]:
  fn_entry_label fn = SOME lbl ==> fn_reachable fn lbl
Proof
  simp[venomWfTheory.fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]
QED

Theorem entry_step_phi_bound[local]:
  codegen_ready_fn fn ==>
  phi_prefix_length (HD fn.fn_blocks).bb_instructions <=
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions)
Proof
  rw[codegen_ready_fn_def] >>
  `fn.fn_blocks <> []` by
    gvs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
  gvs[block_entries_ready_def, venomInstTheory.entry_block_def,
      listTheory.NULL_EQ] >>
  Cases_on `(HD fn.fn_blocks).bb_instructions` >>
  gvs[livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >> rw[] >>
  simp[phi_prefix_length_def]
QED

Theorem entry_step_run_rest[local]:
  !cp fn vs as ra rest fuel ctx vs_p.
  codegen_ready_fn fn /\ fn_entry_state_rel cp fn vs as ra rest /\
  lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks = SOME (HD fn.fn_blocks) /\
  exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
    exec_block fuel ctx (HD fn.fn_blocks) vs_p ==>
  run_blocks (SUC fuel) ctx fn vs =
    block_rest fuel ctx fn (HD fn.fn_blocks) vs_p
Proof
  rpt gen_tac >> strip_tac >>
  drule entry_run_block >>
  disch_then (qspecl_then [`fuel`, `ctx`, `vs`] assume_tac) >>
  gvs[fn_entry_state_rel_def, run_blocks_unfold, block_rest_def] >>
  Cases_on `exec_block fuel ctx (HD fn.fn_blocks) vs_p` >> simp[]
QED

Theorem entry_step_return[local]:
  !cp fn vs as ra rest fuel ctx ret vs' as'.
  fn_entry_state_rel cp fn vs as ra rest /\
  run_blocks fuel ctx fn vs = IntRet ret vs' /\
  context_memory_rel cp vs'.vs_memory as'.as_memory /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
       read_byte b as'.as_memory = read_byte b as.as_memory) /\
  shared_state_rel vs' as' ==>
  fn_return_state_rel ctx cp fn vs' as as'
Proof
  rpt gen_tac >> strip_tac >>
  drule run_blocks_intret_fields >> strip_tac >>
  gvs[fn_entry_state_rel_def, fn_return_state_rel_def, shared_state_rel_def]
QED

(* A revert forwarding starts at a RETURNDATACOPY, which is not a
   parameter, so it lies past the block's parameter prefix. *)
Theorem get_params_el[local]:
  !l i. i < LENGTH (get_params l) ==>
        i < LENGTH l /\ is_param_opcode (EL i l).inst_opcode
Proof
  Induct >> simp[get_params_def] >> rw[] >> Cases_on `i` >> gvs[]
QED

Theorem revert_forward_pair_past_params[local]:
  !bb i j. revert_forward_pair bb i j ==>
           LENGTH (get_params bb.bb_instructions) <= i
Proof
  rw[revert_forward_pair_def] >> CCONTR_TAC >>
  `i < LENGTH (get_params bb.bb_instructions)` by decide_tac >>
  drule get_params_el >>
  gvs[venomInstTheory.get_instruction_def, AllCaseEqs(), venomInstTheory.is_param_opcode_def]
QED

Theorem entry_body_frame_sim[local]:
  !fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   lbl_ctr ps_end ps0 param_ops ps1 body_ops ps_after pc_bb vs as
   Inv ra pc_ret rest mem0.
  gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
  ctx = unit.cu_context /\ lo = SND (compute_label_offsets prog) /\
  o2pc = build_offset_to_pc prog /\ generate_context_plan ctx = SOME cp /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
  EL i cp.cp_regions = r /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  (!f inst callee_name args callee.
    MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
    MEM inst (fn_insts f) /\
    inst.inst_opcode = INVOKE /\ inst.inst_operands = Label callee_name :: args /\
    lookup_function callee_name ctx.ctx_functions = SOME callee ==>
    fn_has_retpc callee) /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
  (!inst. active_inst fn inst vs ==> Inv ctx fn inst vs) /\
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\
  ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
         (fcg_analyze ctx) fn.fn_name /\
  growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
  ps0 = init_cleanup_plan_state ch growth r.sr_spill_base lbl_ctr /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    r.sr_spill_base lbl_ctr = SOME (r.sr_plan, ps_end) /\
  ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label /\
  vs.vs_current_bb = (HD fn.fn_blocks).bb_label /\
  lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks = SOME (HD fn.fn_blocks) /\
  dfs_block_state liveness dfg cfg fn ps0 (HD fn.fn_blocks).bb_label ps0 /\
  generate_block_plan liveness dfg cfg fn (HD fn.fn_blocks) ps0 =
    SOME (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops, ps_after) /\
  block_plan_state liveness dfg cfg fn (HD fn.fn_blocks) ps0
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1 /\
  generate_block_insts_plan liveness dfg cfg fn (HD fn.fn_blocks).bb_label
    (bb_is_halting (HD fn.fn_blocks))
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
    (LENGTH (HD fn.fn_blocks).bb_instructions) 0
    (non_param_insts (HD fn.fn_blocks)) ps1 = SOME (body_ops, ps_after) /\
  vs.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
  ~vs.vs_call_ctx.cc_static /\
  asm_block_at prog pc_bb (execute_plan cp.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
  as.as_pc = pc_bb + LENGTH (execute_plan cp.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps1 vs as /\
  (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
  (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) ==>
  (!vs'. block_rest fuel ctx fn (HD fn.fn_blocks) vs = Halt vs' ==>
    ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
      venom_asm_terminal_rel vs' as') /\
  (!a vs'. block_rest fuel ctx fn (HD fn.fn_blocks) vs = Abort a vs' ==>
    ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
             (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
      venom_asm_terminal_rel vs' as') /\
  (!ret vs'. block_rest fuel ctx fn (HD fn.fn_blocks) vs = IntRet ret vs' ==>
    ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\ as'.as_pc = pc_ret /\
      as'.as_stack = REVERSE ret.iret_values ++ rest /\
      context_memory_rel cp vs'.vs_memory as'.as_memory /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        read_byte b as'.as_memory = read_byte b mem0) /\ shared_state_rel vs' as')
Proof
  rpt gen_tac >> strip_tac >>
  `fn_reachable fn (HD fn.fn_blocks).bb_label` by
    metis_tac[entry_step_reachable] >>
  drule_all entry_step_shape >> strip_tac >>
  drule entry_step_phi_bound >> strip_tac >>
  `lineage_state liveness dfg cfg fn ps0 (HD fn.fn_blocks).bb_label ps0` by
    metis_tac[lineage_state_rules] >>
  `!i j. revert_forward_pair (HD fn.fn_blocks) i j ==>
         LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <= i \/
         j < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    metis_tac[revert_forward_pair_past_params] >>
  `!xs L. ?prefixL prefixD core.
     xs = prefixL ++ core /\ xs = prefixD ++ core /\
     (!v. MEM v L ==> ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)` by
    (rpt gen_tac >> qexistsl_tac [`[]`, `[]`, `xs`] >> simp[]) >>
  irule block_body_frame_sim >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC)) >>
  conj_tac >- simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`rpolicy`, `unit`] >> simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `Inv` >> simp[]) >>
  qexistsl_tac [`SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops`,
    `cfg`, `ch`, `dfg`, `r.sr_plan`, `growth`, `ps0.ps_cleanup_height`,
    `i`, `LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`, `lbl_ctr`,
    `liveness`, `pc_bb`, `param_ops`, `ps0.ps_cleanup_promised`, `ps1`,
    `ps_after`, `ps0`, `ps_after`, `ps_end`, `ps0`, `r`, `ra`, `body_ops`,
    `r.sr_spill_base`] >>
  gvs[init_cleanup_plan_state_def, init_plan_state_def] >>
  first_assum ACCEPT_TAC
QED

(* As for fn_block_frame_step, but for the entry block, which
   gen_fn_frame_sim_at excludes.

   Why it should hold: region i's plan is the function planner's output
   for some label counter (fnEntryPlan$region_fn_plan) and starts with
   the entry block's code, planned from the initial state ps0: its label,
   its parameter code, then its instructions' code
   (fnEntryPlan$entry_block_plan), and the premise's asm_block_at puts
   that code at as.as_pc.  The entry block has no PHIs
   (fnEntryParams$entry_run_block), and the parameter prefix turns
   fn_entry_state_rel into fn_frame_inv at ps1 with mem0 = as.as_memory
   (fnEntryParams$entry_prefix_frame_sim, which also gives Inv, the
   labels and the alias premise at the state vs_p after it).  So
   run_blocks (SUC fuel) from vs is block_rest from vs_p, which
   fnBlockBody$block_body_frame_sim simulates (bb = HD fn.fn_blocks,
   ps_l = ps_dfs = ps0 with its own cleanup fields, k = the parameter
   count, ps = ps1, prefix_ops = the parameter code); its steps are added
   to the prefix's.  Its IntRet clause gives fn_return_state_rel: the
   spill-byte clause is the frame's against mem0, and the call, tx and
   block context, code and prev-hash clauses hold because the run never
   changes those fields (fnRunFields$run_blocks_intret_fields) and
   fn_entry_state_rel equates them with as's. *)
Theorem fn_entry_block_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel ==>
         gen_fn_sim_at (SUC fuel)
Proof
  gen_tac >> strip_tac >>
  rewrite_tac[gen_fn_sim_at_def] >> rpt gen_tac >> strip_tac >>
  drule_all entry_step_shape >> strip_tac >>
  drule_all region_fn_plan >> strip_tac >>
  drule_all entry_block_plan >> strip_tac >>
  qabbrev_tac `lbl = (HD fn.fn_blocks).bb_label` >>
  rename1 `generate_context_plan ctx = SOME cplan` >>
  qabbrev_tac `fmp = cplan.cp_initial_fmp` >>
  `!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)` by
    metis_tac[entry_step_spill_bound] >>
  `asm_block_at prog as.as_pc
     (execute_plan fmp (SOLabel lbl :: param_ops ++ body_ops)) /\
   asm_block_at prog as.as_pc (execute_plan fmp (SOLabel lbl :: param_ops))` by
    (qpat_x_assum `asm_block_at _ _ (execute_plan _ r.sr_plan)` mp_tac >>
     qpat_assum `r.sr_plan = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[execute_plan_append, asm_block_at_append] >>
     rpt strip_tac >> fs[]) >>
  `ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  qspecl_then [`fuel`, `ctx`, `cplan`, `lo`, `o2pc`, `prog`,
    `liveness_analyze fn`, `dfg_build_function fn`, `fn`,
    `cleanup_caller_height (LENGTH ctx.ctx_functions) ctx (fcg_analyze ctx)
       fn.fn_name`,
    `cleanup_growth_table ctx (fcg_analyze ctx)`, `r.sr_spill_base`,
    `lbl_ctr`,
    `init_cleanup_plan_state
       (cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
          (fcg_analyze ctx) fn.fn_name)
       (cleanup_growth_table ctx (fcg_analyze ctx)) r.sr_spill_base lbl_ctr`,
    `param_ops`, `ps1`, `r`, `vs`, `as`, `ra`, `rest`, `Inv`]
    mp_tac entry_prefix_frame_sim >>
  impl_tac >- (unabbrev_all_tac >> simp[]) >>
  strip_tac >>
  `run_blocks (SUC fuel) ctx fn vs = block_rest fuel ctx fn (HD fn.fn_blocks) vs_p`
    by (irule entry_step_run_rest >> unabbrev_all_tac >> metis_tac[]) >>
  qspecl_then [`fuel`, `rpolicy`, `unit`, `cplan`, `prog`, `ctx`, `lo`, `o2pc`,
    `i`, `fn`, `r`, `liveness_analyze fn`, `dfg_build_function fn`,
    `cfg_analyze fn`,
    `cleanup_caller_height (LENGTH ctx.ctx_functions) ctx (fcg_analyze ctx)
       fn.fn_name`,
    `cleanup_growth_table ctx (fcg_analyze ctx)`, `lbl_ctr`, `ps_end`,
    `init_cleanup_plan_state
       (cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
          (fcg_analyze ctx) fn.fn_name)
       (cleanup_growth_table ctx (fcg_analyze ctx)) r.sr_spill_base lbl_ctr`,
    `param_ops`, `ps1`, `body_ops`, `ps_after`, `as.as_pc`, `vs_p`, `as'`,
    `Inv`, `ra`, `pc_ret`, `rest`, `as.as_memory`]
    mp_tac entry_body_frame_sim >>
  impl_tac
  >- (unabbrev_all_tac >> gvs[fn_entry_state_rel_def] >> metis_tac[]) >>
  strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `!vs'. block_rest _ _ _ _ _ = Halt _ ==> _`
        (qspec_then `vs'` mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      metis_tac[asm_steps_compose_halt])
  >- (qpat_x_assum `!a vs'. block_rest _ _ _ _ _ = Abort _ _ ==> _`
        (qspecl_then [`a`, `vs'`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      metis_tac[asm_steps_compose_revert, asm_steps_compose_fault])
  >- (qpat_x_assum `!ret vs'. block_rest _ _ _ _ _ = IntRet _ _ ==> _`
        (qspecl_then [`ret`, `vs'`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      rename1 `asm_steps _ _ _ m as' = AsmOK as2` >>
      qexistsl_tac [`n + m`, `as2`] >>
      rpt conj_tac
      >- metis_tac[asm_steps_compose_ok]
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (irule entry_step_return >> metis_tac[]))
QED
