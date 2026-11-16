(*
 * One lemma per instruction class for fnBlockBody$block_body_frame_sim,
 * at instruction k of block bb under fnBlockBodySteps$body_inv:
 *
 *   body_ordinary_ok, body_gas_ok, body_invoke_step (OK case)
 *       - the instruction's code runs and fn_frame_inv holds after it;
 *         body_inv_advance then moves the invariant to k + 1
 *   body_jmp_step, body_jnz_step
 *       - the rest of the run, from the successor (body_jump_continue)
 *   body_halt_step, body_abort_step, body_invoke_step, body_ret_step
 *       - the run ends here
 *   body_revert_step
 *       - a revert forwarding from k runs the block's rest as one step
 *
 * The operand-count and LOG topic-count facts, and the revert
 * forwarding's no-spill fact, are hypotheses where they are consumed.
 *)

Theory fnBlockBodyClasses
Ancestors
  fnBlockBodySteps fnBlockBodyHelpers fnBlockPlanStatic fnAliasStep
  fnFrameStepsRevertForwardDeep fnFrameDeep fnSimSpec fnPlanPlace
  fnPlanCover fnPlanPlaceDfsBlock fnPlanLineage fnLineageStatic
  fnPlanPrefix opcodeClass cfgAnalysisProps
  stepWriteFootprintForward asmTargetSafety codegen allocMono
  unitShapeDefs contextCodegenRel codegenRel frameRel stackPlanGen
  venomExecProps venomInstProps venomExecSemantics venomWf venomInst
  venomState stackOpSim asmSem dfgDefs list rich_list arithmetic
  finite_map option relation genFrameSim asmIR stackModel venomEffects
  stackPlanTypes planExec reorderSim fnFrameDeepInst fnFrameDeepGas
  fnFrameDeepHalt fnFrameDeepAbort fnFrameDeepRet fnFrameDeepJmp
  fnFrameDeepJnz fnFrameDeepInvoke

fun is_body_inv th =
  (fst (dest_const (fst (strip_comb (concl th)))) = "body_inv")
  handle HOL_ERR _ => false;

val unpack_inv =
  first_assum (strip_assume_tac o REWRITE_RULE [body_inv_def] o
               assert is_body_inv);

(* The facts every instruction lemma reads, as assumptions. *)
fun is_body_plan_inv th =
  (fst (dest_const (fst (strip_comb (concl th)))) = "body_plan_inv")
  handle HOL_ERR _ => false;

val unpack_plan_inv =
  first_assum (strip_assume_tac o REWRITE_RULE [body_plan_inv_def] o
               assert is_body_plan_inv);

(* The facts every instruction lemma reads, as assumptions. *)
val gather_tac =
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule body_inv_equiv >> disch_then drule >> disch_then drule >>
  strip_tac >> unpack_inv;

val gather_plan_tac =
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >>
  strip_tac >> unpack_plan_inv;

val phi_tac =
  rpt strip_tac >> qpat_x_assum `inst.inst_opcode = PHI` mp_tac >>
  qpat_x_assum `inst.inst_opcode <> PHI` mp_tac >> simp[];

(* ===== The terminator's successor ===== *)

val unpack_plan_inv_reloc =
  qhdtm_assum `body_plan_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_reloc_def]);

Theorem body_plan_terminator_last_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') ==>
    ps' = ps_after
Proof
  strip_tac >> drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_step_reloc >> strip_tac >>
  `k = PRE (LENGTH bb.bb_instructions)` by
    (qpat_x_assum `bb_well_formed bb`
       (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
     qpat_x_assum `!i. i < LENGTH _ /\ is_terminator _ ==> _`
       (qspec_then `k` mp_tac) >>
     fs[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME (ops, ps')`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `DROP (SUC k - LENGTH (get_params bb.bb_instructions))
     (non_param_insts bb) = []` by
    (qpat_x_assum `non_param_insts bb = _` SUBST1_TAC >>
     irule DROP_LENGTH_TOO_LONG >> fs[LENGTH_DROP]) >>
  qpat_x_assum `DROP (SUC k - _) _ = []`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ [] _ = _` mp_tac >>
  simp[Once generate_block_insts_plan_def] >> fs[]
QED

Theorem body_terminator_last_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') ==>
    ps' = ps_after
Proof
  strip_tac >> drule body_inv_plan_reloc >> strip_tac >>
  drule_all body_plan_terminator_last_reloc >> disch_then ACCEPT_TAC
QED

Theorem body_plan_terminator_last:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') ==>
    ps' = ps_after
Proof
  pure_rewrite_tac [body_plan_inv_reloc_specialize] >>
  metis_tac[body_plan_terminator_last_reloc]
QED

Theorem body_terminator_last:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') ==>
    ps' = ps_after
Proof
  pure_rewrite_tac [body_inv_reloc_specialize] >>
  metis_tac[body_terminator_last_reloc]
QED

Theorem body_plan_succ_placed_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
    ?tbb ps_tdfs tops tafter toff tpc.
      lookup_block t fn.fn_blocks = SOME tbb /\ tbb.bb_label = t /\
      fn_reachable fn t /\ tbb <> HD fn.fn_blocks /\
      MEM t (cfg_succs_of cfg bb.bb_label) /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs /\
      generate_block_plan liveness dfg cfg fn tbb ps_tdfs =
        SOME (tops, tafter) /\
      FLOOKUP lo t = SOME toff /\ toff < dimword (:256) /\
      FLOOKUP o2pc toff = SOME tpc /\
      asm_block_at prog tpc (execute_plan cpl.cp_initial_fmp tops) /\
      ps_tdfs.ps_alloc.sa_spill_base = spill_base /\
      ps_tdfs.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule body_plan_inv_facts_reloc >> strip_tac >>
  unpack_plan_inv_reloc >>
  drule_all body_succ_block >> strip_tac >>
  drule_all fnPlanCoverTheory.dfs_block_state_reachable >> strip_tac >>
  qpat_x_assum `spill_base = _` SUBST_ALL_TAC >>
  qpat_x_assum `fn_ops = r.sr_plan` SUBST_ALL_TAC >>
  drule_all dfs_block_code_placed_reloc >> strip_tac >>
  drule_all body_dfs_state_region >> strip_tac >>
  qexistsl_tac [`tbb`, `ps_dfs'`, `block_ops'`, `ps_dfs_after'`, `off`, `pc`] >>
  gvs[]
QED

Theorem body_succ_placed_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
    ?tbb ps_tdfs tops tafter toff tpc.
      lookup_block t fn.fn_blocks = SOME tbb /\ tbb.bb_label = t /\
      fn_reachable fn t /\ tbb <> HD fn.fn_blocks /\
      MEM t (cfg_succs_of cfg bb.bb_label) /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs /\
      generate_block_plan liveness dfg cfg fn tbb ps_tdfs =
        SOME (tops, tafter) /\
      FLOOKUP lo t = SOME toff /\ toff < dimword (:256) /\
      FLOOKUP o2pc toff = SOME tpc /\
      asm_block_at prog tpc (execute_plan cpl.cp_initial_fmp tops) /\
      ps_tdfs.ps_alloc.sa_spill_base = spill_base /\
      ps_tdfs.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule body_inv_plan_reloc >> strip_tac >>
  drule_all body_plan_succ_placed_reloc >> disch_then ACCEPT_TAC
QED

Theorem body_plan_succ_placed:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
    ?tbb ps_tdfs tops tafter toff tpc.
      lookup_block t fn.fn_blocks = SOME tbb /\ tbb.bb_label = t /\
      fn_reachable fn t /\ tbb <> HD fn.fn_blocks /\
      MEM t (cfg_succs_of cfg bb.bb_label) /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs /\
      generate_block_plan liveness dfg cfg fn tbb ps_tdfs =
        SOME (tops, tafter) /\
      FLOOKUP lo t = SOME toff /\ toff < dimword (:256) /\
      FLOOKUP o2pc toff = SOME tpc /\
      asm_block_at prog tpc (execute_plan cpl.cp_initial_fmp tops) /\
      ps_tdfs.ps_alloc.sa_spill_base = spill_base /\
      ps_tdfs.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  pure_rewrite_tac [body_plan_inv_reloc_specialize] >>
  metis_tac[body_plan_succ_placed_reloc]
QED

Theorem body_succ_placed:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
    ?tbb ps_tdfs tops tafter toff tpc.
      lookup_block t fn.fn_blocks = SOME tbb /\ tbb.bb_label = t /\
      fn_reachable fn t /\ tbb <> HD fn.fn_blocks /\
      MEM t (cfg_succs_of cfg bb.bb_label) /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs /\
      generate_block_plan liveness dfg cfg fn tbb ps_tdfs =
        SOME (tops, tafter) /\
      FLOOKUP lo t = SOME toff /\ toff < dimword (:256) /\
      FLOOKUP o2pc toff = SOME tpc /\
      asm_block_at prog tpc (execute_plan cpl.cp_initial_fmp tops) /\
      ps_tdfs.ps_alloc.sa_spill_base = spill_base /\
      ps_tdfs.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  pure_rewrite_tac [body_inv_reloc_specialize] >>
  metis_tac[body_succ_placed_reloc]
QED

(* ===== The callee of an INVOKE ===== *)

Theorem body_callee_placed_reloc:
  !rpolicy unit cpl prog ctx lo o2pc Inv nm.
    ctx = unit.cu_context /\
    code_labels_agree prog lo /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cpl ==>
    !j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
      ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
               FLOOKUP o2pc off = SOME pc /\
               asm_block_at prog pc
                 (execute_plan cpl.cp_initial_fmp (EL j cpl.cp_regions).sr_plan)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `fn_entry_label (EL j ctx.ctx_functions) =
     SOME (EL j ctx.ctx_functions).fn_name` by
    (irule (cj 4 body_fn_shape) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `(HD (EL j ctx.ctx_functions).fn_blocks).bb_label = nm` by
    (qpat_x_assum `fn_entry_label _ = _` mp_tac >>
     simp[fn_entry_label_def, entry_block_def] >>
     Cases_on `(EL j ctx.ctx_functions).fn_blocks` >> simp[]) >>
  qpat_x_assum `(HD _).bb_label = nm` (SUBST1_TAC o SYM) >>
  irule fn_region_placed_reloc >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem body_callee_placed:
  !rpolicy unit cpl prog ctx lo o2pc Inv nm.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cpl ==>
    !j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
      ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
               FLOOKUP o2pc off = SOME pc /\
               asm_block_at prog pc
                 (execute_plan cpl.cp_initial_fmp (EL j cpl.cp_regions).sr_plan)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule body_callee_placed_reloc >>
  rpt (goal_assum (drule_at Any)) >> gvs[] >> metis_tac[]
QED

Theorem body_callee_sim_resource:
  !safe q fuel rpolicy unit cpl prog ctx lo o2pc Inv.
    gen_fn_sim_at safe q fuel /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    codegen_context_obligations Inv ctx cpl /\
    reachability_closed Inv ctx ==>
    !j callee rj cvs cas cra crest cpc.
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
          ?n as'. cost_le (OPTION_MAP (\F. F unit cpl prog) q) n /\
                  asm_steps lo o2pc prog n cas = AsmHalt as' /\
                  venom_asm_terminal_rel vs' as' /\
                  (safe ==> create_safe_prefix lo o2pc prog n cas)) /\
       (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
          ?n as'. cost_le (OPTION_MAP (\F. F unit cpl prog) q) n /\
                  ((a = Revert_abort /\
                    asm_steps lo o2pc prog n cas = AsmRevert as') \/
                   (a = ExHalt_abort /\
                    asm_steps lo o2pc prog n cas = AsmFault as')) /\
                  venom_asm_terminal_rel vs' as' /\
                  (safe ==> create_safe_prefix lo o2pc prog n cas)) /\
       (!ret vs'. run_blocks fuel ctx callee cvs = IntRet ret vs' ==>
          ?n as'. cost_le (OPTION_MAP (\F. F unit cpl prog) q) n /\
                  asm_steps lo o2pc prog n cas = AsmOK as' /\
                  as'.as_pc = cpc /\
                  as'.as_stack = REVERSE ret.iret_values ++ crest /\
                  fn_return_state_rel ctx cpl callee vs' cas as' /\
                  (safe ==> create_safe_prefix lo o2pc prog n cas))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `gen_fn_sim_at _ _ _`
    (mp_tac o REWRITE_RULE [gen_fn_sim_at_def]) >>
  disch_then (qspecl_then [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`,
                           `o2pc`, `j`, `rj`, `callee`, `cvs`, `cas`, `Inv`,
                           `cra`, `cpc`, `crest`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`n`, `as'`] >> simp[]
QED


Theorem body_callee_sim:
  !fuel rpolicy unit cpl prog ctx lo o2pc Inv.
    gen_fn_sim_at_simple fuel /\
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    codegen_context_obligations Inv ctx cpl /\
    reachability_closed Inv ctx ==>
    !j callee rj cvs cas cra crest cpc.
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
          ?n as'. ((a = Revert_abort /\
                    asm_steps lo o2pc prog n cas = AsmRevert as') \/
                   (a = ExHalt_abort /\
                    asm_steps lo o2pc prog n cas = AsmFault as')) /\
                  venom_asm_terminal_rel vs' as') /\
       (!ret vs'. run_blocks fuel ctx callee cvs = IntRet ret vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmOK as' /\
                  as'.as_pc = cpc /\
                  as'.as_stack = REVERSE ret.iret_values ++ crest /\
                  fn_return_state_rel ctx cpl callee vs' cas as')
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all (SRULE [GSYM gen_fn_sim_at_simple_def, cost_le_def]
    (Q.SPECL [`F`, `NONE`] body_callee_sim_resource)) >>
  disch_then irule >> simp[]
QED

(* ===== Moving the invariant past an instruction ===== *)

Theorem body_plan_advance_core_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    vs1.vs_labels = vs.vs_labels /\ vs1.vs_call_ctx = vs.vs_call_ctx /\
    vs1.vs_current_bb = vs.vs_current_bb /\
    (!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) ==>
    body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after (prefix_ops ++ ops) rest' (SUC k) ps'
      pc0 (vs1 with vs_inst_idx := SUC k) as1 ra pc_ret rest mem0
Proof
  strip_tac >> drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule_all body_plan_inv_static_reloc >> strip_tac >> unpack_plan_inv_reloc >>
  `execute_plan cpl.cp_initial_fmp (SOLabel bb.bb_label :: (prefix_ops ++ ops)) =
   execute_plan cpl.cp_initial_fmp (SOLabel bb.bb_label :: prefix_ops) ++
   execute_plan cpl.cp_initial_fmp ops` by
    REWRITE_TAC [GSYM execute_plan_append, APPEND] >>
  Q.SUBGOAL_THEN `?prefixL prefixD core.
     ps_after.ps_stack = prefixL ++ core /\
     ps_dfs_after.ps_stack = prefixD ++ core /\
     (!v. MEM v (live_vars_at liveness bb.bb_label
                   (LENGTH bb.bb_instructions)) ==>
        ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)` ASSUME_TAC
  >- (qexistsl_tac [`prefixL`, `prefixD`, `core`] >> simp[]) >>
  PURE_REWRITE_TAC [body_plan_inv_reloc_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC)
  >~ [`FLOOKUP (_ with vs_inst_idx := _).vs_labels`]
  >- (simp[] >> qpat_x_assum `vs1.vs_labels = _` SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  >~ [`lookup_block (_ with vs_inst_idx := _).vs_current_bb`]
  >- (simp[] >> qpat_x_assum `vs1.vs_current_bb = _` SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  >~ [`block_plan_state`]
  >- (irule block_plan_state_step >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >> qexistsl_tac [`ops`, `ps`] >>
      qpat_x_assum `EL k _ = inst` SUBST1_TAC >>
      conj_tac >> first_assum ACCEPT_TAC)
  >~ [`block_ops = _`]
  >- (qpat_x_assum `block_ops = _` SUBST1_TAC >>
      qpat_x_assum `rest_ops = _` SUBST1_TAC >> simp[])
  >~ [`phi_prefix_length`]
  >- (qpat_x_assum `phi_prefix_length _ <= k` mp_tac >> simp[])
  >~ [`revert_forward_pair`]
  >- (rpt strip_tac >>
      qpat_x_assum `!i j. revert_forward_pair bb i j ==> _` drule >>
      rename1 `revert_forward_pair bb a b` >>
      `a <> k` by
        (strip_tac >> qpat_x_assum `a = k` SUBST_ALL_TAC >> res_tac) >> simp[])
  >~ [`(_ with vs_inst_idx := _).vs_inst_idx`] >- simp[]
  >~ [`as1.as_pc = _`]
  >- (qpat_x_assum `execute_plan _ (SOLabel _ :: (_ ++ _)) = _` SUBST1_TAC >>
      qpat_x_assum `as1.as_pc = _` SUBST1_TAC >>
      qpat_x_assum `as.as_pc = _` SUBST1_TAC >> simp[])
  >~ [`fn_frame_inv`]
  >- (REWRITE_TAC [fn_frame_inv_inst_idx] >> first_assum ACCEPT_TAC)
  >~ [`operand_val`]
  >- (REWRITE_TAC [frame_view_inst_idx, operand_val_inst_idx] >> first_assum ACCEPT_TAC)
QED

Theorem body_plan_advance_core:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    vs1.vs_labels = vs.vs_labels /\ vs1.vs_call_ctx = vs.vs_call_ctx /\
    vs1.vs_current_bb = vs.vs_current_bb /\
    (!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) ==>
    body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after (prefix_ops ++ ops) rest' (SUC k) ps'
      pc0 (vs1 with vs_inst_idx := SUC k) as1 ra pc_ret rest mem0
Proof
  pure_rewrite_tac [body_plan_inv_reloc_specialize] >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  drule_all body_plan_advance_core_reloc >> simp[]
QED

Theorem body_plan_advance_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    step_inst fuel ctx inst vs = OK vs1 /\
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) ==>
    body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after (prefix_ops ++ ops) rest' (SUC k) ps'
      pc0 (vs1 with vs_inst_idx := SUC k) as1 ra pc_ret rest mem0
Proof
  strip_tac >> drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule_all body_plan_inv_static_reloc >> strip_tac >> unpack_plan_inv_reloc >>
  `vs1.vs_labels = vs.vs_labels /\ vs1.vs_call_ctx = vs.vs_call_ctx /\
   vs1.vs_current_bb = vs.vs_current_bb` by
    metis_tac[step_preserves_labels, step_preserves_call_ctx,
              step_preserves_control_flow] >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
     operand_val (frame_view fn ra vs1) lo at =
     operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)` by
    ((rpt strip_tac >>
     drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`) alias_step_preserve >>
     disch_then irule >> simp[] >> rpt (goal_assum (drule_at Any)) >> simp[] >> (metis_tac[]))) >>
  drule_all body_plan_advance_core_reloc >> simp[]
QED

Theorem body_plan_advance:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    step_inst fuel ctx inst vs = OK vs1 /\
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) ==>
    body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after (prefix_ops ++ ops) rest' (SUC k) ps'
      pc0 (vs1 with vs_inst_idx := SUC k) as1 ra pc_ret rest mem0
Proof
  pure_rewrite_tac [body_plan_inv_reloc_specialize] >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  drule_all body_plan_advance_reloc >> simp[]
QED

Theorem body_inv_advance_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    step_inst fuel ctx inst vs = OK vs1 /\
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) ==>
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after (prefix_ops ++ ops) rest' (SUC k) ps'
      pc0 (vs1 with vs_inst_idx := SUC k) as1 Inv ra pc_ret rest mem0
Proof
  pure_rewrite_tac [body_inv_bundle_reloc] >> strip_tac >>
  reverse conj_tac
  >- (drule_all body_plan_inv_inst_reloc >> strip_tac >> unpack_plan_inv_reloc >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `reachability_closed _ _`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [reachability_closed_def]) >>
      disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
      disch_then assume_tac >> gvs[] >> first_x_assum irule >> simp[]) >>
  drule_all body_plan_advance_reloc >> simp[]
QED

Theorem body_inv_advance:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    step_inst fuel ctx inst vs = OK vs1 /\
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) ==>
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after (prefix_ops ++ ops) rest' (SUC k) ps'
      pc0 (vs1 with vs_inst_idx := SUC k) as1 Inv ra pc_ret rest mem0
Proof
  pure_rewrite_tac [body_inv_reloc_specialize] >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  drule_all body_inv_advance_reloc >> simp[]
QED

(* ===== Results ===== *)

Theorem body_result_resource_halt:
  (?n as'. cost_le b n /\
           (safe ==> create_safe_prefix lo o2pc prog n as) /\ asm_steps lo o2pc prog n as = AsmHalt as' /\
           venom_asm_terminal_rel vs as') ==>
  body_result safe b lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Halt vs)
Proof
  rw[body_result_def] >> metis_tac[]
QED


Theorem body_result_resource_abort:
  (?n as'. cost_le b n /\
           (safe ==> create_safe_prefix lo o2pc prog n as) /\
           ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
            (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
           venom_asm_terminal_rel vs as') ==>
  body_result safe b lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Abort a vs)
Proof
  rw[body_result_def] >> metis_tac[]
QED


Theorem body_result_resource_intret:
  (?n as'. cost_le b n /\
           (safe ==> create_safe_prefix lo o2pc prog n as) /\ asm_steps lo o2pc prog n as = AsmOK as' /\
           as'.as_pc = pc_ret /\
           as'.as_stack = REVERSE ret.iret_values ++ rest /\
           context_memory_rel cpl vs.vs_memory as'.as_memory /\
           (!b. context_spill_byte cpl b /\
                ~closure_spill_byte ctx cpl fn.fn_name b ==>
                read_byte b as'.as_memory = read_byte b mem0) /\
           shared_state_rel vs as') ==>
  body_result safe b lo o2pc prog cpl ctx fn mem0 pc_ret rest as (IntRet ret vs)
Proof
  rw[body_result_def] >> metis_tac[]
QED


Theorem body_result_halt:
  (?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
           venom_asm_terminal_rel vs as') ==>
  body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Halt vs)
Proof
  mp_tac (Q.INST [`safe` |-> `F`, `b` |-> `NONE`]
    body_result_resource_halt) >> simp[GSYM body_result_simple_def, cost_le_def]
QED

Theorem body_result_abort:
  (?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
            (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
           venom_asm_terminal_rel vs as') ==>
  body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Abort a vs)
Proof
  mp_tac (Q.INST [`safe` |-> `F`, `b` |-> `NONE`]
    body_result_resource_abort) >> simp[GSYM body_result_simple_def, cost_le_def]
QED

Theorem body_result_intret:
  (?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
           as'.as_pc = pc_ret /\
           as'.as_stack = REVERSE ret.iret_values ++ rest /\
           context_memory_rel cpl vs.vs_memory as'.as_memory /\
           (!b. context_spill_byte cpl b /\
                ~closure_spill_byte ctx cpl fn.fn_name b ==>
                read_byte b as'.as_memory = read_byte b mem0) /\
           shared_state_rel vs as') ==>
  body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (IntRet ret vs)
Proof
  mp_tac (Q.INST [`safe` |-> `F`, `b` |-> `NONE`]
    body_result_resource_intret) >> simp[GSYM body_result_simple_def, cost_le_def]
QED

(* ===== Instructions that don't end the block ===== *)

(* The arguments of the fnFrameDeep instruction lemmas at instruction k. *)
val deep_args =
  [`fuel`, `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
   `fn`, `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
   `bb_is_halting bb`,
   `k + 1 < LENGTH bb.bb_instructions /\
    is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
   `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `r`, `ra`,
   `rest`, `mem0`];

(* Relocated instruction facts, local to the ordinary and GAS consumers. *)
local
  val gather_reloc_tac =
    drule body_inv_facts_reloc >> strip_tac >>
    drule_all body_inv_inst_reloc >> strip_tac >>
    drule_all body_inv_step_reloc >> strip_tac >>
    drule_all body_inv_static_reloc >> strip_tac >>
    drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >>
    strip_tac >> qhdtm_assum `body_inv_reloc`
      (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]);
  val gather_plan_reloc_tac =
    drule body_plan_inv_facts_reloc >> strip_tac >>
    drule_all body_plan_inv_inst_reloc >> strip_tac >>
    drule_all body_plan_inv_step_reloc >> strip_tac >>
    drule_all body_plan_inv_static_reloc >> strip_tac >>
    drule body_plan_inv_equiv_reloc >> disch_then drule >> disch_then drule >>
    strip_tac >> unpack_plan_inv_reloc;
  val step_reloc_tac =
    drule body_inv_not_in_rf_reloc >> disch_then drule >> strip_tac >>
    drule_all body_inv_memory_reloc >> strip_tac >>
    `!e. step_inst fuel ctx inst vs <> Error e` by
      (qpat_x_assum `step_inst fuel ctx inst vs = _` (fn th => simp[th])) >>
    drule body_inv_label_resolve_reloc >> disch_then drule >> disch_then drule >>
    disch_then drule >> disch_then drule >> strip_tac;
  val step_plan_reloc_tac =
    `!e. step_inst fuel ctx inst vs <> Error e` by
      (qpat_x_assum `step_inst fuel ctx inst vs = _` (fn th => simp[th])) >>
    drule body_plan_inv_label_resolve_reloc >> disch_then drule >> disch_then drule >>
    disch_then drule >> disch_then drule >> strip_tac;
in

Theorem body_plan_ordinary_ok_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    source_memory_reads_disjoint cpl inst vs /\
    context_source_memory_writes_disjoint cpl inst vs /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)
Proof
  strip_tac >> gather_plan_reloc_tac >> step_plan_reloc_tac >>
  qspecl_then deep_args mp_tac gen_inst_frame_sim_deep_reloc >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`ASSERT`] >- (strip_tac >> first_assum ACCEPT_TAC)
      >~ [`stack_get_phi_depth`] >- phi_tac) >>
  disch_then drule >> strip_tac >>
  qexistsl_tac [`ops`, `ps'`, `rest'`, `n`, `as'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_plan_ordinary_ok:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    source_memory_reads_disjoint cpl inst vs /\
    context_source_memory_writes_disjoint cpl inst vs /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)
Proof
  strip_tac >>
  qhdtm_x_assum `body_plan_inv`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_reloc_specialize]) >>
  drule_all body_plan_ordinary_ok_reloc >> simp[]
QED

Theorem body_ordinary_ok_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      n <= LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
      (inst_create_size_ok inst vs ==> create_safe_prefix lo o2pc prog n as)
Proof
  strip_tac >> gather_reloc_tac >> step_reloc_tac >>
  qspecl_then deep_args mp_tac gen_inst_frame_sim_deep_reloc >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`ASSERT`] >- (strip_tac >> first_assum ACCEPT_TAC)
      >~ [`stack_get_phi_depth`] >- phi_tac) >>
  disch_then drule >> strip_tac >>
  qexistsl_tac [`ops`, `ps'`, `rest'`, `n`, `as'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_ordinary_ok:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      n <= LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
      (inst_create_size_ok inst vs ==> create_safe_prefix lo o2pc prog n as)
Proof
  strip_tac >>
  qhdtm_x_assum `body_inv`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_specialize]) >>
  drule_all body_ordinary_ok_reloc >> simp[]
QED

val gas_tac =
  qpat_x_assum `inst.inst_opcode = GAS`
    (fn th => simp[th, is_terminator_def]);

Theorem body_plan_gas_ok_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    source_memory_reads_disjoint cpl inst vs /\
    context_source_memory_writes_disjoint cpl inst vs /\
    inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)
Proof
  strip_tac >> gather_plan_reloc_tac >>
  `inst.inst_opcode <> INVOKE` by gas_tac >> step_plan_reloc_tac >>
  `context_spill_step_safe cpl vs vs1` by
    metis_tac[stepWriteFootprintBaseTheory.noninvoke_spill_step_safe] >>
  qspecl_then deep_args mp_tac gas_inst_frame_sim_owned_deep_reloc >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`stack_get_phi_depth`] >- phi_tac >> gas_tac) >>
  disch_then (qspec_then `vs1` mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`ops`, `ps'`, `rest'`, `n`, `as'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_plan_gas_ok:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    source_memory_reads_disjoint cpl inst vs /\
    context_source_memory_writes_disjoint cpl inst vs /\
    inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)
Proof
  strip_tac >>
  qhdtm_x_assum `body_plan_inv`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_reloc_specialize]) >>
  drule_all body_plan_gas_ok_reloc >> simp[]
QED

Theorem body_gas_ok_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      n <= LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
      create_safe_prefix lo o2pc prog n as
Proof
  strip_tac >> gather_reloc_tac >>
  `inst.inst_opcode <> INVOKE` by gas_tac >> step_reloc_tac >>
  `context_spill_step_safe cpl vs vs1` by
    (qpat_x_assum `!fuel vs1. _ ==> context_spill_step_safe _ _ _` irule >>
     qexists_tac `fuel` >> first_assum ACCEPT_TAC) >>
  qspecl_then deep_args mp_tac gas_inst_frame_sim_owned_deep_exact_reloc >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`stack_get_phi_depth`] >- phi_tac >> gas_tac) >>
  disch_then (qspec_then `vs1` mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`ops`, `ps'`, `rest'`,
    `LENGTH (execute_plan cpl.cp_initial_fmp ops)`, `as'`] >>
  simp[]
QED

Theorem body_gas_ok:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      n <= LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
      create_safe_prefix lo o2pc prog n as
Proof
  strip_tac >>
  qhdtm_x_assum `body_inv`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_specialize]) >>
  drule_all body_gas_ok_reloc >> simp[]
QED

end

(* ===== Instructions that end the run ===== *)

local
  fun terminal_inv name th =
    fst (dest_const (fst (strip_comb (concl th)))) = name
    handle HOL_ERR _ => false;
  val terminal_gather_tac =
    drule body_inv_facts_reloc >> strip_tac >>
    drule_all body_inv_inst_reloc >> strip_tac >>
    drule_all body_inv_step_reloc >> strip_tac >>
    drule_all body_inv_static_reloc >> strip_tac >>
    drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >>
    strip_tac >>
    first_assum (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def] o
                 assert (terminal_inv "body_inv_reloc"));
  val terminal_plan_gather_tac =
    drule body_plan_inv_facts_reloc >> strip_tac >>
    drule_all body_plan_inv_inst_reloc >> strip_tac >>
    drule_all body_plan_inv_step_reloc >> strip_tac >>
    drule_all body_plan_inv_static_reloc >> strip_tac >>
    drule body_plan_inv_equiv_reloc >> disch_then drule >> disch_then drule >>
    strip_tac >>
    first_assum (strip_assume_tac o REWRITE_RULE [body_plan_inv_reloc_def] o
                 assert (terminal_inv "body_plan_inv_reloc"));
  val terminal_step_facts_tac =
    drule body_inv_not_in_rf_reloc >> disch_then drule >> strip_tac >>
    drule_all body_inv_memory_reloc >> strip_tac >>
    `!e. step_inst fuel ctx inst vs <> Error e` by
      (qpat_x_assum `step_inst fuel ctx inst vs = _` (fn th => simp[th])) >>
    drule body_inv_label_resolve_reloc >> disch_then drule >> disch_then drule >>
    disch_then drule >> disch_then drule >> strip_tac;
in

Theorem body_halt_step_resource_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Halt vs1 ==>
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops)))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Halt vs1)
Proof
  strip_tac >> terminal_gather_tac >> terminal_step_facts_tac >>
  qspecl_then deep_args mp_tac gen_inst_halt_frame_sim_deep_reloc >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `vs1` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> irule body_result_resource_halt >>
  qexistsl_tac [`n`, `as'`] >>
  gvs[cost_le_def, execute_plan_append]
QED

Theorem body_halt_step_resource:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Halt vs1 ==>
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops)))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Halt vs1)
Proof
  pure_rewrite_tac[body_inv_reloc_specialize] >> strip_tac >>
  drule_all body_halt_step_resource_reloc >> simp[]
QED


Theorem body_halt_step_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Halt vs1 ==>
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Halt vs1)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`safe` |-> `F`] body_halt_step_resource_reloc)) >> strip_tac >>
  rewrite_tac[body_result_simple_def] >>
  irule body_result_resource_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem body_halt_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Halt vs1 ==>
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Halt vs1)
Proof
  pure_rewrite_tac[body_inv_reloc_specialize] >> strip_tac >>
  drule_all body_halt_step_reloc >> simp[]
QED

Theorem body_abort_step_resource_reloc:
  (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Abort a vs1 ==>
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + 7))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Abort a vs1)
Proof
  strip_tac >> terminal_gather_tac >> terminal_step_facts_tac >>
  `safe ==> inst_create_size_ok inst vs` by
    (strip_tac >> qpat_x_assum `safe ==> !f inst s. _` drule >>
     disch_then (qspecl_then [`fn`, `inst`, `vs`] mp_tac) >> simp[]) >>
  `inst.inst_opcode = ASSERT ==>
     ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
       FLOOKUP o2pc off = SOME pc /\
       asm_block_at prog pc (execute_plan cpl.cp_initial_fmp revert_postamble)` by
    (strip_tac >> qexistsl_tac [`roff`, `rpc`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then deep_args mp_tac gen_inst_abort_frame_sim_deep_reloc >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`a`, `vs1`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> irule body_result_resource_abort >>
  qexistsl_tac [`n`, `as'`] >>
  gvs[cost_le_def, execute_plan_append]
QED

Theorem body_abort_step_resource:
  (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Abort a vs1 ==>
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + 7))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Abort a vs1)
Proof
  pure_rewrite_tac[body_inv_reloc_specialize] >> strip_tac >>
  drule_all body_abort_step_resource_reloc >> simp[]
QED


Theorem body_abort_step_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Abort a vs1 ==>
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Abort a vs1)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`safe` |-> `F`] body_abort_step_resource_reloc)) >> strip_tac >>
  rewrite_tac[body_result_simple_def] >>
  irule body_result_resource_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem body_abort_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Abort a vs1 ==>
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Abort a vs1)
Proof
  pure_rewrite_tac[body_inv_reloc_specialize] >> strip_tac >>
  drule_all body_abort_step_reloc >> simp[]
QED

Theorem body_ret_step_resource_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = IntRet ret vs1 ==>
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops)))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (IntRet ret vs1)
Proof
  strip_tac >> terminal_gather_tac >>
  `inst.inst_opcode = RET` by metis_tac[codegen_ready_intret_opcode] >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (qspecl_then [`fn`, `bb`, `inst`] mp_tac reachable_fn_mem_inst >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `ps'.ps_stack = []` by
    (qpat_x_assum `inst.inst_opcode = RET ==> _` drule >>
     disch_then (qspecl_then [`ops`, `ps'`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
  qspecl_then
    [`fuel`, `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
     `fn`, `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
     `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `ra`,
     `rest`, `mem0`, `pc_ret`] mp_tac gen_ret_frame_sim_deep_exact_reloc >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`ret`, `vs1`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> irule body_result_resource_intret >>
  qexistsl_tac [`LENGTH (execute_plan cpl.cp_initial_fmp ops)`, `as'`] >>
  gvs[cost_le_def, execute_plan_append]
QED

Theorem body_ret_step_resource:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = IntRet ret vs1 ==>
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops)))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (IntRet ret vs1)
Proof
  pure_rewrite_tac[body_inv_reloc_specialize] >> strip_tac >>
  drule_all body_ret_step_resource_reloc >> simp[]
QED


Theorem body_plan_ret_step_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = IntRet ret vs1 ==>
    ?n as1.
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      as1.as_pc = pc_ret /\ as1.as_stack = REVERSE ret.iret_values ++ rest /\
      context_memory_rel cpl vs1.vs_memory as1.as_memory /\
      (!b. context_spill_byte cpl b /\
           ~closure_spill_byte ctx cpl fn.fn_name b ==>
           read_byte b as1.as_memory = read_byte b mem0) /\
      shared_state_rel vs1 as1
Proof
  strip_tac >> terminal_plan_gather_tac >>
  `inst.inst_opcode = RET` by metis_tac[codegen_ready_intret_opcode] >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (qspecl_then [`fn`, `bb`, `inst`] mp_tac reachable_fn_mem_inst >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `ps'.ps_stack = []` by
    (qpat_x_assum `inst.inst_opcode = RET ==> _` drule >>
     disch_then (qspecl_then [`ops`, `ps'`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC) >>
  qspecl_then
    [`fuel`, `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
     `fn`, `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
     `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `ra`,
     `rest`, `mem0`, `pc_ret`] mp_tac gen_ret_frame_sim_deep_reloc >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`ret`, `vs1`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem body_plan_ret_step:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = IntRet ret vs1 ==>
    ?n as1.
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      as1.as_pc = pc_ret /\ as1.as_stack = REVERSE ret.iret_values ++ rest /\
      context_memory_rel cpl vs1.vs_memory as1.as_memory /\
      (!b. context_spill_byte cpl b /\
           ~closure_spill_byte ctx cpl fn.fn_name b ==>
           read_byte b as1.as_memory = read_byte b mem0) /\
      shared_state_rel vs1 as1
Proof
  pure_rewrite_tac[body_plan_inv_reloc_specialize] >> strip_tac >>
  drule_all body_plan_ret_step_reloc >> simp[]
QED

Theorem body_ret_step_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = IntRet ret vs1 ==>
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (IntRet ret vs1)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`safe` |-> `F`] body_ret_step_resource_reloc)) >> strip_tac >>
  rewrite_tac[body_result_simple_def] >>
  irule body_result_resource_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem body_ret_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = IntRet ret vs1 ==>
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (IntRet ret vs1)
Proof
  pure_rewrite_tac[body_inv_reloc_specialize] >> strip_tac >>
  drule_all body_ret_step_reloc >> simp[]
QED

end

(* ===== INVOKE ===== *)

Theorem body_invoke_step_resource:
  gen_fn_sim_at safe q fuel /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = INVOKE /\
    LENGTH (compute_operands inst) <= 16 ==>
    (!vs1. step_inst fuel ctx inst vs = OK vs1 ==>
       ?ops ps' rest' n as1.
         generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
         cost_le (OPTION_MAP (\F. LENGTH (execute_plan cpl.cp_initial_fmp ops) +
                                F unit cpl prog) q) n /\
         (safe ==> create_safe_prefix lo o2pc prog n as) /\
         asm_steps lo o2pc prog n as = AsmOK as1 /\
         fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
         as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
       body_result safe (OPTION_MAP (\F.
         LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + F unit cpl prog) q)
         lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Halt vs1)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
       body_result safe (OPTION_MAP (\F.
         LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + F unit cpl prog) q)
         lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Abort a vs1))
Proof
  strip_tac >> gather_tac >>
  `?nm arg_ops. inst.inst_operands = Label nm :: arg_ops` by
    (qpat_x_assum `codegen_ready_inst inst` mp_tac >>
     qpat_x_assum `inst.inst_opcode = INVOKE` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[codegen_ready_inst_def, invoke_operands_wf_def] >>
     BasicProvers.every_case_tac >> gvs[]) >>
  qspecl_then [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `Inv`,
               `nm`] mp_tac body_callee_placed >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`safe`, `q`, `fuel`, `rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`,
               `Inv`] mp_tac body_callee_sim_resource >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then
    [`safe`, `OPTION_MAP (\F. F unit cpl prog) q`,
     `fuel`, `rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `Inv`,
     `liveness`, `dfg`, `cfg`, `fn`, `inst`,
     `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `r`, `ra`,
     `rest`, `mem0`, `nm`, `arg_ops`] mp_tac gen_invoke_frame_sim_deep_resource >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_x_assum `!j callee rj cvs cas cra crest cpc. _` mp_tac >>
    Cases_on `q` >> simp_tac (srw_ss()) [cost_le_def]) >>
  strip_tac >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!vs'. step_inst fuel ctx inst vs = OK vs' ==> _` drule >>
      strip_tac >>
      qexistsl_tac [`ops`, `ps'`, `rest'`, `n`, `as'`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum `case OPTION_MAP _ q of NONE => T | SOME B => _` mp_tac >>
      Cases_on `q` >> simp_tac (srw_ss()) [cost_le_def])
  >- (rpt strip_tac >>
      qpat_x_assum `!vs'. step_inst fuel ctx inst vs = Halt vs' ==> _`
        (qspec_then `vs1` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      strip_tac >> irule body_result_resource_halt >>
      qexistsl_tac [`n`, `as'`] >>
      Cases_on `q` >> simp[cost_le_def, execute_plan_append] >>
      fs[cost_le_def] >> decide_tac)
  >- (rpt strip_tac >>
      qpat_x_assum `!a vs'. step_inst fuel ctx inst vs = Abort a vs' ==> _`
        (qspecl_then [`a`, `vs1`] mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      strip_tac >> irule body_result_resource_abort >>
      qexistsl_tac [`n`, `as'`] >>
      Cases_on `q` >> simp[cost_le_def, execute_plan_append] >>
      fs[cost_le_def] >> decide_tac)
QED


Theorem body_plan_call_entry:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label nm :: arg_ops /\
    LENGTH (compute_operands inst) <= 16 /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\
    setup_callee callee args vs = SOME cvs ==>
  ?ops ps' rest' j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
    callee.fn_name = nm /\
    LENGTH args = LENGTH (compute_operands inst) /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    asm_block_at prog cas.as_pc
      (execute_plan cpl.cp_initial_fmp (EL j cpl.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cpl callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE (compute_operands inst)
      (live_vars_at liveness bb.bb_label (k + 1)) ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)))
      as = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cpl.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked spill_base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |>
Proof
  strip_tac >> gather_plan_tac >>
  qspecl_then [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`,
               `\_ _ _ _. F`, `nm`] mp_tac body_callee_placed >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `liveness`,
    `dfg`, `cfg`, `fn`, `inst`,
    `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
    `k + 1 < LENGTH bb.bb_instructions /\
     is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
    `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `r`,
    `ra`, `rest`, `mem0`, `nm`, `arg_ops`, `callee`, `args`, `cvs`]
    mp_tac invoke_enter_callee_plan >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`j`, `iops`, `prepared`, `rops`, `arranged`,
    `ret_lbl`, `ret_off`, `call_post`, `mid`, `saved`, `cas`, `pc`]
    strip_assume_tac) >>
  qexistsl_tac [`ops`, `ps'`, `rest'`, `j`, `iops`, `prepared`, `rops`,
    `arranged`, `ret_lbl`, `ret_off`, `call_post`, `mid`, `saved`, `cas`, `pc`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem body_invoke_step:
  gen_fn_sim_at_simple fuel /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = INVOKE /\
    LENGTH (compute_operands inst) <= 16 ==>
    (!vs1. step_inst fuel ctx inst vs = OK vs1 ==>
       ?ops ps' rest' n as1.
         generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
         asm_steps lo o2pc prog n as = AsmOK as1 /\
         fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
         as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
       body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Halt vs1)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
       body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Abort a vs1))
Proof
  mp_tac (Q.INST [`safe` |-> `F`, `q` |-> `NONE`]
    body_invoke_step_resource) >>
  simp[GSYM gen_fn_sim_at_simple_def, GSYM body_result_simple_def, cost_le_def]
QED

(* ===== Jumps ===== *)

(* The run from the successor t that a jump enters, in assembly state as1
   at t's code: gen_fn_frame_sim_at_simple fuel, entered through the lineage
   entry from bb, after the n steps from as. *)
val control_unpack_inv =
  qhdtm_assum `body_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]);

val control_gather_tac =
  drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all body_inv_step_reloc >> strip_tac >>
  drule_all body_inv_static_reloc >> strip_tac >>
  drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >>
  strip_tac >> control_unpack_inv;

val control_gather_plan_tac =
  drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule_all body_plan_inv_step_reloc >> strip_tac >>
  drule_all body_plan_inv_static_reloc >> strip_tac >>
  drule body_plan_inv_equiv_reloc >> disch_then drule >> disch_then drule >>
  strip_tac >> unpack_plan_inv_reloc;

Theorem body_plan_jump_entry_reloc:
  !fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
   growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
   ra pc_ret rest mem0 inst t vs1 n as1 off.
    body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
    MEM t (get_successors inst) /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
    ?tbb ps_tdfs tops tafter.
      lookup_block t fn.fn_blocks = SOME tbb /\ tbb.bb_label = t /\
      fn_reachable fn t /\ tbb <> HD fn.fn_blocks /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs /\
      generate_block_plan liveness dfg cfg fn tbb ps_tdfs =
        SOME (tops, tafter) /\
      asm_block_at prog as1.as_pc (execute_plan cpl.cp_initial_fmp tops) /\
      ps_tdfs.ps_alloc.sa_spill_base = r.sr_spill_base /\
      ps_tdfs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
      lineage_entry liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label t
        (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled |>) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0
        (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled |>) vs1 as1
Proof
  rpt gen_tac >> strip_tac >>
  drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule_all body_plan_succ_placed_reloc >> strip_tac >>
  unpack_plan_inv_reloc >>
  `toff = off` by
    (qpat_x_assum `FLOOKUP lo t = SOME toff` mp_tac >>
     qpat_x_assum `FLOOKUP lo t = SOME off` (fn th => REWRITE_TAC [th]) >>
     simp[]) >>
  `asm_block_at prog as1.as_pc (execute_plan cpl.cp_initial_fmp tops)` by
    (`tpc = as1.as_pc` by
       (qpat_x_assum `FLOOKUP o2pc toff = SOME tpc` mp_tac >>
        qpat_x_assum `toff = off` SUBST1_TAC >>
        qpat_x_assum `FLOOKUP o2pc off = SOME _` (fn th => REWRITE_TAC [th]) >>
        simp[]) >>
     qpat_x_assum `tpc = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `ps_tdfs.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (irule LESS_EQ_TRANS >> qexists_tac `ps_end.ps_alloc.sa_next_offset` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ps_tdfs.ps_alloc.sa_spill_base = r.sr_spill_base` by
    (qpat_x_assum `ps_tdfs.ps_alloc.sa_spill_base = spill_base` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `ps_after.ps_spilled = ps_tdfs.ps_spilled` by
    (qpat_x_assum `ps_after.ps_spilled = ps_dfs_after.ps_spilled`
       SUBST1_TAC >>
     irule fnBlockPlanStaticRegionTheory.dfs_edge_spilled >> simp[] >>
     metis_tac[]) >>
  suspend "lineage"
QED

Resume body_plan_jump_entry_reloc[lineage]:
  `lineage_entry liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label t
     (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                      ps_spilled := ps_after.ps_spilled |>)` by
    (PURE_REWRITE_TAC [lineage_entry_def] >>
     qexistsl_tac [`ps_l`, `bb`, `ps_dfs`, `block_ops`, `ps_dfs_after`, `h`,
                   `promised`, `ps_after`, `ps_tdfs`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
     qexistsl_tac [`prefixL`, `prefixD`, `core`] >> simp[]) >>
  `fn_frame_inv ctx cpl lo fn ra rest mem0
     (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                      ps_spilled := ps_after.ps_spilled |>) vs1 as1` by
    (qspecl_then [`ctx`, `cpl`, `lo`, `fn`, `ra`, `rest`, `mem0`, `ps_after`,
                  `ps_tdfs with <| ps_stack := ps_after.ps_stack;
                                   ps_spilled := ps_after.ps_spilled |>`,
                  `vs1`, `as1`, `r`] mp_tac fn_frame_inv_same_slots >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
         TRY (first_assum ACCEPT_TAC) >>
         qpat_x_assum `ps_tdfs.ps_alloc.sa_spill_base = r.sr_spill_base`
           (fn th => REWRITE_TAC [th, LESS_EQ_REFL])) >>
     disch_then ACCEPT_TAC) >>
  qexistsl_tac [`tbb`, `ps_tdfs`, `tops`, `tafter`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise body_plan_jump_entry_reloc

Theorem body_jump_continue_resource_at_lo:
  !safe q fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
   growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
   ra pc_ret rest mem0 inst t vs1 n as1 off.
    (gen_fn_frame_sim_at_reloc safe q fuel \/
     (lo = SND (compute_label_offsets prog) /\ gen_fn_frame_sim_at safe q fuel)) /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
    MEM t (get_successors inst) /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    (safe ==> create_safe_prefix lo o2pc prog n as) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F. n + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  rpt gen_tac >> strip_tac >>
  drule body_inv_plan_reloc >> strip_tac >>
  drule_all body_plan_jump_entry_reloc >> strip_tac >>
  drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >> control_unpack_inv >>
  `~vs1.vs_halted` by
    (qpat_assum `fn_frame_inv _ _ _ _ _ _ _ ps_after vs1 as1`
       (mp_tac o REWRITE_RULE [fn_frame_inv_def]) >> simp[]) >>
  `vs1.vs_labels = vs.vs_labels /\ vs1.vs_call_ctx = vs.vs_call_ctx /\
   vs1.vs_current_bb = t /\ vs1.vs_prev_bb = SOME bb.bb_label` by
    (qpat_x_assum `vs1 = _` SUBST1_TAC >>
     qpat_assum `bb.bb_label = vs.vs_current_bb`
       (fn th => simp[th, jump_to_def])) >>
  `fn_entry_inv Inv ctx fn vs1` by
    (PURE_REWRITE_TAC [fn_entry_inv_def] >> rpt strip_tac >>
     qpat_x_assum `reachability_closed _ _`
       (mp_tac o el 2 o CONJUNCTS o REWRITE_RULE [reachability_closed_def]) >>
     disch_then (qspecl_then [`fn`, `inst`, `inst'`, `vs`, `vs1`, `s1`,
                              `fuel`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  suspend "callee"
QED

Resume body_jump_continue_resource_at_lo[callee]:
  markerLib.RESUME_TAC >> (
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum (mp_tac o REWRITE_RULE
      [gen_fn_frame_sim_at_reloc_def, gen_fn_frame_sim_at_def] o
    assert (fn th => mem (fst (dest_const (fst (strip_comb (concl th)))))
      ["gen_fn_frame_sim_at_reloc", "gen_fn_frame_sim_at"])) >>
  disch_then (qspecl_then
    [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `i`, `fn`, `r`,
     `liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`, `lbl_ctr`,
     `fn_ops`, `ps_end`, `tbb`, `bb.bb_label`,
     `ps_tdfs with <| ps_stack := ps_after.ps_stack;
                      ps_spilled := ps_after.ps_spilled |>`,
     `ps_tdfs`, `tops`, `tafter`, `vs1`, `as1`, `Inv`, `ra`, `pc_ret`, `rest`,
     `mem0`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum `vs1.vs_labels = _` (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum `vs1.vs_call_ctx = _` (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum `vs1.vs_current_bb = _` (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum `vs1.vs_prev_bb = _` (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum `tbb.bb_label = t` (fn th => REWRITE_TAC [th]) >>
      TRY (first_assum ACCEPT_TAC) >>
      SIMP_TAC (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `body_result safe (OPTION_MAP (\F. F unit cpl prog) q)
     lo o2pc prog cpl ctx fn mem0 pc_ret rest as1
     (run_blocks fuel ctx fn vs1)` by
    (PURE_REWRITE_TAC [body_result_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all body_result_resource_prefix >> simp[OPTION_MAP_COMPOSE, combinTheory.o_DEF])
QED

Finalise body_jump_continue_resource_at_lo

Theorem body_jump_continue_resource_reloc:
  !safe q fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
   growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
   ra pc_ret rest mem0 inst t vs1 n as1 off.
    gen_fn_frame_sim_at_reloc safe q fuel /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
    MEM t (get_successors inst) /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    (safe ==> create_safe_prefix lo o2pc prog n as) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F. n + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  rpt gen_tac >> strip_tac >>
  irule body_jump_continue_resource_at_lo >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem body_jump_continue_resource:
  !safe q fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
   growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
   ra pc_ret rest mem0 inst t vs1 n as1 off.
    gen_fn_frame_sim_at safe q fuel /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
    MEM t (get_successors inst) /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    (safe ==> create_safe_prefix lo o2pc prog n as) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F. n + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  pure_rewrite_tac [body_inv_reloc_specialize] >>
  rpt gen_tac >> strip_tac >>
  irule body_jump_continue_resource_at_lo >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem body_plan_jump_entry:
  !fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
   growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
   ra pc_ret rest mem0 inst t vs1 n as1 off.
    body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
    MEM t (get_successors inst) /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
    ?tbb ps_tdfs tops tafter.
      lookup_block t fn.fn_blocks = SOME tbb /\ tbb.bb_label = t /\
      fn_reachable fn t /\ tbb <> HD fn.fn_blocks /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs /\
      generate_block_plan liveness dfg cfg fn tbb ps_tdfs =
        SOME (tops, tafter) /\
      asm_block_at prog as1.as_pc (execute_plan cpl.cp_initial_fmp tops) /\
      ps_tdfs.ps_alloc.sa_spill_base = r.sr_spill_base /\
      ps_tdfs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
      lineage_entry liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label t
        (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled |>) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0
        (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled |>) vs1 as1
Proof
  pure_rewrite_tac [body_plan_inv_reloc_specialize] >>
  rpt gen_tac >> strip_tac >>
  drule_all body_plan_jump_entry_reloc >> simp[]
QED

Theorem body_jump_continue_reloc:
  !fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
   growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
   ra pc_ret rest mem0 inst t vs1 n as1 off.
    gen_fn_frame_sim_at_simple_reloc fuel /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
    MEM t (get_successors inst) /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
    ~vs1.vs_halted /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  mp_tac (Q.SPECL [`F`, `NONE`] body_jump_continue_resource_reloc) >>
  simp[GSYM gen_fn_frame_sim_at_simple_reloc_def, GSYM body_result_simple_def]
QED

Theorem body_jump_continue:
  !fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
   growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
   ra pc_ret rest mem0 inst t vs1 n as1 off.
    gen_fn_frame_sim_at_simple fuel /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
    MEM t (get_successors inst) /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
       operand_val (frame_view fn ra vs1) lo at =
       operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
    ~vs1.vs_halted /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  mp_tac (Q.SPECL [`F`, `NONE`] body_jump_continue_resource) >>
  simp[GSYM gen_fn_frame_sim_at_simple_def, GSYM body_result_simple_def]
QED

(* The body_inv variables, in body_jump_continue's order. *)
val body_vars =
  [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `i`, `fn`, `r`,
   `liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`, `lbl_ctr`,
   `fn_ops`, `ps_end`, `bb`, `ps_l`, `h`, `promised`, `ps_dfs`, `block_ops`,
   `ps_dfs_after`, `ps_after`, `prefix_ops`, `rest_ops`, `k`, `ps`, `pc0`,
   `vs`, `as`, `Inv`, `ra`, `pc_ret`, `rest`, `mem0`];

(* The slot alias after a jump's step, at ps_after. *)
val jump_alias_tac =
  qspecl_then
    [`fuel`, `ctx`, `lo`, `fn`, `ra`, `liveness`, `dfg`, `cfg`, `inst`,
     `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `ps`, `ops`, `ps_after`, `vs`, `vs1`] mp_tac
    alias_step_preserve >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac;

val jump_resource_finish_tac =
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  irule body_result_resource_mono >> goal_assum (drule_at Any) >>
  Cases_on `q` >> simp[execute_plan_append] >> decide_tac;

Theorem body_jmp_step_resource_at_lo:
  (gen_fn_frame_sim_at_reloc safe q fuel \/
   (lo = SND (compute_label_offsets prog) /\ gen_fn_frame_sim_at safe q fuel)) /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F.
      LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (run_blocks fuel ctx fn vs1)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> control_gather_tac >>
  `?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JMP` mp_tac >>
     rpt (pop_assum kall_tac) >> rw[inst_wf_def] >> gvs[]) >>
  `is_terminator inst.inst_opcode` by
    (qpat_x_assum `inst.inst_opcode = JMP`
       (fn th => simp[th, is_terminator_def])) >>
  `MEM target (get_successors inst)` by
    (qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `is_terminator _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[get_successors_def, get_label_def]) >>
  drule_all body_terminator_last_reloc >> strip_tac >>
  drule_all body_succ_placed_reloc >> strip_tac >>
  `pending_inventory_wf
     (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                 (live_vars_at liveness target 0))) ps` by
    (qpat_x_assum `inst.inst_opcode = JMP ==> !target target_bb target_stack.
                     _ ==> pending_inventory_wf _ _` drule >>
     disch_then (qspecl_then [`target`, `tbb`,
       `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                   (live_vars_at liveness target 0))`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `inst.inst_opcode = JMP ==> !target target_bb target_stack.
                  _ ==> LENGTH _ <= _ /\ _` drule >>
  disch_then (qspecl_then [`target`, `tbb`,
    `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                (live_vars_at liveness target 0))`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  qspecl_then
    [`MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                 (live_vars_at liveness target 0))`,
     `ps`, `fn`, `ra`, `vs`, `lo`, `dfg`] mp_tac mem_operand_equiv >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          qspecl_then [`MAP Var (input_vars_from bb.bb_label
                          tbb.bb_instructions (live_vars_at liveness target 0))`,
                       `ps`, `op`] mp_tac pending_inventory_wf_owned >>
          impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
          disch_then ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  suspend "local_run"
QED

Resume body_jmp_step_resource_at_lo[local_run]:
  markerLib.RESUME_TAC >> (
  qspecl_then
    [`fuel`, `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
     `fn`, `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
     `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `r`, `ra`,
     `rest`, `mem0`, `target`, `tbb`,
     `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                 (live_vars_at liveness target 0))`, `toff`, `tpc`]
    mp_tac gen_jmp_frame_sim_deep_exact_reloc >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`FST (restore_spilled_plan _ _)`]
      >- (rpt strip_tac >>
      qpat_x_assum `!off. MEM (SORestore off) ops ==> _` irule >>
      qspecl_then
        [`liveness`, `dfg`, `cfg`, `fn`, `inst`,
         `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
         `k + 1 < LENGTH bb.bb_instructions /\
          is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
         `bb.bb_label`, `ps`, `ops`, `ps'`, `target`, `tbb`, `off`]
        mp_tac jmp_plan_restore_ops >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
      simp[]) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `ps' = ps_after` SUBST_ALL_TAC >> jump_alias_tac >>
  qspecl_then ([`safe`, `q`, `fuel`] @ body_vars @
               [`inst`, `target`, `vs1`,
                `LENGTH (execute_plan cpl.cp_initial_fmp ops)`, `as'`, `toff`]) mp_tac
    body_jump_continue_resource_at_lo >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`safe ==> create_safe_prefix _ _ _ _ _`] >- simp[] >>
      qpat_x_assum `as'.as_pc = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  jump_resource_finish_tac)
QED

Finalise body_jmp_step_resource_at_lo


Theorem body_jnz_step_resource_at_lo:
  (gen_fn_frame_sim_at_reloc safe q fuel \/
   (lo = SND (compute_label_offsets prog) /\ gen_fn_frame_sim_at safe q fuel)) /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JNZ /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F.
      LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (run_blocks fuel ctx fn vs1)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> control_gather_tac >>
  `?c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
             inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JNZ` mp_tac >>
     rpt (pop_assum kall_tac) >> rw[inst_wf_def] >> gvs[]) >>
  `~is_label_operand c` by
    (qpat_x_assum `inst_shape_ok inst` mp_tac >>
     qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JNZ` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[inst_shape_ok_def, label_positions_ok_def]) >>
  `is_terminator inst.inst_opcode` by
    (qpat_x_assum `inst.inst_opcode = JNZ`
       (fn th => simp[th, is_terminator_def])) >>
  `MEM l1 (get_successors inst) /\ MEM l2 (get_successors inst)` by
    (qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `is_terminator _` mp_tac >>
     qpat_x_assum `~is_label_operand c` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `c` >>
     simp[get_successors_def, get_label_def, is_label_operand_def]) >>
  `MEM c (compute_operands inst)` by
    (qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JNZ` mp_tac >>
     qpat_x_assum `~is_label_operand c` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `c` >>
     simp[compute_operands_def, get_non_label_operands_def,
          is_label_operand_def]) >>
  `eval_operand c vs = operand_val (frame_view fn ra vs) lo c` by
    (`eval_operand c vs = eval_operand c (frame_view fn ra vs)` by
       (irule eval_operand_frame_view_vs >> rpt strip_tac >>
        `MEM (Var x) inst.inst_operands` by
          (qpat_x_assum `inst.inst_operands = _` (fn th => REWRITE_TAC [th]) >>
           qpat_x_assum `c = Var x` (fn th => REWRITE_TAC [GSYM th, MEM])) >>
        drule_all opaque_use_ok_retpc_use >> strip_tac >>
        qpat_x_assum `retpc_use_ok _ _` mp_tac >>
        qpat_x_assum `inst.inst_opcode = JNZ`
          (fn th => simp[retpc_use_ok_def, th])) >>
     qpat_x_assum `eval_operand c vs = _` SUBST1_TAC >>
     qpat_x_assum `!op. MEM op (compute_operands inst) ==>
                     eval_operand op _ = _` irule >>
     first_assum ACCEPT_TAC) >>
  suspend "targets"
QED

Resume body_jnz_step_resource_at_lo[targets]:
  drule_all body_terminator_last_reloc >> strip_tac >>
  mp_tac (INST [``t:string`` |-> ``l1:string``] (SPEC_ALL body_succ_placed_reloc)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tbb1`, `ps_tdfs1`, `tops1`, `tafter1`,
                               `toff1`, `tpc1`] strip_assume_tac) >>
  mp_tac (INST [``t:string`` |-> ``l2:string``] (SPEC_ALL body_succ_placed_reloc)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tbb2`, `ps_tdfs2`, `tops2`, `tafter2`,
                               `toff2`, `tpc2`] strip_assume_tac) >>
  qpat_x_assum `inst.inst_opcode = JNZ ==> _` drule >>
  disch_then (qspecl_then [`c`, `l1`, `l2`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qspecl_then
    [`fuel`, `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
     `fn`, `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
     `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `r`, `ra`,
     `rest`, `mem0`, `c`, `l1`, `l2`, `toff1`, `toff2`, `tpc1`, `tpc2`]
    mp_tac gen_jnz_frame_sim_deep_exact_reloc >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!op at. MEM op (compute_operands inst) /\ _ ==> _` irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (disj1_tac >> first_assum ACCEPT_TAC) >>
      disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  suspend "branches"
QED

Resume body_jnz_step_resource_at_lo[branches]:
  disch_then drule >> strip_tac >>
  qmatch_asmsub_abbrev_tac `asm_steps lo o2pc prog n as` >>
  `create_safe_prefix lo o2pc prog n as` by simp[Abbr `n`] >>
  `n <= LENGTH (execute_plan cpl.cp_initial_fmp rest_ops)` by
    (simp[Abbr `n`, execute_plan_append, execute_plan_def, exec_stack_op_def] >>
     rw[] >> decide_tac) >>
  qpat_x_assum `ps' = ps_after` SUBST_ALL_TAC >> jump_alias_tac
  >- (qspecl_then ([`safe`, `q`, `fuel`] @ body_vars @
                   [`inst`, `l1`, `vs1`, `n`, `as'`, `toff1`]) mp_tac
        body_jump_continue_resource_at_lo >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >~ [`safe ==> create_safe_prefix _ _ _ _ _`] >- simp[] >>
          qpat_x_assum `as'.as_pc = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      irule body_result_resource_mono >> goal_assum (drule_at Any) >>
      Cases_on `q` >- simp[] >>
      qpat_x_assum `n <= LENGTH (execute_plan _ rest_ops)` mp_tac >>
      simp[execute_plan_append] >> decide_tac)
  >- (qspecl_then ([`safe`, `q`, `fuel`] @ body_vars @
                   [`inst`, `l2`, `vs1`, `n`, `as'`, `toff2`]) mp_tac
        body_jump_continue_resource_at_lo >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >~ [`safe ==> create_safe_prefix _ _ _ _ _`] >- simp[] >>
          qpat_x_assum `as'.as_pc = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      irule body_result_resource_mono >> goal_assum (drule_at Any) >>
      Cases_on `q` >- simp[] >>
      qpat_x_assum `n <= LENGTH (execute_plan _ rest_ops)` mp_tac >>
      simp[execute_plan_append] >> decide_tac)
QED

Finalise body_jnz_step_resource_at_lo


Theorem body_jmp_step_resource_reloc:
  gen_fn_frame_sim_at_reloc safe q fuel /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F.
      LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> irule body_jmp_step_resource_at_lo >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem body_jmp_step_resource:
  gen_fn_frame_sim_at safe q fuel /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F.
      LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (run_blocks fuel ctx fn vs1)
Proof
  pure_rewrite_tac [body_inv_reloc_specialize] >>
  strip_tac >> irule body_jmp_step_resource_at_lo >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem body_jnz_step_resource_reloc:
  gen_fn_frame_sim_at_reloc safe q fuel /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JNZ /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F.
      LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> irule body_jnz_step_resource_at_lo >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem body_jnz_step_resource:
  gen_fn_frame_sim_at safe q fuel /\
    (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s) /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JNZ /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result safe (OPTION_MAP (\F.
      LENGTH (execute_plan cpl.cp_initial_fmp rest_ops) + F unit cpl prog) q)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (run_blocks fuel ctx fn vs1)
Proof
  pure_rewrite_tac [body_inv_reloc_specialize] >>
  strip_tac >> irule body_jnz_step_resource_at_lo >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem jmp_plan_positive[local]:
  !liveness dfg cfg fn inst nl ih nit label ps ops final target target_bb fmp.
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
    inst.inst_outputs = [] /\ lookup_block target fn.fn_blocks = SOME target_bb /\
    generate_inst_plan liveness dfg cfg fn inst nl ih nit label ps =
      SOME (ops, final) ==>
    0 < LENGTH (execute_plan fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_jmp] >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       get_non_label_operands_def, is_commutative_def,
       venom_to_evm_name_def, generate_emit_ops_def, stack_pop_def,
       join_target_ops_def] >>
  Cases_on `restore_spilled_plan
    (MAP Var (input_vars_from label target_bb.bb_instructions
      (live_vars_at liveness target 0))) ps` >>
  rename1 `restore_spilled_plan _ ps = (restore_ops, restored)` >>
  Cases_on `reorder_plan dfg
    (MAP Var (input_vars_from label target_bb.bb_instructions
      (live_vars_at liveness target 0))) restored` >>
  simp[] >> strip_tac >>
  gvs[execute_plan_append, execute_plan_def, exec_stack_op_def]
QED

Theorem body_plan_jmp_step_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?target n as1 off.
      0 < n /\
      vs1 = jump_to target vs /\ MEM target (get_successors inst) /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
      (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
         operand_val (frame_view fn ra vs1) lo at =
         operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
      FLOOKUP lo target = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> control_gather_plan_tac >>
  `?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JMP` mp_tac >>
     rpt (pop_assum kall_tac) >> rw[inst_wf_def] >> gvs[]) >>
  `is_terminator inst.inst_opcode` by
    (qpat_x_assum `inst.inst_opcode = JMP`
       (fn th => simp[th, is_terminator_def])) >>
  `MEM target (get_successors inst)` by
    (qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `is_terminator _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[get_successors_def, get_label_def]) >>
  drule_all body_plan_terminator_last_reloc >> strip_tac >>
  drule_all body_plan_succ_placed_reloc >> strip_tac >>
  `pending_inventory_wf
     (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                 (live_vars_at liveness target 0))) ps` by
    (qpat_x_assum `inst.inst_opcode = JMP ==> !target target_bb target_stack.
                     _ ==> pending_inventory_wf _ _` drule >>
     disch_then (qspecl_then [`target`, `tbb`,
       `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                   (live_vars_at liveness target 0))`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `inst.inst_opcode = JMP ==> !target target_bb target_stack.
                  _ ==> LENGTH _ <= _ /\ _` drule >>
  disch_then (qspecl_then [`target`, `tbb`,
    `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                (live_vars_at liveness target 0))`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  qspecl_then
    [`MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                 (live_vars_at liveness target 0))`,
     `ps`, `fn`, `ra`, `vs`, `lo`, `dfg`] mp_tac mem_operand_equiv >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          qspecl_then [`MAP Var (input_vars_from bb.bb_label
                          tbb.bb_instructions (live_vars_at liveness target 0))`,
                       `ps`, `op`] mp_tac pending_inventory_wf_owned >>
          impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
          disch_then ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  qspecl_then
    [`fuel`, `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
     `fn`, `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
     `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `r`, `ra`,
     `rest`, `mem0`, `target`, `tbb`,
     `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
                 (live_vars_at liveness target 0))`, `toff`, `tpc`]
    mp_tac gen_jmp_frame_sim_deep_exact_reloc >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`FST (restore_spilled_plan _ _)`]
      >- (rpt strip_tac >>
      qpat_x_assum `!off. MEM (SORestore off) ops ==> _` irule >>
      qspecl_then
        [`liveness`, `dfg`, `cfg`, `fn`, `inst`,
         `live_vars_at liveness bb.bb_label (k + 1)`, `bb_is_halting bb`,
         `k + 1 < LENGTH bb.bb_instructions /\
          is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
         `bb.bb_label`, `ps`, `ops`, `ps'`, `target`, `tbb`, `off`]
        mp_tac jmp_plan_restore_ops >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
      simp[]) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `ps' = ps_after` SUBST_ALL_TAC >> jump_alias_tac >>
  `0 < LENGTH (execute_plan cpl.cp_initial_fmp ops)` by
    metis_tac[jmp_plan_positive] >>
  qexistsl_tac [`target`, `LENGTH (execute_plan cpl.cp_initial_fmp ops)`,
    `as'`, `toff`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `as'.as_pc = _` SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Theorem body_plan_jmp_step:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?target n as1 off.
      0 < n /\
      vs1 = jump_to target vs /\ MEM target (get_successors inst) /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
      (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
         operand_val (frame_view fn ra vs1) lo at =
         operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
      FLOOKUP lo target = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  pure_rewrite_tac [body_plan_inv_reloc_specialize] >>
  strip_tac >> drule_all body_plan_jmp_step_reloc >> simp[]
QED

Theorem body_jmp_step_reloc:
  gen_fn_frame_sim_at_simple_reloc fuel /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  mp_tac (Q.INST [`safe` |-> `F`, `q` |-> `NONE`]
    body_jmp_step_resource_reloc) >>
  simp[GSYM gen_fn_frame_sim_at_simple_reloc_def, GSYM body_result_simple_def]
QED

Theorem body_jmp_step:
  gen_fn_frame_sim_at_simple fuel /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  mp_tac (Q.INST [`safe` |-> `F`, `q` |-> `NONE`]
    body_jmp_step_resource) >>
  simp[GSYM gen_fn_frame_sim_at_simple_def, GSYM body_result_simple_def]
QED

Theorem body_plan_jnz_step_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JNZ /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?target n as1 off.
      0 < n /\
      vs1 = jump_to target vs /\ MEM target (get_successors inst) /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
      (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
         operand_val (frame_view fn ra vs1) lo at =
         operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
      FLOOKUP lo target = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> control_gather_plan_tac >>
  `?c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
             inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JNZ` mp_tac >>
     rpt (pop_assum kall_tac) >> rw[inst_wf_def] >> gvs[]) >>
  `~is_label_operand c` by
    (qpat_x_assum `inst_shape_ok inst` mp_tac >>
     qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JNZ` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[inst_shape_ok_def, label_positions_ok_def]) >>
  `is_terminator inst.inst_opcode` by
    (qpat_x_assum `inst.inst_opcode = JNZ`
       (fn th => simp[th, is_terminator_def])) >>
  `MEM l1 (get_successors inst) /\ MEM l2 (get_successors inst)` by
    (qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `is_terminator _` mp_tac >>
     qpat_x_assum `~is_label_operand c` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `c` >>
     simp[get_successors_def, get_label_def, is_label_operand_def]) >>
  `MEM c (compute_operands inst)` by
    (qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JNZ` mp_tac >>
     qpat_x_assum `~is_label_operand c` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `c` >>
     simp[compute_operands_def, get_non_label_operands_def,
          is_label_operand_def]) >>
  `eval_operand c vs = operand_val (frame_view fn ra vs) lo c` by
    (`eval_operand c vs = eval_operand c (frame_view fn ra vs)` by
       (irule eval_operand_frame_view_vs >> rpt strip_tac >>
        `MEM (Var x) inst.inst_operands` by
          (qpat_x_assum `inst.inst_operands = _` (fn th => REWRITE_TAC [th]) >>
           qpat_x_assum `c = Var x` (fn th => REWRITE_TAC [GSYM th, MEM])) >>
        drule_all opaque_use_ok_retpc_use >> strip_tac >>
        qpat_x_assum `retpc_use_ok _ _` mp_tac >>
        qpat_x_assum `inst.inst_opcode = JNZ`
          (fn th => simp[retpc_use_ok_def, th])) >>
     qpat_x_assum `eval_operand c vs = _` SUBST1_TAC >>
     qpat_x_assum `!op. MEM op (compute_operands inst) ==>
                     eval_operand op _ = _` irule >>
     first_assum ACCEPT_TAC) >>
  drule_all body_plan_terminator_last_reloc >> strip_tac >>
  mp_tac (INST [``t:string`` |-> ``l1:string``] (SPEC_ALL body_plan_succ_placed_reloc)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tbb1`, `ps_tdfs1`, `tops1`, `tafter1`,
                               `toff1`, `tpc1`] strip_assume_tac) >>
  mp_tac (INST [``t:string`` |-> ``l2:string``] (SPEC_ALL body_plan_succ_placed_reloc)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tbb2`, `ps_tdfs2`, `tops2`, `tafter2`,
                               `toff2`, `tpc2`] strip_assume_tac) >>
  qpat_x_assum `inst.inst_opcode = JNZ ==> _` drule >>
  disch_then (qspecl_then [`c`, `l1`, `l2`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qspecl_then
    [`fuel`, `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
     `fn`, `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
     `bb_is_halting bb`,
     `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb.bb_label`, `spill_base`, `ps`, `vs`, `as`, `ops`, `ps'`, `r`, `ra`,
     `rest`, `mem0`, `c`, `l1`, `l2`, `toff1`, `toff2`, `tpc1`, `tpc2`]
    mp_tac gen_jnz_frame_sim_deep_exact_reloc >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!op at. MEM op (compute_operands inst) /\ _ ==> _` irule >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (disj1_tac >> first_assum ACCEPT_TAC) >>
      disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `ps' = ps_after` SUBST_ALL_TAC >> jump_alias_tac
  >- (qexistsl_tac [`l1`,
        `LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) +
         (if w = 0w then 4 else 2)`, `as'`, `toff1`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (Cases_on `w = 0w` >> simp[] >> NO_TAC) >>
      qpat_x_assum `as'.as_pc = _` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`l2`,
        `LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) +
         (if w = 0w then 4 else 2)`, `as'`, `toff2`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (Cases_on `w = 0w` >> simp[] >> NO_TAC) >>
      qpat_x_assum `as'.as_pc = _` SUBST1_TAC >> first_assum ACCEPT_TAC)
QED

Theorem body_plan_jnz_step:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JNZ /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?target n as1 off.
      0 < n /\
      vs1 = jump_to target vs /\ MEM target (get_successors inst) /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
      (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
         operand_val (frame_view fn ra vs1) lo at =
         operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
      FLOOKUP lo target = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  pure_rewrite_tac [body_plan_inv_reloc_specialize] >>
  strip_tac >> drule_all body_plan_jnz_step_reloc >> simp[]
QED

Theorem body_jnz_step_reloc:
  gen_fn_frame_sim_at_simple_reloc fuel /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JNZ /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  mp_tac (Q.INST [`safe` |-> `F`, `q` |-> `NONE`]
    body_jnz_step_resource_reloc) >>
  simp[GSYM gen_fn_frame_sim_at_simple_reloc_def, GSYM body_result_simple_def]
QED

Theorem body_jnz_step:
  gen_fn_frame_sim_at_simple fuel /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JNZ /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ~vs1.vs_halted /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (run_blocks fuel ctx fn vs1)
Proof
  mp_tac (Q.INST [`safe` |-> `F`, `q` |-> `NONE`]
    body_jnz_step_resource) >>
  simp[GSYM gen_fn_frame_sim_at_simple_def, GSYM body_result_simple_def]
QED

(* ===== Revert forwarding ===== *)

Theorem rf_exec_block_cases:
  !bb s j fuel ctx.
    revert_forward_pair bb s.vs_inst_idx j ==>
    (?a t. exec_block fuel ctx bb s = Abort a t) \/
    (?e. exec_block fuel ctx bb s = Error e)
Proof
  rpt strip_tac >>
  `!t. exec_block fuel ctx bb s <> Halt t` by
    metis_tac[revert_forward_pair_no_halt] >>
  `!t ret. exec_block fuel ctx bb s <> OK t /\
           exec_block fuel ctx bb s <> IntRet ret t` by
    metis_tac[revert_forward_pair_no_normal] >>
  Cases_on `exec_block fuel ctx bb s` >> metis_tac[]
QED

(* A revert forwarding from k runs the rest of the block as one step,
   given that its code neither spills nor restores. *)
Theorem body_plan_revert_step_resource_reloc[local]:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    revert_forward_pair bb k j /\
    (!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) ==>
    (!t. exec_block fuel ctx bb vs <> OK t) /\
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops)))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (exec_block fuel ctx bb vs)
Proof
  strip_tac >> drule body_plan_inv_facts_reloc >> strip_tac >> unpack_plan_inv_reloc >>
  `revert_forward_pair bb vs.vs_inst_idx j` by
    (qpat_x_assum `vs.vs_inst_idx = k` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qspecl_then [`bb`, `vs`, `j`, `fuel`, `ctx`] mp_tac rf_exec_block_cases >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac
  >~ [`exec_block fuel ctx bb vs = Error e`]
  >- (qpat_x_assum `exec_block fuel ctx bb vs = _`
        (fn th => REWRITE_TAC [th, body_result_def]) >>
      simp[]) >>
  conj_tac
  >- (qpat_x_assum `exec_block fuel ctx bb vs = _`
        (fn th => REWRITE_TAC [th]) >> simp[]) >>
  `k < LENGTH bb.bb_instructions` by
    (qpat_x_assum `revert_forward_pair bb k j` mp_tac >>
     rpt (pop_assum kall_tac) >> CONV_TAC CONTRAPOS_CONV >> strip_tac >>
     simp[revert_forward_pair_def, get_instruction_def]) >>
  `EL k bb.bb_instructions = EL k bb.bb_instructions` by REWRITE_TAC [] >>
  drule_all body_plan_inv_static_reloc >> strip_tac >>
  `!inst. MEM inst bb.bb_instructions ==> inst_shape_ok inst` by
    (rpt strip_tac >>
     qspecl_then [`fn`, `bb`, `inst`] mp_tac body_inst_ready >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_x_assum `EVERY inst_shape_ok (fn_insts fn)` mp_tac >>
     REWRITE_TAC [EVERY_MEM] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  qspecl_then [`bb`, `k`, `j`] mp_tac rf_pair_no_labels >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `k - LENGTH (get_params bb.bb_instructions) +
   LENGTH (get_params bb.bb_instructions) = k` by
    (qpat_x_assum `LENGTH (get_params _) <= k` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  `DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb) =
   DROP k bb.bb_instructions` by
    (qpat_x_assum `non_param_insts bb = _` SUBST1_TAC >>
     REWRITE_TAC [DROP_DROP_T] >>
     qpat_x_assum `_ + _ = k` (fn th => REWRITE_TAC [th])) >>
  suspend "run"
QED

Resume body_plan_revert_step_resource_reloc[run]:
  `asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)` by
    (qspecl_then [`prog`, `pc0`, `cpl.cp_initial_fmp`, `bb.bb_label`,
                  `prefix_ops`, `rest_ops`, `[]`] mp_tac block_ops_at >>
     REWRITE_TAC [APPEND_NIL] >>
     impl_tac
     >- (qpat_x_assum `block_ops = _` (fn th =>
           qpat_x_assum `asm_block_at prog pc0 _` (fn th2 =>
             ACCEPT_TAC (REWRITE_RULE [th] th2)))) >>
     qpat_x_assum `as.as_pc = _` SUBST1_TAC >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `!j. revert_forward_pair bb k j ==> !k' inst' op. _` drule >>
  strip_tac >>
  qpat_x_assum `DROP (k - _) (non_param_insts bb) = _` (fn dth =>
    qpat_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ ps =
                SOME (rest_ops, ps_after)`
      (fn th => assume_tac (REWRITE_RULE [dth] th))) >>
  `!name. MEM (AsmOp name) (execute_plan cpl.cp_initial_fmp rest_ops) ==>
          IS_SOME (evm_opcode_byte name)` by
    (rpt strip_tac >>
     qspecl_then [`rpolicy`, `unit`, `prog`, `as.as_pc`,
                  `execute_plan cpl.cp_initial_fmp rest_ops`, `name`]
       mp_tac body_placed_target_safe >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  qspecl_then [`fuel`, `ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`,
               `cfg`, `fn`, `bb`, `k`, `j`, `spill_base`, `ps`, `vs`, `as`,
               `rest_ops`, `ps_after`, `ra`, `rest`, `mem0`]
    mp_tac revert_forward_frame_sim_deep_reloc >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`a`, `t`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `exec_block fuel ctx bb vs = _` (fn th => REWRITE_TAC [th]) >>
  strip_tac >> irule body_result_resource_abort >>
  qexistsl_tac [`n`, `as'`] >> simp[cost_le_def]
QED

Finalise body_plan_revert_step_resource_reloc


Theorem body_revert_step_resource_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    revert_forward_pair bb k j /\
    (!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) ==>
    (!t. exec_block fuel ctx bb vs <> OK t) /\
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops)))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (exec_block fuel ctx bb vs)
Proof
  strip_tac >> drule body_inv_plan_reloc >> strip_tac >>
  drule_all body_plan_revert_step_resource_reloc >> simp[]
QED

Theorem body_revert_step_resource:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    revert_forward_pair bb k j /\
    (!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) ==>
    (!t. exec_block fuel ctx bb vs <> OK t) /\
    body_result safe (SOME (LENGTH (execute_plan cpl.cp_initial_fmp rest_ops)))
      lo o2pc prog cpl ctx fn mem0 pc_ret rest as (exec_block fuel ctx bb vs)
Proof
  pure_rewrite_tac [body_inv_reloc_specialize] >>
  strip_tac >> drule_all body_revert_step_resource_reloc >> simp[]
QED

Theorem body_plan_revert_step_reloc:
  body_plan_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    revert_forward_pair bb k j /\
    (!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) ==>
    (!t. exec_block fuel ctx bb vs <> OK t) /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (exec_block fuel ctx bb vs)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`safe` |-> `F`]
    body_plan_revert_step_resource_reloc)) >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rewrite_tac[body_result_simple_def] >>
  irule body_result_resource_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem body_plan_revert_step:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    revert_forward_pair bb k j /\
    (!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) ==>
    (!t. exec_block fuel ctx bb vs <> OK t) /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (exec_block fuel ctx bb vs)
Proof
  pure_rewrite_tac [body_plan_inv_reloc_specialize] >>
  strip_tac >> drule_all body_plan_revert_step_reloc >> simp[]
QED

Theorem body_revert_step_reloc:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    revert_forward_pair bb k j /\
    (!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) ==>
    (!t. exec_block fuel ctx bb vs <> OK t) /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (exec_block fuel ctx bb vs)
Proof
  strip_tac >> drule body_inv_plan_reloc >> strip_tac >>
  drule_all body_plan_revert_step_reloc >> simp[]
QED

Theorem body_revert_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    revert_forward_pair bb k j /\
    (!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) ==>
    (!t. exec_block fuel ctx bb vs <> OK t) /\
    body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest as
      (exec_block fuel ctx bb vs)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`safe` |-> `F`] body_revert_step_resource)) >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rewrite_tac[body_result_simple_def] >>
  irule body_result_resource_mono >> goal_assum (drule_at Any) >> simp[]
QED
