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
  stackPlanTypes planExec reorderSim

fun is_body_inv th =
  (fst (dest_const (fst (strip_comb (concl th)))) = "body_inv")
  handle HOL_ERR _ => false;

val unpack_inv =
  first_assum (strip_assume_tac o REWRITE_RULE [body_inv_def] o
               assert is_body_inv);

(* The facts every instruction lemma reads, as assumptions. *)
val gather_tac =
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule_all body_inv_equiv >> strip_tac >>
  unpack_inv;

val phi_tac =
  rpt strip_tac >> qpat_x_assum `inst.inst_opcode = PHI` mp_tac >>
  qpat_x_assum `inst.inst_opcode <> PHI` mp_tac >> simp[];

(* ===== The terminator's successor ===== *)

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
  strip_tac >> drule body_inv_facts >> strip_tac >>
  drule_all body_inv_step >> strip_tac >>
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

Theorem body_succ_placed:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
    ?tbb ps_tdfs tops tafter off pc.
      lookup_block t fn.fn_blocks = SOME tbb /\ tbb.bb_label = t /\
      fn_reachable fn t /\ tbb <> HD fn.fn_blocks /\
      MEM t (cfg_succs_of cfg bb.bb_label) /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs /\
      generate_block_plan liveness dfg cfg fn tbb ps_tdfs =
        SOME (tops, tafter) /\
      FLOOKUP lo t = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME pc /\
      asm_block_at prog pc (execute_plan cpl.cp_initial_fmp tops) /\
      ps_tdfs.ps_alloc.sa_spill_base = spill_base /\
      ps_tdfs.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >> unpack_inv >>
  qspecl_then [`fn`, `bb`, `k`, `inst`, `t`] mp_tac body_succ_block >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`,
               `lbl_ctr`, `fn`, `fn_ops`, `ps_end`, `t`, `tbb`]
    mp_tac dfs_block_state_reachable >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `i`,
               `fn`, `r`, `liveness`, `dfg`, `cfg`, `ch`, `growth`, `lbl_ctr`,
               `ps_end`, `t`, `tbb`, `ps_dfs'`, `block_ops'`,
               `ps_dfs_after'`] mp_tac dfs_block_code_placed >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
  strip_tac >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `fn`, `spill_base`,
               `lbl_ctr`, `fn_ops`, `ps_end`, `t`, `ps_dfs'`, `tbb`,
               `block_ops'`, `ps_dfs_after'`] mp_tac body_dfs_state_region >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`tbb`, `ps_dfs'`, `block_ops'`, `ps_dfs_after'`, `off`,
                `pc`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]
QED

(* ===== The callee of an INVOKE ===== *)

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
  qspecl_then [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `j`,
               `EL j ctx.ctx_functions`, `EL j cpl.cp_regions`] mp_tac
    fn_region_placed >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  qspecl_then [`ctx`, `unit`, `Inv`, `cpl`, `j`, `EL j ctx.ctx_functions`]
    mp_tac body_fn_shape >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  `(HD (EL j ctx.ctx_functions).fn_blocks).bb_label = nm` by
    (qpat_x_assum `fn_entry_label _ = _` mp_tac >>
     simp[fn_entry_label_def, entry_block_def] >>
     Cases_on `(EL j ctx.ctx_functions).fn_blocks` >> simp[]) >>
  qexistsl_tac [`off`, `pc`] >> gvs[]
QED

Theorem body_callee_sim:
  !fuel rpolicy unit cpl prog ctx lo o2pc Inv.
    gen_fn_sim_at fuel /\
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
       ~cvs.vs_call_ctx.cc_static /\
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
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `gen_fn_sim_at _` (mp_tac o REWRITE_RULE [gen_fn_sim_at_def]) >>
  disch_then (qspecl_then [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`,
                           `o2pc`, `j`, `rj`, `callee`, `cvs`, `cas`, `Inv`,
                           `cra`, `cpc`, `crest`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

(* ===== Moving the invariant past an instruction ===== *)

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
  strip_tac >> drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  unpack_inv >>
  `vs1.vs_labels = vs.vs_labels /\ vs1.vs_call_ctx = vs.vs_call_ctx /\
   vs1.vs_current_bb = vs.vs_current_bb` by
    metis_tac[step_preserves_labels, step_preserves_call_ctx,
              step_preserves_control_flow] >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
     operand_val (frame_view fn ra vs1) lo at =
     operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)` by
    (qspecl_then [`fuel`, `ctx`, `lo`, `fn`, `ra`, `liveness`, `dfg`, `cfg`,
                  `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
                  `bb_is_halting bb`,
                  `k + 1 < LENGTH bb.bb_instructions /\
                   is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
                  `bb.bb_label`, `ps`, `ops`, `ps'`, `vs`, `vs1`]
       mp_tac alias_step_preserve >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `execute_plan cpl.cp_initial_fmp (SOLabel bb.bb_label :: (prefix_ops ++ ops)) =
   execute_plan cpl.cp_initial_fmp (SOLabel bb.bb_label :: prefix_ops) ++
   execute_plan cpl.cp_initial_fmp ops` by
    REWRITE_TAC [GSYM execute_plan_append, APPEND] >>
  PURE_REWRITE_TAC [body_inv_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC)
  >~ [`FLOOKUP (_ with vs_inst_idx := _).vs_labels`]
  >- (simp[] >> qpat_x_assum `vs1.vs_labels = _` SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  >~ [`(_ with vs_inst_idx := _).vs_call_ctx`]
  >- (simp[] >> qpat_x_assum `vs1.vs_call_ctx = _` SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  >~ [`Inv ctx fn _ (_ with vs_inst_idx := _)`]
  >- (rpt strip_tac >>
      qpat_x_assum `reachability_closed _ _`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [reachability_closed_def]) >>
      disch_then (qspecl_then [`fn`, `inst`, `inst'`, `vs`, `vs1`, `fuel`]
                    mp_tac) >>
      qpat_x_assum `vs.vs_inst_idx = k` (fn th => REWRITE_TAC [th]) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[])
  >~ [`lookup_block (_ with vs_inst_idx := _).vs_current_bb`]
  >- (simp[] >> qpat_x_assum `vs1.vs_current_bb = _` SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  >~ [`block_plan_state`]
  >- (irule block_plan_state_step >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`ops`, `ps`] >>
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
        (strip_tac >> qpat_x_assum `a = k` SUBST_ALL_TAC >> res_tac) >>
      simp[])
  >~ [`(_ with vs_inst_idx := _).vs_inst_idx`] >- simp[]
  >~ [`as1.as_pc = _`]
  >- (qpat_x_assum `execute_plan _ (SOLabel _ :: (_ ++ _)) = _` SUBST1_TAC >>
      qpat_x_assum `as1.as_pc = _` SUBST1_TAC >>
      qpat_x_assum `as.as_pc = _` SUBST1_TAC >> simp[])
  >~ [`fn_frame_inv`]
  >- (REWRITE_TAC [fn_frame_inv_inst_idx] >> first_assum ACCEPT_TAC)
  >~ [`operand_val`]
  >- (REWRITE_TAC [frame_view_inst_idx, operand_val_inst_idx] >>
      first_assum ACCEPT_TAC)
QED
