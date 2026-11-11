(*
 * The per-instruction steps of fnBlockBody$block_body_frame_sim.
 *
 * body_inv bundles that theorem's premises (all but the fuel-level
 * simulation hypotheses) at instruction k of block bb; body_result is
 * its conclusion about a run result.  Each instruction class gets one
 * lemma: an ordinary, GAS or INVOKE instruction that steps OK moves the
 * invariant to k + 1 (body_inv_advance); a JMP or JNZ hands the rest of
 * the run to the successor block; halt, abort, RET and revert forwarding
 * end it.  The facts each instruction lemma needs from the planner, the
 * placement and Inv come from body_inv_facts, body_inv_step,
 * body_inv_inst and body_inv_static.
 *
 * The operand-count (DUP depth) and LOG topic-count facts are
 * hypotheses of the lemmas that consume them, in their consumers' form.
 *)

Theory fnBlockBodySteps
Ancestors
  fnBlockBodyHelpers fnBlockPlanStatic fnAliasStep
  fnFrameStepsRevertForwardDeep fnFrameDeep fnSimSpec fnPlanPlace
  fnPlanCover fnPlanPlaceDfsBlock fnPlanLineage fnLineageStatic
  fnPlanPrefix opcodeClass cfgAnalysisProps
  stepWriteFootprintForward asmTargetSafety codegen allocMono
  unitShapeDefs contextCodegenRel codegenRel frameRel stackPlanGen
  venomExecProps venomInstProps venomExecSemantics venomWf venomInst
  venomState stackOpSim asmSem dfgDefs list rich_list arithmetic
  finite_map option relation genFrameSim asmIR stackModel venomEffects
  stackPlanTypes planExec reorderSim

(* ===== The invariant and the conclusion ===== *)

(* block_body_frame_sim's premises other than gen_fn_sim_at and
   gen_fn_frame_sim_at, in its variable order. *)
Definition body_inv_def:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 <=>
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    ~vs.vs_call_ctx.cc_static /\
    codegen_context_obligations Inv ctx cpl /\
    reachability_closed Inv ctx /\
    (!inst. active_inst fn inst vs ==> Inv ctx fn inst vs) /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_reachable fn bb.bb_label /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      k ps /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions))
      (DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps = SOME (rest_ops, ps_after) /\
    block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
    phi_prefix_length bb.bb_instructions <= k /\
    (!i j. revert_forward_pair bb i j ==> k <= i \/ j < k) /\
    vs.vs_inst_idx = k /\
    asm_block_at prog pc0 (execute_plan cpl.cp_initial_fmp block_ops) /\
    as.as_pc = pc0 + LENGTH (execute_plan cpl.cp_initial_fmp
                                 (SOLabel bb.bb_label :: prefix_ops)) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
End

(* block_body_frame_sim's conclusion about the run result res from the
   assembly state as. *)
Definition body_result_def:
  body_result lo o2pc prog cpl ctx fn mem0 pc_ret rest as res <=>
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as') /\
    (!ret vs'. res = IntRet ret vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE ret.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as')
End

Theorem body_result_error:
  !lo o2pc prog cpl ctx fn mem0 pc_ret rest as e.
    body_result lo o2pc prog cpl ctx fn mem0 pc_ret rest as (Error e)
Proof
  simp[body_result_def]
QED

Theorem body_result_ok:
  !lo o2pc prog cpl ctx fn mem0 pc_ret rest as s.
    body_result lo o2pc prog cpl ctx fn mem0 pc_ret rest as (OK s)
Proof
  simp[body_result_def]
QED

(* Assembly steps that end OK in as1 compose with a result from as1. *)
Theorem body_result_prefix:
  !lo o2pc prog cpl ctx fn mem0 pc_ret rest as as1 n res.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    body_result lo o2pc prog cpl ctx fn mem0 pc_ret rest as1 res ==>
    body_result lo o2pc prog cpl ctx fn mem0 pc_ret rest as res
Proof
  rw[body_result_def] >> gvs[] >>
  qexistsl_tac [`n' + n`, `as'`] >> imp_res_tac asm_steps_add_ok >> fs[]
QED

(* ===== Generic facts ===== *)

Theorem body_insts_plan_spill_base:
  !insts liveness dfg cfg fn bb_label is_halting n_params block_len i
   ps ops ps'.
    generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
      n_params block_len i insts ps = SOME (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  Induct_on `insts` >> rpt gen_tac >>
  simp[Once generate_block_insts_plan_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  metis_tac[generate_inst_plan_spill_base]
QED

Theorem body_insts_plan_next_offset:
  !insts liveness dfg cfg fn bb_label is_halting n_params block_len i
   ps ops ps'.
    generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
      n_params block_len i insts ps = SOME (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  Induct_on `insts` >> rpt gen_tac >>
  simp[Once generate_block_insts_plan_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  metis_tac[generate_inst_plan_next_offset, LESS_EQ_TRANS]
QED

Theorem ef_read0_is_read0:
  !op. ef_read0 op ==> is_read0_opcode op
Proof
  rw[ef_read0_def, is_read0_opcode_def]
QED

Theorem step_inst_invoke_not_intret:
  !fuel ctx inst s vals t.
    inst.inst_opcode = INVOKE ==> step_inst fuel ctx inst s <> IntRet vals t
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once step_inst_def] >> gvs[AllCaseEqs(), bind_outputs_def]
QED

(* A non-retpc operand reads the same in the frame view. *)
Theorem eval_operand_frame_view_vs:
  !fn ra vs op.
    (!x. op = Var x ==> ~retpc_var fn x) ==>
    eval_operand op vs = eval_operand op (frame_view fn ra vs)
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, frame_view_non_retpc] >>
  simp[frame_view_def]
QED

Theorem phi_prefix_not_phi:
  !insts k.
    phi_prefix_length insts <= k /\ k < LENGTH insts /\
    (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) ==>
    (EL k insts).inst_opcode <> PHI
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `k`
  >- (Cases_on `h.inst_opcode = PHI` >> fs[]) >>
  Cases_on `h.inst_opcode = PHI`
  >- (fs[] >> qpat_x_assum `!k. _` irule >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!i j. _` (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
      simp[]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!i j. _` (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]
QED

(* The AsmOp names of placed code are known opcodes. *)
Theorem body_placed_target_safe:
  !rpolicy unit prog pc xs name.
    codegen_assembly rpolicy unit = SOME prog /\ asm_block_at prog pc xs /\
    MEM (AsmOp name) xs ==>
    IS_SOME (evm_opcode_byte name)
Proof
  rpt strip_tac >>
  `assembly_target_safe rpolicy.rpol_target prog` by
    (qpat_x_assum `codegen_assembly _ _ = _` mp_tac >>
     simp[codegen_assembly_def, AllCaseEqs()] >> rw[] >> simp[]) >>
  fs[MEM_EL, asm_block_at_def, assembly_target_safe_def, EVERY_EL] >>
  `EL (pc + n) prog = AsmOp name` by
    (qpat_x_assum `!j. j < LENGTH xs ==> _` (qspec_then `n` mp_tac) >>
     fs[]) >>
  qpat_x_assum `!n. n < LENGTH prog ==> _` (qspec_then `pc + n` mp_tac) >>
  simp[asm_inst_target_safe_def, asm_opcode_target_supported_def] >>
  qpat_x_assum `AsmOp name = _` (fn th => simp[GSYM th])
QED

(* A revert forwarding runs to the block's end: a RETURNDATACOPY, ASSIGNs
   and the terminating REVERT, none with label operands. *)
Theorem rf_pair_no_labels:
  !bb i j.
    bb_well_formed bb /\
    (!inst. MEM inst bb.bb_instructions ==> inst_shape_ok inst) /\
    revert_forward_pair bb i j ==>
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  `i < j /\ j < LENGTH bb.bb_instructions /\
   (EL i bb.bb_instructions).inst_opcode = RETURNDATACOPY /\
   (EL j bb.bb_instructions).inst_opcode = REVERT /\
   !k. i < k /\ k < j ==> (EL k bb.bb_instructions).inst_opcode = ASSIGN` by
    (fs[revert_forward_pair_def, get_instruction_def] >> rw[] >>
     first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  `j = PRE (LENGTH bb.bb_instructions)` by
    (fs[bb_well_formed_def] >> first_x_assum irule >>
     simp[is_terminator_def]) >>
  `!m. i <= m /\ m < LENGTH bb.bb_instructions ==>
       EVERY (\op. ~is_label_operand op) (EL m bb.bb_instructions).inst_operands` by
    (rpt strip_tac >>
     `inst_shape_ok (EL m bb.bb_instructions)` by metis_tac[EL_MEM] >>
     `~MEM (EL m bb.bb_instructions).inst_opcode
         [JMP; JNZ; PHI; INVOKE; ADD; CODECOPY]` by
       (Cases_on `m = i` >- gvs[] >>
        Cases_on `m = j` >- gvs[] >>
        `(EL m bb.bb_instructions).inst_opcode = ASSIGN` by
          (first_x_assum irule >> simp[]) >>
        simp[]) >>
     irule label_positions_ok_other >> fs[inst_shape_ok_def]) >>
  simp[EVERY_EL, EL_DROP] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `n + i` mp_tac) >> impl_tac >- decide_tac >>
  simp[EVERY_EL]
QED

(* A terminator's successor is a non-entry block of the function, reached
   from bb along a CFG edge. *)
Theorem body_succ_block:
  !fn bb k inst t.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
    ?tbb. lookup_block t fn.fn_blocks = SOME tbb /\ tbb.bb_label = t /\
          fn_reachable fn t /\ tbb <> HD fn.fn_blocks /\
          MEM t (cfg_succs_of (cfg_analyze fn) bb.bb_label)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ block_entries_ready (cfg_analyze fn) fn` by
    fs[codegen_ready_fn_def] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `k = PRE (LENGTH bb.bb_instructions)` by
    (fs[bb_well_formed_def] >> first_x_assum irule >> gvs[]) >>
  `inst = LAST bb.bb_instructions` by
    (fs[bb_well_formed_def] >> gvs[LAST_EL]) >>
  `MEM t (bb_succs bb)` by
    (simp[bb_succs_def] >> Cases_on `bb.bb_instructions` >>
     fs[bb_well_formed_def]) >>
  `MEM t (fn_labels fn)` by
    (fs[wf_function_def, fn_succs_closed_def] >> metis_tac[]) >>
  `?tbb. MEM tbb fn.fn_blocks /\ tbb.bb_label = t` by
    (fs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `lookup_block t fn.fn_blocks = SOME tbb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  `MEM t (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    (irule bb_succs_in_cfg_succs >> fs[wf_function_def]) >>
  qexists_tac `tbb` >> simp[] >> conj_tac
  >- (fs[fn_reachable_def] >>
      irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1)) >>
      qexists_tac `bb.bb_label` >> simp[fn_cfg_edge_def] >>
      metis_tac[]) >>
  strip_tac >>
  `fn.fn_blocks <> []` by (strip_tac >> fs[]) >>
  `entry_block fn = SOME (HD fn.fn_blocks)` by
    (simp[entry_block_def] >> Cases_on `fn.fn_blocks` >> fs[]) >>
  fs[block_entries_ready_def] >>
  `MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) t)` by
    metis_tac[cfg_edge_symmetry_uncond] >>
  gvs[NULL_EQ]
QED

(* A JMP's plan starts with restoring its join target's spilled values. *)
Theorem jmp_plan_restore_ops:
  !liveness dfg cfg fn inst nl ih nit bb_label ps ops ps' target target_bb
   off.
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
    inst.inst_outputs = [] /\
    lookup_block target fn.fn_blocks = SOME target_bb /\
    generate_inst_plan liveness dfg cfg fn inst nl ih nit bb_label ps =
      SOME (ops, ps') /\
    MEM (SORestore off)
      (FST (restore_spilled_plan
              (MAP Var (input_vars_from bb_label target_bb.bb_instructions
                          (live_vars_at liveness target 0))) ps)) ==>
    MEM (SORestore off) ops
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
              (MAP Var (input_vars_from bb_label target_bb.bb_instructions
                          (live_vars_at liveness target 0))) ps` >>
  Cases_on `reorder_plan dfg
              (MAP Var (input_vars_from bb_label target_bb.bb_instructions
                          (live_vars_at liveness target 0))) r` >>
  simp[] >> strip_tac >> gvs[]
QED

(* Values of owned operands that the DFG identifies agree. *)
Theorem mem_operand_equiv:
  !ops ps fn ra vs lo dfg.
    (!op. MEM op ops ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) ==>
    !op at. MEM op ops /\
            (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
            operand_equiv dfg op at ==>
            operand_val (frame_view fn ra vs) lo op =
            operand_val (frame_view fn ra vs) lo at
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[operand_equiv_def] >>
  metis_tac[]
QED

Theorem pending_inventory_wf_owned:
  !pending ps op.
    pending_inventory_wf pending ps /\ MEM op pending ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled
Proof
  rw[pending_inventory_wf_def] >>
  first_x_assum (qspec_then `op` mp_tac) >>
  `LIST_ELEM_COUNT op pending > 0` by metis_tac[LIST_ELEM_COUNT_MEM] >>
  `LIST_ELEM_COUNT op ps.ps_stack > 0 ==> MEM op ps.ps_stack` by
    metis_tac[LIST_ELEM_COUNT_MEM] >>
  rw[] >> fs[]
QED

(* ===== Facts from the invariant ===== *)

fun is_body_inv th =
  (fst (dest_const (fst (strip_comb (concl th)))) = "body_inv")
  handle HOL_ERR _ => false;

val unpack_inv =
  first_assum (strip_assume_tac o REWRITE_RULE [body_inv_def] o
               assert is_body_inv);

Theorem body_inv_facts:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 ==>
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    fn_entry_label fn = SOME fn.fn_name /\ EVERY inst_shape_ok (fn_insts fn) /\
    MEM fn ctx.ctx_functions /\ MEM r cpl.cp_regions /\
    r.sr_fn_name = fn.fn_name /\
    MEM bb fn.fn_blocks /\ bb.bb_label = vs.vs_current_bb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    bb_well_formed bb /\
    non_param_insts bb =
      DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
    LENGTH (get_params bb.bb_instructions) <= k /\
    asm_symbols_ok prog /\
    ps_after.ps_alloc.sa_spill_base = r.sr_spill_base /\
    ps_after.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (?pre post. r.sr_plan = pre ++ block_ops ++ post) /\
    IS_SOME (FLOOKUP lo "revert") /\
    (?roff rpc. FLOOKUP lo "revert" = SOME roff /\ roff < dimword (:256) /\
       FLOOKUP o2pc roff = SOME rpc /\
       asm_block_at prog rpc
         (execute_plan cpl.cp_initial_fmp revert_postamble))
Proof
  strip_tac >> unpack_inv >>
  qspecl_then [`ctx`, `unit`, `Inv`, `cpl`, `i`, `fn`] mp_tac body_fn_shape >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`ctx`, `cpl`, `i`] mp_tac body_context_region_fn_name >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = vs.vs_current_bb` by metis_tac[lookup_block_label] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by metis_tac[] >>
  `bb_well_formed bb` by fs[codegen_ready_fn_def, wf_function_def] >>
  `canonical_param_prefix fn` by fs[codegen_ready_fn_def] >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `fn`, `spill_base`,
               `lbl_ctr`, `fn_ops`, `ps_end`, `bb.bb_label`, `ps_dfs`, `bb`,
               `block_ops`, `ps_dfs_after`] mp_tac body_dfs_block_alloc_bounded >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `fn`, `spill_base`,
               `lbl_ctr`, `fn_ops`, `ps_end`, `bb.bb_label`, `ps_dfs`, `bb`,
               `block_ops`, `ps_dfs_after`] mp_tac dfs_block_plan_contained >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`] mp_tac
    revert_postamble_placed >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rpt conj_tac
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- metis_tac[EL_MEM]
  >- metis_tac[]
  >- metis_tac[]
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- metis_tac[non_param_insts_drop]
  >- fs[block_plan_state_def]
  >- metis_tac[codegen_assembly_symbols_ok]
  >- metis_tac[]
  >- metis_tac[LESS_EQ_TRANS]
  >- metis_tac[]
  >- fs[]
  >- metis_tac[]
QED

Theorem body_inv_inst:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst ==>
    inst.inst_opcode <> PHI /\ inst_wf inst /\ codegen_ready_inst inst /\
    MEM inst (fn_insts fn) /\ inst_shape_ok inst /\
    MEM inst bb.bb_instructions /\ get_instruction bb k = SOME inst /\
    active_inst fn inst vs /\ Inv ctx fn inst vs /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op)
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >> unpack_inv >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  qspecl_then [`fn`, `bb`, `inst`] mp_tac body_inst_ready >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `inst_shape_ok inst` by fs[EVERY_MEM] >>
  `get_instruction bb k = SOME inst` by simp[get_instruction_def] >>
  `active_inst fn inst vs` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[]) >>
  `inst.inst_opcode <> PHI` by
    (`!i j. i < j /\ j < LENGTH bb.bb_instructions /\
            (EL j bb.bb_instructions).inst_opcode = PHI ==>
            (EL i bb.bb_instructions).inst_opcode = PHI` by
       fs[bb_well_formed_def] >>
     qspecl_then [`bb.bb_instructions`, `k`] mp_tac phi_prefix_not_phi >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `EL k _ = inst` (fn th => simp[th])) >>
  rpt conj_tac
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- res_tac
  >- (strip_tac >> fs[inst_shape_ok_def] >> metis_tac[ef_read0_is_read0])
  >- metis_tac[eval_operand_frame_view]
QED

Theorem body_inv_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst ==>
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
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
      ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
      EVERY (\s. case s of SOSpill off => off < dimword(:256)
        | SORestore off => off < dimword(:256) | _ => T) ops /\
      (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
      asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp ops) /\
      (!lbl j. j < LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
               EL j (execute_plan cpl.cp_initial_fmp ops) = AsmLabel lbl ==>
               ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                     FLOOKUP o2pc off = SOME (as.as_pc + j))
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >> unpack_inv >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `fn`, `bb`, `k`, `ps`, `rest_ops`,
               `ps_after`] mp_tac block_insts_plan_step >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `EL k _ = inst` (SUBST_ALL_TAC o SYM) >>
  qexistsl_tac [`ops`, `ps'`, `rest'`] >>
  `ps'.ps_alloc.sa_spill_base = ps_after.ps_alloc.sa_spill_base /\
   ps'.ps_alloc.sa_next_offset <= ps_after.ps_alloc.sa_next_offset` by
    metis_tac[body_insts_plan_spill_base, body_insts_plan_next_offset] >>
  `!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
         off < dimword (:256)` by
    (gen_tac >> strip_tac >>
     qspecl_then [`ctx`, `cpl`, `r`, `pre ++ SOLabel bb.bb_label :: prefix_ops`,
                  `ops`, `rest' ++ post`, `off`] mp_tac
       body_region_spill_offsets >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
     simp[]) >>
  qspecl_then [`prog`, `pc0`, `cpl.cp_initial_fmp`, `bb.bb_label`,
               `prefix_ops`, `ops`, `rest'`] mp_tac block_ops_at >>
  impl_tac >- gvs[] >> strip_tac >>
  rpt conj_tac
  >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- fs[]
  >- metis_tac[LESS_EQ_TRANS]
  >- (rw[EVERY_MEM] >> Cases_on `s` >> simp[] >> metis_tac[])
  >- metis_tac[]
  >- gvs[]
  >- (qspecl_then [`prog`, `lo`, `o2pc`, `as.as_pc`,
                   `execute_plan cpl.cp_initial_fmp ops`] mp_tac
        asm_block_labels >>
      impl_tac >- gvs[] >> simp[])
QED

Theorem body_inv_static:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst ==>
    generated_plan_state_wf_marked spill_base ps /\
    MEM inst (fn_insts fn) /\ inst_wf inst /\
    ~is_param_opcode inst.inst_opcode /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) (live_vars_at liveness bb.bb_label (k + 1)) ps)).ps_stack /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v inst.inst_outputs) /\
    (inst.inst_opcode = JNZ ==>
     !cond_op if_nz if_z.
       inst.inst_operands = [cond_op; Label if_nz; Label if_z] ==>
       1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] (live_vars_at liveness bb.bb_label (k + 1)) ps)).ps_stack /\
       (is_var_operand cond_op ==>
         IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
         IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
       cond_op <> dead_stack_marker /\
       (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker)) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb.bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       pending_inventory_wf target_stack ps) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb.bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       LENGTH target_stack <=
         LENGTH (SND (restore_spilled_plan target_stack ps)).ps_stack /\
       EVERY (\op. op <> dead_stack_marker /\
         !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
         target_stack) /\
    (inst.inst_opcode = RET ==>
     !ops ps'.
       generate_inst_plan liveness dfg cfg fn inst (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
         (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
         bb.bb_label ps = SOME (ops, ps') ==>
       ps'.ps_stack = []) /\
    (!j. revert_forward_pair bb k j ==>
     !k' inst' op.
       k <= k' /\ get_instruction bb k' = SOME inst' /\
       MEM op (compute_operands inst') /\ is_var_operand op /\
       (!k'' inst'' x. k <= k'' /\ k'' < k' /\
                       get_instruction bb k'' = SOME inst'' /\
                       op = Var x ==> ~MEM x inst''.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!j. revert_forward_pair bb k j ==>
     !ops ps_end.
       generate_block_insts_plan liveness dfg cfg fn bb.bb_label
         (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
         (LENGTH bb.bb_instructions) (k - LENGTH (get_params bb.bb_instructions))
         (DROP k bb.bb_instructions) ps = SOME (ops, ps_end) ==>
       !off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops)
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >> unpack_inv >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`,
               `lbl_ctr`, `fn`, `fn_ops`, `ps_end`, `bb.bb_label`, `bb`,
               `ps_l`, `ps_dfs`, `ps_dfs_after`, `h`, `promised`,
               `block_ops`, `ps_after`, `k`, `ps`, `inst`,
               `live_vars_at liveness bb.bb_label (k + 1)`,
               `k + 1 < LENGTH bb.bb_instructions /\
                is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`]
    mp_tac block_plan_state_static >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      metis_tac[body_ready_fn_no_marker]) >>
  disch_then ACCEPT_TAC
QED

Theorem body_inv_equiv:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst ==>
    !op at. MEM op (compute_operands inst) /\
            (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
             MEM at (compute_operands inst)) /\
            operand_equiv dfg op at ==>
            operand_val (frame_view fn ra vs) lo op =
            operand_val (frame_view fn ra vs) lo at
Proof
  strip_tac >> drule_all body_inv_static >> strip_tac >> unpack_inv >>
  qspecl_then [`compute_operands inst`, `ps`, `fn`, `ra`, `vs`, `lo`, `dfg`]
    mp_tac owned_operand_equiv >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem body_inv_not_in_rf:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    (!j. ~revert_forward_pair bb k j) ==>
    ~in_revert_forward fn vs
Proof
  strip_tac >> drule body_inv_facts >> strip_tac >> unpack_inv >>
  simp[in_revert_forward_def, revert_forward_at_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!i j. revert_forward_pair _ _ _ ==> _` drule >>
  fs[revert_forward_pair_def]
QED

Theorem body_inv_memory:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~in_revert_forward fn vs ==>
    source_memory_reads_disjoint cpl inst vs /\
    context_source_memory_writes_disjoint cpl inst vs /\
    (!fuel vs1. step_inst fuel ctx inst vs = OK vs1 ==>
                context_spill_step_safe cpl vs vs1)
Proof
  strip_tac >> drule_all body_inv_inst >> strip_tac >>
  drule body_inv_facts >> strip_tac >> unpack_inv >>
  `codegen_memory_obligations Inv ctx cpl` by
    fs[codegen_context_obligations_def] >>
  pop_assum (mp_tac o REWRITE_RULE [codegen_memory_obligations_def]) >>
  disch_then (qspecl_then [`fn`, `inst`, `vs`] assume_tac) >>
  rpt conj_tac
  >- (first_x_assum (qspecl_then [`vs`, `0`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac)
  >- (first_x_assum (qspecl_then [`vs`, `0`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac)
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`vs1`, `fuel`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >> res_tac)
QED

Theorem body_inv_label_resolve:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode <> INVOKE /\
    (!e. step_inst fuel ctx inst vs <> Error e) ==>
    !l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)
Proof
  strip_tac >> drule_all body_inv_inst >> strip_tac >> unpack_inv >>
  rpt strip_tac >>
  `step_inst fuel ctx inst vs = step_inst_base inst vs` by
    metis_tac[step_inst_non_invoke] >>
  qspecl_then [`inst`, `vs`, `l`] mp_tac step_label_operands_resolve >>
  impl_tac >- (fs[inst_shape_ok_def] >> metis_tac[]) >>
  qpat_x_assum `!l. FLOOKUP vs.vs_labels l = _` (fn th => simp[th]) >>
  simp[IS_SOME_MAP]
QED
