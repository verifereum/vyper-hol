(*
 * The symbolic fuel induction: the two steps of fnEntryStep and fnBlockStep
 * with the symbolic run added, and their closure over all fuel.  The
 * concrete function-level statements at each fuel come from codegen's own
 * steps (fn_entry_block_step, fn_block_frame_step).
 *
 * TOP-LEVEL:
 *   sym_fn_entry_block_step  - sym_fn_sim_at (SUC fuel) from the four
 *                              function statements at fuel
 *   sym_fn_block_frame_step  - sym_fn_frame_sim_at (SUC fuel), likewise
 *   sym_fn_sims_all          - all four at every fuel
 *)
Theory symFnStep
Ancestors
  symBlockBody symFrameBoundary symFnSimSpec codegenSymRel fnEntryStep
  fnBlockStep fnBlockStepHelpers fnBlockBody fnSimSpec asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel venomExecSemantics
  venomState planExec stackOpSim blockSimHelpers
Libs
  prefixContractLib

val _ = Theory.add_ML_dependency "prefixContractLib";

(* These names are representation variables in the boundary contracts. *)
val _ = Parse.hide "base";
val _ = Parse.hide "body";
Theorem sym_frame_inv_cleanup_fields:
  !prog env ctx cp fn ret srest labs0 ps h promised as ss.
    sym_frame_inv prog env ctx cp fn ret srest labs0
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      as ss <=>
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
Proof
  simp[sym_frame_inv_def, sym_kinds_ok_def]
QED

Theorem sym_label_block_steps:
  !lo o2pc prog as fmp lbl ops env ctx cp fn ret srest labs0 ps ss.
    asm_block_at prog as.as_pc (execute_plan fmp (SOLabel lbl :: ops)) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    asm_steps lo o2pc prog 1 as = AsmOK (as with as_pc := as.as_pc + 1) /\
    sym_steps prog env 1 ss =
      SymOK (ss with sym_base := ss.sym_base with as_pc := as.as_pc + 1) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps
      (as with as_pc := as.as_pc + 1)
      (ss with sym_base := ss.sym_base with as_pc := as.as_pc + 1) /\
    asm_block_at prog (as.as_pc + 1) (execute_plan fmp ops)
Proof
  rpt gen_tac >> strip_tac >> drule label_block_steps >> strip_tac >> simp[] >>
  gvs[sym_frame_inv_def, asm_sym_rel_def] >>
  gvs[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [numLib.num_CONV ``1:num``])) >>
      simp[sym_steps_def, sym_step_def, sym_lift_def,
           asmSemTheory.asm_step_def, asmSemTheory.asm_next_def,
           sym_state_component_equality]) >>
  simp[sym_kinds_ok_def] >> gvs[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_body_result_prefix:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss res n as1 ss1.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as1 ss1 res ==>
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as ss res
Proof
  rpt gen_tac >> simp[sym_body_result_def] >> strip_tac >> rpt conj_tac
  >> rpt gen_tac >> strip_tac
  >> first_x_assum drule >> strip_tac
  >> qexists_tac `n + n'`
  >> simp[stackOpSimTheory.asm_steps_add, sym_steps_add]
  >> metis_tac[]
QED

Theorem sym_block_prefix_step:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised vs as s_phi clean_ops ps2 ops ps3 r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    generated_plan_state_wf_marked spill_base ps_l /\
    (!op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1 ==>
     !op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==> off < dimword (:256)) /\
    (!at. MEM at ps_l.ps_stack \/ at IN FDOM ps_l.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps_l vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = bb.bb_instructions /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan liveness cfg fn bb
            (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
     else ([], ps_l with <| ps_cleanup_height := h;
                            ps_cleanup_promised := promised |>)) =
      (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps_l as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (phi_prefix_length bb.bb_instructions)
        (non_param_insts bb) ps2 = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (phi_prefix_length bb.bb_instructions)
        (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb))
        ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule take_drop_phi_prefix >> strip_tac >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1`
  >- suspend "single"
  >> suspend "join"
QED

Resume sym_block_prefix_step[single]:
  qpat_assum `LENGTH (TAKE _ _) = _` (fn len =>
  prefix_contract_tac REWRITE_RULE irule
    [`ps` |-> `ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`,
     `base:num` |-> `spill_base:num`,
     `phis:instruction list` |-> `TAKE (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`,
     `body:instruction list` |-> `DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`]
    [len, listTheory.TAKE_DROP, stackPlanTypesTheory.plan_state_accfupds,
     combinTheory.K_THM, fnPlanPrefixTheory.wf_marked_cleanup_fields,
     fn_frame_inv_cleanup_fields, sym_frame_inv_cleanup_fields]
    sym_single_pred_prefix_frame_sim) >> simp[] >>
  suspend "single_inputs"
QED

Resume sym_block_prefix_step[single_inputs]:
  conj_tac >- suspend "single_spill_bounds" >>
  conj_tac >- suspend "single_operand_stability" >>
  suspend "single_lineage_witnesses"
QED

Resume sym_block_prefix_step[single_spill_bounds]:
  gvs[listTheory.MEM_APPEND]
QED

Resume sym_block_prefix_step[single_operand_stability]:
  metis_tac[]
QED

Resume sym_block_prefix_step[single_lineage_witnesses]:
  qexistsl_tac [`ch`, `growth`, `h`, `lbl_ctr`, `pred`, `promised`, `ps_l`, `spill_base`, `vs`] >>
  gvs[] >> metis_tac[]
QED

Resume sym_block_prefix_step[join]:
  gvs[] >>
  qpat_assum `non_param_insts _ = _` (fn np =>
  prefix_contract_tac (SRULE o cons listTheory.TAKE_DROP)
    (drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`))
    [`ps` |-> `ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`,
     `base:num` |-> `spill_base:num`,
     `phis:instruction list` |-> `TAKE (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`,
     `body:instruction list` |-> `DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`]
    [np, stackPlanTypesTheory.plan_state_accfupds, combinTheory.K_THM,
     fnPlanPrefixTheory.wf_marked_cleanup_fields,
     fn_frame_inv_cleanup_fields, sym_frame_inv_cleanup_fields]
    sym_phi_prefix_frame_sim) >>
  suspend "join_frame_inputs"
QED

Resume sym_block_prefix_step[join_frame_inputs]:
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  suspend "join_lineage_region_inputs"
QED

Resume sym_block_prefix_step[join_lineage_region_inputs]:
  disch_then (drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `MEM _ _.cp_regions`)) >>
  suspend "join_side_conditions"
QED

Resume sym_block_prefix_step[join_side_conditions]:
  simp[] >> (impl_tac >- metis_tac[]) >> simp[]
QED

Finalise sym_block_prefix_step

Theorem sym_nonentry_run_rest:
  !fuel ctx fn vs bb s_phi.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis vs bb.bb_instructions = OK s_phi ==>
    run_blocks (SUC fuel) ctx fn vs =
    block_rest fuel ctx fn bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >> simp[run_blocks_unfold, run_block_def, block_rest_def] >>
  Cases_on `exec_block fuel ctx bb
    (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]
QED

Theorem sym_phi_entry_inv:
  !Inv ctx fn vs bb s_phi.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_entry_inv Inv ctx fn vs /\
    eval_phis vs bb.bb_instructions = OK s_phi ==>
    !inst. active_inst fn inst
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
      Inv ctx fn inst
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  qpat_x_assum `fn_entry_inv _ _ _ _`
    (irule o REWRITE_RULE [fn_entry_inv_def]) >>
  simp[enters_block_def]
QED

Theorem sym_entry_body_inv:
  !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   lbl_ctr ps_end ps0 param_ops ps1 body_ops ps_after pc_bb vs as
   Inv ra pc_ret rest mem0.
    ctx = unit.cu_context /\ lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\ generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
      MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
      MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label callee_name :: args /\
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
    body_inv rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth r.sr_spill_base lbl_ctr r.sr_plan ps_end (HD fn.fn_blocks)
      ps0 ps0.ps_cleanup_height ps0.ps_cleanup_promised ps0
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)
      ps_after ps_after param_ops body_ops
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1
      pc_bb vs as Inv ra pc_ret rest mem0
Proof
  rpt gen_tac >> strip_tac >> suspend "entry_shape"
QED

Resume sym_entry_body_inv[entry_shape]:
  drule_all step_fn_shape >> strip_tac >> suspend "entry_body_fields"
QED

Resume sym_entry_body_inv[entry_body_fields]:
  gvs[fnBlockBodyStepsTheory.body_inv_def, stackPlanGenTheory.init_cleanup_plan_state_def,
      stackPlanTypesTheory.init_plan_state_def] >> suspend "entry_body_static"
QED

Resume sym_entry_body_inv[entry_body_static]:
  rpt conj_tac >> metis_tac[entry_step_phi_bound,
    revert_forward_pair_past_params, fnPlanLineageTheory.lineage_state_rules,
    venomWfTheory.fn_reachable_def, relationTheory.RTC_REFL]
QED

Finalise sym_entry_body_inv

Theorem sym_nonentry_body_inv:
  !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb pred ps_l h promised ps_dfs
   block_ops ps_dfs_after ps_after prefix_ops rest_ops ps pc0 vs s_phi as
   Inv ra pc_ret rest mem0.
    ctx = unit.cu_context /\ lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\ generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
      MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
      MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label callee_name :: args /\
      lookup_function callee_name ctx.ctx_functions = SOME callee ==>
      fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    ~vs.vs_call_ctx.cc_static /\
    codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
    fn_entry_inv Inv ctx fn vs /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\ fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_reachable fn bb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (block_ops, ps_after) /\
    ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
    ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
      (phi_prefix_length bb.bb_instructions) ps /\
    non_param_insts bb = bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (phi_prefix_length bb.bb_instructions)
      (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb))
      ps = SOME (rest_ops, ps_after) /\
    block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    asm_block_at prog pc0 (execute_plan cp.cp_initial_fmp block_ops) /\
    as.as_pc = pc0 + LENGTH (execute_plan cp.cp_initial_fmp
      (SOLabel bb.bb_label :: prefix_ops)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra s_phi) lo at =
      operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) ==>
    body_inv rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops
      (phi_prefix_length bb.bb_instructions) ps pc0
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      as Inv ra pc_ret rest mem0
Proof
  rpt gen_tac >> strip_tac >> suspend "phi_fields"
QED

Resume sym_nonentry_body_inv[phi_fields]:
  `s_phi.vs_labels = vs.vs_labels /\
   s_phi.vs_call_ctx = vs.vs_call_ctx /\
   s_phi.vs_current_bb = vs.vs_current_bb` by
    (drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  suspend "phi_body_inputs"
QED

Resume sym_nonentry_body_inv[phi_body_inputs]:
  `!inst. active_inst fn inst
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
      Inv ctx fn inst
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[sym_phi_entry_inv] >>
  suspend "phi_body_static"
QED

Resume sym_nonentry_body_inv[phi_body_static]:
  `get_params bb.bb_instructions = []` by
    (irule fnBlockBodyHelpersTheory.no_param_get_params >>
     gvs[callLayoutDefsTheory.no_param_insts_def,
         stackPlanGenTheory.non_param_insts_def, listTheory.FILTER_EQ_ID]) >>
  suspend "phi_body_finish"
QED

Resume sym_nonentry_body_inv[phi_body_finish]:
  gvs[fnBlockBodyStepsTheory.body_inv_def,
      fnBlockStepHelpersTheory.operand_val_frame_view_inst_idx] >>
  metis_tac[fnPlanLineageTheory.lineage_entry_lineage_state,
            fnBlockStepHelpersTheory.revert_forward_pair_past_phis]
QED

Finalise sym_nonentry_body_inv

Theorem sym_phi_error_body_result:
  !fuel ctx fn vs bb e lo o2pc prog env cp mem0 pc_ret rest srest labs0 as ss.
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis vs bb.bb_instructions = Error e ==>
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as ss (run_blocks (SUC fuel) ctx fn vs)
Proof
  rpt strip_tac >>
  simp[run_blocks_unfold, run_block_def, sym_body_result_def]
QED

Theorem sym_entry_return_result:
  !lo o2pc prog env cp ctx fn pc_ret rest srest fuel vs as ss ra rv vs'.
    fn_entry_state_rel cp fn vs as ra rest /\
    sym_body_result lo o2pc prog env cp ctx fn as.as_memory pc_ret rest
      srest ss.sym_mem_labels as ss (run_blocks fuel ctx fn vs) /\
    run_blocks fuel ctx fn vs = IntRet rv vs' ==>
    ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = pc_ret /\ as'.as_stack = REVERSE rv.iret_values ++ rest /\
      fn_return_state_rel ctx cp fn vs' as as' /\
      sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
      ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
      (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
      (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> simp[sym_body_result_def] >> strip_tac >>
  metis_tac[entry_step_return]
QED

Theorem sym_block_prefix_prepare:
  !unit cpl prog ctx i fn r liveness dfg cfg ch growth spill_base lbl_ctr
   fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after vs Inv.
    ctx = unit.cu_context /\ generate_context_plan ctx = SOME cpl /\
    unit_shape_ok unit /\ i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
    codegen_context_obligations Inv ctx cpl /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\ fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs = SOME (block_ops, ps_dfs_after)
    ==>
    ?h promised ps_after clean_ops ps2 inst_ops.
      codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
      non_param_insts bb = bb.bb_instructions /\ get_params bb.bb_instructions = [] /\
      lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb
        (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
        SOME (block_ops, ps_after) /\
      ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
      ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
      (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
         clean_stack_plan liveness cfg fn bb
           (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
       else ([], ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
        (clean_ops, ps2) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
        (non_param_insts bb) ps2 = SOME (inst_ops, ps_after) /\
      block_ops = SOLabel bb.bb_label :: clean_ops ++ inst_ops /\
      generated_plan_state_wf_marked spill_base ps /\
      (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
        ~MEM op (FLAT (MAP (\inst. inst.inst_operands) (collect_phis bb.bb_instructions))) /\
        (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
        ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
      (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1 ==>
       !op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
         (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
         ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
      MEM r cpl.cp_regions /\ r.sr_fn_name = fn.fn_name /\
      r.sr_spill_base <= ps_after.ps_alloc.sa_spill_base /\
      ps_after.ps_alloc.sa_next_offset <= r.sr_spill_end /\
      (!off. MEM (SOSpill off) (clean_ops ++ inst_ops) \/
        MEM (SORestore off) (clean_ops ++ inst_ops) ==> off < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >> suspend "prepare_shape"
QED

Resume sym_block_prefix_prepare[prepare_shape]:
  drule_all step_fn_shape >> strip_tac >> suspend "prepare_label"
QED

Resume sym_block_prefix_prepare[prepare_label]:
  drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  suspend "prepare_label_inputs"
QED

Resume sym_block_prefix_prepare[prepare_label_inputs]:
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
   dfs_block_state liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_dfs` by
    metis_tac[] >> suspend "prepare_params"
QED

Resume sym_block_prefix_prepare[prepare_params]:
  `canonical_param_prefix fn` by fs[stackPlanGenTheory.codegen_ready_fn_def] >>
  drule_all fnPlanPrefixTheory.nonentry_block_no_params >> strip_tac >> suspend "prepare_lineage"
QED

Resume sym_block_prefix_prepare[prepare_lineage]:
  drule fnPlanPrefixTheory.codegen_ready_fn_no_marker >> strip_tac >>
  drule fnPlanLineageTheory.lineage_entry_lineage_state >> strip_tac >>
  suspend "prepare_regenerate"
QED

Resume sym_block_prefix_prepare[prepare_regenerate]:
  drule_all fnPlanLineageTheory.lineage_state_block_plan >> strip_tac >>
  suspend "prepare_static"
QED

Resume sym_block_prefix_prepare[prepare_static]:
  drule_all fnLineageStaticTheory.lineage_state_static >> strip_tac >>
  suspend "prepare_split"
QED

Resume sym_block_prefix_prepare[prepare_split]:
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    generate_block_plan_nonentry >>
  (impl_tac >- simp[]) >> strip_tac >> suspend "prepare_bounds"
QED

Resume sym_block_prefix_prepare[prepare_bounds]:
  drule_all fnPlanPlaceDfsBlockTheory.dfs_block_plan_contained >> strip_tac >>
  suspend "prepare_alloc"
QED

Resume sym_block_prefix_prepare[prepare_alloc]:
  drule_all dfs_block_alloc_bounded >> strip_tac >> suspend "prepare_region"
QED

Resume sym_block_prefix_prepare[prepare_region]:
  drule_all context_region_fn_name >> suspend "prepare_region_fields"
QED

Resume sym_block_prefix_prepare[prepare_region_fields]:
  simp[] >> strip_tac >> suspend "prepare_finish"
QED

Resume sym_block_prefix_prepare[prepare_finish]:
  qexistsl_tac [`h`, `promised`, `ps_after`, `clean_ops`, `ps2`, `inst_ops`] >>
  simp[] >> suspend "prepare_finish_bounds"
QED

Resume sym_block_prefix_prepare[prepare_finish_bounds]:
  `r.sr_spill_base <= ps_after.ps_alloc.sa_spill_base /\
   ps_after.ps_alloc.sa_next_offset <= r.sr_spill_end` by (gvs[] >> decide_tac) >>
  gvs[] >> suspend "prepare_offsets"
QED

Resume sym_block_prefix_prepare[prepare_offsets]:
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> suspend "prepare_offset_bound"
QED

Resume sym_block_prefix_prepare[prepare_offset_bound]:
  gen_tac >> disch_tac >> irule region_subplan_spill_offsets >>
  suspend "prepare_offset_witness"
QED

Resume sym_block_prefix_prepare[prepare_offset_witness]:
  qexistsl_tac [`cpl`, `unit.cu_context`, `clean_ops ++ inst_ops`, `post`,
               `pre ++ [SOLabel vs.vs_current_bb]`, `EL i cpl.cp_regions`] >>
  gvs[]
QED

Finalise sym_block_prefix_prepare

Theorem sym_block_step_prefix:
  !unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth spill_base
   lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after vs as Inv
   ra rest mem0 s_phi env ret srest labs0 ss.
    ctx = unit.cu_context /\ lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\ generate_context_plan ctx = SOME cpl /\
    unit_shape_ok unit /\ i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
    codegen_context_obligations Inv ctx cpl /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\ fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps /\
    vs.vs_prev_bb = SOME pred /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs = SOME (block_ops, ps_dfs_after) /\
    asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp block_ops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\ asm_static_wf prog /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
    ?h promised ps_after prefix_ops rest_ops ps1 n as1 ss1.
      non_param_insts bb = bb.bb_instructions /\
      generate_block_plan liveness dfg cfg fn bb
        (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
        SOME (block_ops, ps_after) /\
      ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
      ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
      block_plan_state liveness dfg cfg fn bb
        (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
        (phi_prefix_length bb.bb_instructions) ps1 /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (phi_prefix_length bb.bb_instructions)
        (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb)) ps1 =
        SOME (rest_ops, ps_after) /\
      block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
        (SOLabel bb.bb_label :: prefix_ops)) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as1 /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        operand_val (frame_view fn ra s_phi) lo at =
        operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss1 /\
      sym_frame_inv prog env ctx cpl fn ret srest labs0 ps1 as1 ss1
Proof
  rpt gen_tac >> strip_tac >> suspend "full_prepare"
QED

Resume sym_block_step_prefix[full_prepare]:
  drule_all sym_block_prefix_prepare >>
  disch_then (strip_assume_tac o SPEC_ALL) >> suspend "full_label"
QED

Resume sym_block_step_prefix[full_label]:
  qpat_assum `block_ops = _` (fn eq =>
    qpat_x_assum `asm_block_at _ _ _` (mp_tac o REWRITE_RULE [eq])) >>
  suspend "full_label_match"
QED

Resume sym_block_step_prefix[full_label_match]:
  rewrite_tac[listTheory.APPEND] >>
  disch_then (mp_then (Pat `asm_block_at _ _ _`) mp_tac sym_label_block_steps) >>
  suspend "full_label_inputs"
QED

Resume sym_block_step_prefix[full_label_inputs]:
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
  suspend "full_phi"
QED

Resume sym_block_step_prefix[full_phi]:
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    sym_block_prefix_step >> suspend "full_phi_frame"
QED

Resume sym_block_step_prefix[full_phi_frame]:
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  suspend "full_phi_inputs"
QED

Resume sym_block_step_prefix[full_phi_inputs]:
  disch_then (mp_tac o REWRITE_RULE [fn_frame_inv_pc]) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  suspend "full_phi_remaining"
QED

Resume sym_block_step_prefix[full_phi_remaining]:
  disch_then (drule_all o SIMP_RULE pure_ss [asmSemTheory.asm_state_accfupds, combinTheory.K_THM]) >>
  strip_tac >> suspend "full_compose"
QED

Resume sym_block_step_prefix[full_compose]:
  qpat_assum `asm_steps _ _ _ 1 _ = _` (mp_tac o MATCH_MP asm_steps_add_ok) >>
  strip_tac >> suspend "full_witness"
QED

Resume sym_block_step_prefix[full_witness]:
  qexistsl_tac [`h`, `promised`, `ps_after`, `clean_ops ++ phi_ops`,
                `body_ops`, `ps1`, `1 + n`, `as'`, `ss'`] >>
  simp[execute_plan_label_length, Once sym_steps_add] >>
  suspend "full_plan_state"
QED

Resume sym_block_step_prefix[full_plan_state]:
  reverse conj_tac >- gvs[] >> suspend "full_plan_witness"
QED

Resume sym_block_step_prefix[full_plan_witness]:
  rewrite_tac[fnBlockPlanStaticTheory.block_plan_state_def] >>
  qexistsl_tac [`[]`,
    `ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`,
    `clean_ops`, `ps2`, `phi_ops`] >> gvs[]
QED

Finalise sym_block_step_prefix

Theorem sym_fn_entry_block_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_sim_at (SUC fuel)
Proof
  gen_tac >> strip_tac >> rewrite_tac[sym_fn_sim_at_def] >>
  rpt gen_tac >> strip_tac >> suspend "entry_plan"
QED

Resume sym_fn_entry_block_step[entry_plan]:
  drule_all step_fn_shape >> strip_tac >> suspend "entry_region"
QED

Resume sym_fn_entry_block_step[entry_region]:
  drule_all fnEntryPlanTheory.region_fn_plan >> strip_tac >>
  suspend "entry_block"
QED

Resume sym_fn_entry_block_step[entry_block]:
  drule_all fnEntryPlanTheory.entry_block_plan >> strip_tac >>
  suspend "entry_placed"
QED

Resume sym_fn_entry_block_step[entry_placed]:
  rename1 `generate_context_plan ctx = SOME cplan` >>
  `asm_block_at prog as.as_pc (execute_plan cplan.cp_initial_fmp
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
   asm_block_at prog as.as_pc (execute_plan cplan.cp_initial_fmp
     (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))` by
    (suspend "entry_placed_fact") >>
  suspend "entry_spills"
QED

Resume sym_fn_entry_block_step[entry_placed_fact]:
  qpat_x_assum `asm_block_at _ _ (execute_plan _ r.sr_plan)` mp_tac >>
  qpat_assum `r.sr_plan = _` (fn th => rewrite_tac[th]) >>
  suspend "entry_placed_reduce"
QED

Resume sym_fn_entry_block_step[entry_placed_reduce]:
  rewrite_tac[execute_plan_append, asm_block_at_append] >>
  rpt strip_tac >> fs[]
QED

Resume sym_fn_entry_block_step[entry_spills]:
  `!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)` by
    (rpt strip_tac >> irule region_subplan_spill_offsets >>
     suspend "entry_spill_witness") >>
  suspend "entry_prefix"
QED

Resume sym_fn_entry_block_step[entry_spill_witness]:
  qexistsl_tac [`cplan`, `ctx`, `param_ops`, `body_ops ++ rest_ops`,
                `[SOLabel (HD fn.fn_blocks).bb_label]`, `r`] >> simp[]
QED

Resume sym_fn_entry_block_step[entry_prefix]:
  prefix_contract_tac SRULE
    (drule_at (Pat `prepare_params_plan _ _ _ = _`))
    [`ch` |-> `cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
       (fcg_analyze ctx) fn.fn_name`,
     `growth` |-> `cleanup_growth_table ctx (fcg_analyze ctx)`,
     `spill_base` |-> `r.sr_spill_base`, `lbl_ctr` |-> `lbl_ctr`]
    [] sym_entry_prefix_frame_sim >>
  disch_then (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`)) >>
  suspend "entry_prefix_symbolic"
QED

Resume sym_fn_entry_block_step[entry_prefix_symbolic]:
  disch_then (drule_at (Pat `asm_sym_rel _ _ _ _`)) >>
  suspend "entry_prefix_inputs"
QED

Resume sym_fn_entry_block_step[entry_prefix_inputs]:
  disch_then (drule_at (Pat `fn_entry_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `MEM _ _.cp_regions`)) >>
  suspend "entry_prefix_stack"
QED

Resume sym_fn_entry_block_step[entry_prefix_stack]:
  disch_then (drule_at (Pat `_.sym_stack = _`)) >>
  simp[] >> suspend "entry_prefix_last"
QED

Resume sym_fn_entry_block_step[entry_prefix_last]:
  disch_then (qspecl_then [`lbl_ctr`, `fuel`] mp_tac) >>
  (impl_tac >- metis_tac[listTheory.MEM_EL, unitShapeDefsTheory.unit_shape_ok_def,
                         listTheory.EVERY_MEM]) >>
  strip_tac >> suspend "entry_body"
QED

Resume sym_fn_entry_block_step[entry_body]:
  drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`) sym_entry_body_inv >>
  disch_then (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  suspend "entry_body_match"
QED

Resume sym_fn_entry_block_step[entry_body_match]:
  disch_then (drule_at (Pat `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> suspend "entry_body_remaining"
QED

Resume sym_fn_entry_block_step[entry_body_remaining]:
  qpat_x_assum `ctx = unit.cu_context` SUBST_ALL_TAC >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  suspend "entry_body_index"
QED

Resume sym_fn_entry_block_step[entry_body_index]:
  disch_then (qspecl_then [`i`, `as.as_pc`, `pc_ret`] mp_tac) >>
  (impl_tac >- (simp[Once arithmeticTheory.ADD_COMM] >>
                fs[fn_entry_state_rel_def] >> metis_tac[])) >>
  suspend "entry_body_finish" 
QED

Resume sym_fn_entry_block_step[entry_body_finish]:
  strip_tac >> drule_all sym_block_body_frame_sim >>
  suspend "entry_body_result"
QED

Resume sym_fn_entry_block_step[entry_body_result]:
  strip_tac >> drule_all sym_body_result_prefix >>
  suspend "entry_run_rest"
QED

Resume sym_fn_entry_block_step[entry_run_rest]:
  strip_tac >>
  `run_blocks (SUC fuel) unit.cu_context fn vs =
   block_rest fuel unit.cu_context fn (HD fn.fn_blocks) vs_p` by
    (irule entry_step_run_rest >> metis_tac[exec_block_def]) >>
  suspend "entry_finish_result"
QED

Resume sym_fn_entry_block_step[entry_finish_result]:
  reverse (rpt conj_tac) >- (suspend "entry_intret") >>
  fs[sym_body_result_def]
QED

Resume sym_fn_entry_block_step[entry_intret]:
  rpt gen_tac >> strip_tac >>
  irule sym_entry_return_result >> suspend "entry_intret_inputs"
QED

Resume sym_fn_entry_block_step[entry_intret_inputs]:
  metis_tac[]
QED

Finalise sym_fn_entry_block_step

Theorem sym_fn_block_frame_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_frame_sim_at (SUC fuel)
Proof
  cheat
QED

Theorem sym_fn_sims_all:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel
Proof
  Induct
  >- (simp[gen_fn_sim_at_def, gen_fn_frame_sim_at_def, sym_fn_sim_at_def,
           sym_fn_frame_sim_at_def] >>
      rpt strip_tac >> gvs[Once run_blocks_def]) >>
  metis_tac[fn_entry_block_step, fn_block_frame_step,
            sym_fn_entry_block_step, sym_fn_block_frame_step]
QED
