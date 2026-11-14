(* Concrete suspended caller plans on the actual source frame stack. *)
Theory fnFramePrefixStack
Ancestors
  blockSimHelpers genBlockSim fnAliasStep dfgAnalysisProps dfgDefs frameViewFacts reorderSim
  fnFrameStepsRevertForward stackModel planWf stackPlanGen stackPlanTypes
  stackOpSim venomInst planExec asmSem unitShapeDefs venomWf venomExecProofs fnFramePrefix fnRunFields frameExecutionHistory calleeTransport
  venomExecSemantics venomInstProofs1 venomInstProps venomState ptrDiscipline
  fnBlockBody fnBlockBodyHelpers fnBlockBodySteps fnBlockBodyClasses fnFrameDeepInvoke fnFrameBoundaryInvoke fnFrameBoundaryGenRet
  frameRel codegenEntryRel contextCodegenRel list rich_list finite_map arithmetic

Theorem alias_invoke_return_preserve:
  !lo fn ra liveness dfg cfg inst next_live is_halting next_is_term
   bb_label ps ops ps' vs rvs ret vs1.
    dfg = dfg_build_function fn /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v inst.inst_outputs) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    generate_inst_plan liveness dfg cfg fn inst next_live is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state vs rvs)) = SOME vs1 ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  `ssa_form fn` by fs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op (compute_operands inst) /\ _ ==> IS_SOME _ \/ _`
       (qspec_then `op` mp_tac) >>
     impl_tac >- metis_tac[] >>
     Cases_on `stack_get_depth op ps.ps_stack` >> simp[FLOOKUP_DEF]
     >- (IF_CASES_TAC >> simp[]) >>
     drule stackModelTheory.stack_get_depth_props >>
     metis_tac[reorderSimTheory.stack_peek_mem]) >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
     MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
     ~is_var_operand at \/
     ?out. MEM out inst.inst_outputs /\ at = Var out` by
    (qspecl_then [`liveness`, `dfg_build_function fn`, `cfg`, `fn`, `inst`,
      `next_live`, `is_halting`, `next_is_term`, `bb_label`, `ps`, `ops`, `ps'`]
      mp_tac generate_inst_plan_inventory >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
     disch_then ACCEPT_TAC) >>
  `!op. (!v. op = Var v ==> ~MEM v inst.inst_outputs) ==>
     operand_val (frame_view fn ra vs1) lo op =
     operand_val (frame_view fn ra vs) lo op` by
    (rpt strip_tac >>
     qspecl_then [`inst.inst_outputs`, `ret.iret_values`, `vs`, `rvs`, `ret`,
       `vs1`, `fn`, `ra`, `lo`, `op`] mp_tac invoke_return_old_operand >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
                  Cases_on `op` >> gvs[EVERY_MEM]) >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!at. MEM at ps'.ps_stack \/ _ ==> _ \/ _ \/ ~is_var_operand at \/ _`
    (qspec_then `at` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac
  >~ [`~is_var_operand at`]
  >- (Cases_on `at` >> gvs[is_var_operand_def, normalize_operand_def])
  >~ [`MEM out inst.inst_outputs`]
  >- (`dfg_get_def (dfg_build_function fn) out = SOME inst` by
        metis_tac[dfg_build_function_ssa_def] >>
      `normalize_operand (dfg_build_function fn) [] (Var out) = Var out` by
        (simp[Once normalize_operand_def] >> gvs[dfg_get_def_def]) >>
      simp[]) >>
  metis_tac[]
QED

Theorem frame_history_readonly:
  !vs0 ctx stk PG G tn fn inst s hs h.
    frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    (s.vs_call_ctx, s.vs_tx_ctx, s.vs_block_ctx, s.vs_code, s.vs_prev_hashes) =
      (vs0.vs_call_ctx, vs0.vs_tx_ctx, vs0.vs_block_ctx,
       vs0.vs_code, vs0.vs_prev_hashes) /\
    EVERY (\f.
      (f.cf_state.vs_call_ctx, f.cf_state.vs_tx_ctx, f.cf_state.vs_block_ctx,
       f.cf_state.vs_code, f.cf_state.vs_prev_hashes) =
      (vs0.vs_call_ctx, vs0.vs_tx_ctx, vs0.vs_block_ctx,
       vs0.vs_code, vs0.vs_prev_hashes)) stk
Proof
  ho_match_mp_tac frame_history_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- (fs[enters_block_def] >> drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => ONCE_REWRITE_TAC [th]) >> fs[])
  >- (drule step_inst_ok_fields >> strip_tac >> fs[])
  >- (drule step_inst_ok_fields >> strip_tac >>
      fs[enters_block_def] >> drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => ONCE_REWRITE_TAC [th]) >> fs[])
  >- (drule setup_callee_shared_fields >> strip_tac >>
      fs[enters_block_def] >> drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => ONCE_REWRITE_TAC [th]) >> fs[])
  >> drule invoke_bind_frame_fields >>
  disch_then (fn th => ONCE_REWRITE_TAC [th]) >>
  Cases_on `ret.iret_adopt_fmp` >>
  fs[adopt_return_fmp_def, merge_callee_state_def]
QED

(* Each suspended caller stores its pre-call planner and the concrete
   arranged snapshot. No caller memory invariant is asserted in the callee. *)
Inductive frame_stack_plan:
[~entry:]
  (!rpolicy unit cpl prog vs0 es0 gas_tail root others lbl.
    initial_ctx_rel_tail gas_tail cpl prog unit.cu_context vs0 es0 /\
    unit.cu_context.ctx_functions = root :: others /\
    fn_entry_label root = SOME lbl /\
    fn_entry_state_rel cpl root
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
      (entry_asm_state vs0 es0) 0w [] ==>
    frame_stack_plan rpolicy unit cpl prog vs0 es0 [] root
      (entry_asm_state vs0 es0) 0w [] (entry_asm_state vs0 es0).as_memory)
[~call:]
  (!rpolicy unit cpl prog vs0 es0 stk fn caller_entry
    i r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
    bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
    rest_ops k ps pc0 vs ast ra pc_ret rest mem0
    f inst nm arg_ops callee args cvs ops ps' rest'
    iops prepared rops arranged ret_lbl ret_off call_post mid saved cas pc.
    frame_stack_plan rpolicy unit cpl prog vs0 es0 stk fn caller_entry
      ra rest mem0 /\
    body_plan_inv rpolicy unit cpl prog unit.cu_context
      (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      i fn r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
      bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
      rest_ops k ps pc0 vs ast ra pc_ret rest mem0 /\
    f.cf_fn = fn /\ f.cf_inst = inst /\ f.cf_state = vs /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
    lookup_function nm unit.cu_context.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs /\
    (vs.vs_call_ctx, vs.vs_tx_ctx, vs.vs_block_ctx, vs.vs_code, vs.vs_prev_hashes) =
      (vs0.vs_call_ctx, vs0.vs_tx_ctx, vs0.vs_block_ctx,
       vs0.vs_code, vs0.vs_prev_hashes) /\
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    emit_input_plan INVOKE (compute_operands inst)
      (live_vars_at liveness bb.bb_label (k + 1)) ps = (iops, prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ call_post /\
    fn_frame_inv unit.cu_context cpl (SND (compute_label_offsets prog))
      fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked spill_base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH args = LENGTH (compute_operands inst) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops))) ast = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cpl.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ call_post)) /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |> /\
    fn_entry_state_rel cpl callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP (build_offset_to_pc prog) (w2n ((n2w ret_off):bytes32)) =
      SOME (ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3) ==>
    frame_stack_plan rpolicy unit cpl prog vs0 es0 (f::stk) callee cas
      (n2w ret_off) (saved ++ rest) cas.as_memory)
End

Theorem frame_stack_plan_entry_fields:
  !rpolicy unit cpl prog vs0 es0 stk fn entry ra rest mem0.
    frame_stack_plan rpolicy unit cpl prog vs0 es0 stk fn entry ra rest mem0 ==>
    mem0 = entry.as_memory /\
    (entry.as_call_ctx, entry.as_tx_ctx, entry.as_block_ctx,
     entry.as_code, entry.as_prev_hashes) =
    (vs0.vs_call_ctx, vs0.vs_tx_ctx, vs0.vs_block_ctx,
     vs0.vs_code, vs0.vs_prev_hashes)
Proof
  ho_match_mp_tac frame_stack_plan_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- fs[fn_entry_state_rel_def, shared_state_rel_def] >>
  fs[fn_frame_inv_def, contextCodegenRelTheory.context_venom_asm_rel_def,
     frame_view_def, shared_state_rel_def]
QED

Theorem frame_stack_plan_push:
  frame_stack_plan rpolicy unit cpl prog vs0 es0 stk fn caller_entry
    ra rest mem0 /\
  frame_history vs0 unit.cu_context stk PG G tn fn inst vs hs history /\
  body_plan_inv rpolicy unit cpl prog unit.cu_context
    (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    i fn r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
    bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
    rest_ops k ps pc0 vs ast ra pc_ret rest mem0 /\
  f.cf_fn = fn /\ f.cf_inst = inst /\ f.cf_state = vs /\
  active_inst fn inst vs /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  lookup_function nm unit.cu_context.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs ==>
  ?n cas ret_off saved j.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK cas /\
    frame_stack_plan rpolicy unit cpl prog vs0 es0 (f::stk) callee cas
      (n2w ret_off) (saved ++ rest) cas.as_memory /\
    fn_entry_state_rel cpl callee cvs cas (n2w ret_off) (saved ++ rest) /\
    j < LENGTH unit.cu_context.ctx_functions /\
    EL j unit.cu_context.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze unit.cu_context).fcg_reachable /\
    asm_block_at prog cas.as_pc
      (execute_plan cpl.cp_initial_fmp (EL j cpl.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    FLOOKUP (build_offset_to_pc prog) (w2n ((n2w ret_off):bytes32)) =
      SOME (ast.as_pc + n)
Proof
  strip_tac >> drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_operands_le_16 >> strip_tac >>
  drule frame_history_readonly >> strip_tac >>
  drule_all body_plan_call_entry >> strip_tac >>
  drule_all frame_stack_plan_call >> strip_tac >>
  qexistsl_tac [`LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3`,
    `cas`, `ret_off`, `saved`, `j`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (decide_tac) >>
  FIRST [ONCE_REWRITE_TAC [ADD_ASSOC] >> first_assum ACCEPT_TAC,
    irule asm_steps_compose_ok >> qexists_tac `mid` >>
    conj_tac >> first_assum ACCEPT_TAC]
QED

Theorem frame_stack_plan_ret:
  frame_stack_plan rpolicy unit cpl prog vs0 es0 stk fn entry ra rest mem0 /\
  frame_history vs0 unit.cu_context stk PG G tn fn inst vs hs history /\
  active_frame_plan rpolicy unit cpl prog fn vs ast ra rest mem0 /\
  active_inst fn inst vs /\ inst.inst_opcode = RET /\
  step_inst fuel unit.cu_context inst vs = IntRet ret vs1 ==>
  ?n asr.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK asr /\
    FLOOKUP (build_offset_to_pc prog) (w2n ra) = SOME asr.as_pc /\
    asr.as_stack = REVERSE ret.iret_values ++ rest /\
    fn_return_state_rel unit.cu_context cpl fn vs1 entry asr
Proof
  rw[active_frame_plan_def] >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (irule reachable_fn_mem_inst >> metis_tac[body_plan_inv_def]) >>
  drule_all ret_source_frame_boundary >>
  disch_then (qspec_then `ra` strip_assume_tac) >>
  drule_all body_operands_le_16 >> strip_tac >>
  drule_all body_plan_ret_step >> strip_tac >>
  drule frame_stack_plan_entry_fields >> strip_tac >>
  drule frame_history_readonly >> strip_tac >>
  `FLOOKUP (build_offset_to_pc prog) (w2n ra) = SOME pc_ret` by
    fs[body_plan_inv_def] >>
  qexistsl_tac [`n`, `as1`] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  fs[fn_return_state_rel_def, shared_state_rel_def] >> metis_tac[]
QED

Theorem frame_stack_plan_pop:
  frame_stack_plan rpolicy unit cpl prog vs0 es0 (f::stk) callee entry
    cra crest cmem /\
  fn_return_state_rel unit.cu_context cpl callee rvs entry asr /\
  FLOOKUP (build_offset_to_pc prog) (w2n cra) = SOME asr.as_pc /\
  asr.as_stack = REVERSE ret.iret_values ++ crest /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state rvs)) = SOME resumed ==>
  ?n fin caller_entry ra rest mem0.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n asr = AsmOK fin /\
    frame_stack_plan rpolicy unit cpl prog vs0 es0 stk f.cf_fn
      caller_entry ra rest mem0 /\
    active_frame_plan rpolicy unit cpl prog f.cf_fn
      (resumed with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      fin ra rest mem0
Proof
  strip_tac >>
  qpat_x_assum `frame_stack_plan _ _ _ _ _ _ (_::_) _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [frame_stack_plan_cases]) >>
  fs[] >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_operands_le_16 >> strip_tac >>
  drule_all invoke_plan_decompose >> strip_tac >>
  `iops' = iops /\ prepared' = prepared` by
    (qpat_assum `emit_input_plan INVOKE _ _ _ = (iops',prepared')`
      (fn newer => qpat_assum `emit_input_plan INVOKE _ _ _ = (iops,prepared)`
        (fn older => mp_tac (TRANS (SYM newer) older))) >> simp[]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`iops' = iops`, `prepared' = prepared`] >>
  `rops' = rops /\ arranged' = arranged` by
    (qpat_assum `reorder_plan _ _ _ = (rops',arranged')`
      (fn newer => qpat_assum `reorder_plan _ _ _ = (rops,arranged)`
        (fn older => mp_tac (TRANS (SYM newer) older))) >> simp[]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`rops' = rops`, `arranged' = arranged`] >>
  `ops' = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++
      call_post /\ ps'' = ps'` by
    (qpat_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME (ops',ps'')`
      (fn newer => qpat_assum
        `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME
          (iops ++ rops ++
           [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++
           call_post,ps')`
        (fn older => mp_tac (TRANS (SYM newer) older))) >> simp[]) >>
  qpat_x_assum `ps'' = ps'` SUBST_ALL_TAC >>
  qpat_x_assum `ops' = _` SUBST_ALL_TAC >>
  `ret_lbl' = ret_lbl /\ call_post = pops ++ opts` by
    (qpat_assum
      `iops ++ rops ++
        [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++
        call_post = iops ++ rops ++
        [SOPushLabel ret_lbl'; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl'] ++
        pops ++ opts` mp_tac >> simp[APPEND_11]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`ret_lbl' = ret_lbl`, `call_post = pops ++ opts`] >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`consumed = _`, `pushed = _`] >>
  qpat_assum `body_plan_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  `ordered_spill_regions cpl.cp_regions /\ ctx_wf unit.cu_context` by
    fs[codegen_context_obligations_def, context_plan_layout_wf_def] >>
  `callee.fn_name = nm` by
    (drule fmpAnalysisPropsTheory.lookup_function_name >> simp[]) >>
  `fn_directly_calls unit.cu_context fn.fn_name callee.fn_name` by
    (qpat_x_assum `callee.fn_name = nm` SUBST1_TAC >>
     drule_all invoke_direct_call >> simp[]) >>
  `~TC (fn_directly_calls unit.cu_context) fn.fn_name fn.fn_name` by
    (qspecl_then [`\_ _ _ _. F`, `unit.cu_context`, `cpl`, `fn.fn_name`]
       mp_tac invoke_context_no_cycle >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by
    (qpat_x_assum `LENGTH (compute_operands inst) <= LENGTH (SND _).ps_stack`
       mp_tac >>
     qpat_x_assum `inst.inst_opcode = INVOKE` (fn th => rewrite_tac [th]) >>
     qpat_assum `emit_input_plan INVOKE _ _ _ = (iops,prepared)`
       (fn th => rewrite_tac [th]) >> simp[]) >>
  qspecl_then [`spill_base`, `ps`, `inst`,
    `live_vars_at liveness bb.bb_label (k + 1)`, `iops`, `prepared`,
    `dfg`, `rops`, `arranged`] mp_tac invoke_entry_structural_marked >>
  impl_tac
  >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        asm_simp_tac (srw_ss()) [] >> NO_TAC]) >>
  strip_tac >>
  `ALL_DISTINCT inst.inst_outputs` by
    metis_tac[genBlockSimTheory.codegen_ready_inst_outputs_distinct] >>
  `EVERY (\x. ~retpc_var fn x) inst.inst_outputs` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     irule noncopy_output_not_retpc >>
     conj_tac >- fs[codegen_ready_fn_def] >>
     qexists_tac `inst` >> simp[]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword (:256)
     | SORestore off => off < dimword (:256) | _ => T) (pops ++ opts)` by
    fs[EVERY_APPEND] >>
  `fn_return_state_rel unit.cu_context cpl callee rvs mid asr` by
    fs[fn_return_state_rel_def] >>
  `asr.as_pc = ast.as_pc +
    LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3` by
    decide_tac >>
  `asm_block_at prog asr.as_pc
     (execute_plan cpl.cp_initial_fmp (SOLabel ret_lbl :: pops ++ opts))` by
    (pop_assum SUBST1_TAC >> PURE_REWRITE_TAC [APPEND] >>
     irule invoke_return_block >>
     qexists_tac `nm` >> PURE_REWRITE_TAC [APPEND_ASSOC, APPEND] >>
     qpat_assum `asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp _)`
       (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_ASSOC, APPEND])) >>
  qspecl_then [`unit.cu_context`, `cpl`, `SND (compute_label_offsets prog)`,
    `build_offset_to_pc prog`, `prog`, `fn`, `ra`, `rest`, `mem0`,
    `arranged`, `compute_operands inst`, `args`, `vs`, `mid`, `saved`,
    `ret.iret_values`, `callee`, `rvs`, `ret`, `resumed`, `asr`, `r`,
    `inst.inst_outputs`, `live_vars_at liveness bb.bb_label (k + 1)`,
    `bb_is_halting bb`, `dfg`, `inst`,
    `k + 1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
    `ret_lbl`, `called`, `pops`, `popped`, `opts`, `swapped`, `ps'`]
    mp_tac invoke_return_frame_numeric_exact >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[APPEND]) >>
  disch_then (qx_choose_then `fin` strip_assume_tac) >>
  `resumed.vs_labels = vs.vs_labels /\
   resumed.vs_call_ctx = vs.vs_call_ctx /\
   resumed.vs_current_bb = vs.vs_current_bb` by
    (drule invoke_bind_frame_fields >>
     Cases_on `ret.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def] >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
    operand_val (frame_view fn ra resumed)
      (SND (compute_label_offsets prog)) at =
    operand_val (frame_view fn ra resumed)
      (SND (compute_label_offsets prog)) (normalize_operand dfg [] at)` by
    (qspecl_then [`SND (compute_label_offsets prog)`, `fn`, `ra`, `liveness`,
       `dfg`, `cfg`, `inst`, `live_vars_at liveness bb.bb_label (k + 1)`,
       `bb_is_halting bb`,
       `k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
       `bb.bb_label`, `ps`, `ops`, `ps'`, `vs`, `rvs`, `ret`, `resumed`]
       mp_tac alias_invoke_return_preserve >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
     disch_then ACCEPT_TAC) >>
  `~is_terminator inst.inst_opcode /\
   (!j. ~revert_forward_pair bb k j)` by
    (conj_tac >- simp[is_terminator_def] >>
     gen_tac >> disch_tac >>
     qpat_assum `revert_forward_pair bb k j`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [revert_forward_pair_def]) >>
     mp_tac (Q.INST [`bb` |-> `bb`, `i` |-> `k`, `j` |-> `j`,
       `k` |-> `k`, `inst` |-> `inst`] rf_forward_instruction_opcode) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     simp[]) >>
  `fin.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)` by
    (fs[execute_plan_append, execute_plan_def, exec_stack_op_def] >> decide_tac) >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`,
    `lo` |-> `SND (compute_label_offsets prog)`,
    `o2pc` |-> `build_offset_to_pc prog`,
    `as` |-> `ast`, `as1` |-> `fin`, `vs1` |-> `resumed`]
    body_plan_advance_core) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[APPEND_ASSOC]) >>
  strip_tac >>
  qexistsl_tac [`1 + LENGTH (execute_plan cpl.cp_initial_fmp (pops ++ opts))`,
    `fin`, `caller_entry`, `ra`, `rest`, `mem0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
  simp[active_frame_plan_def] >>
  qexistsl_tac [`i`, `r`, `liveness`, `dfg`, `cfg`, `ch`, `growth`,
    `spill_base`, `lbl_ctr`, `fn_ops`, `ps_end`, `bb`, `ps_l`, `h`,
    `promised`, `ps_dfs`, `block_ops`, `ps_dfs_after`, `ps_after`,
    `prefix_ops ++ ops`, `rest'`, `SUC k`, `ps'`, `pc0`, `pc_ret`] >>
  qpat_x_assum `vs.vs_inst_idx = k` (fn th => PURE_REWRITE_TAC [th]) >>
  first_assum ACCEPT_TAC
QED
