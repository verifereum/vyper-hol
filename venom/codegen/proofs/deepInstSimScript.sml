(*
 * genBlockSim's gen_inst_ok_sim over a planner state with repeated
 * dead_stack_marker slots (generated_plan_state_wf_marked), with operands
 * owned at any stack depth and only an address bound on the plan's spill
 * and restore offsets.  The input preparation runs on deepResidualSim's
 * marker-tolerant numeric chain.
 *
 * TOP-LEVEL:
 *   gen_inst_ok_sim_marked
 *)

Theory deepInstSim
Ancestors
  fnFrameDeepInvoke deepResidualSim deepResidualBudget fnPlanPrefix regularPostfixSim genBlockSim planWf
  codegenReadyCompute regularMemorySim reorderSpillFresh prefixSpillReplay deepDupCallerSim
  stackOpAsmSim planSim asmIR venomInstProofs1 venomEffects indexedLists instSimHelpers
  opcodeClass strongPrefixSim emitInputSim planAlign asmOpSim spillSim allocMono cleanOpsSim
  contextCodegenRelProps
  regularEmitSim regularPlanSim emitSim prefixExec prefixSim venomWf
  generatedPrefixSim preparedPrefixSim generatedReorderSim reorderSim
  doSwapSim mixedPrefixSim codegenRel blockSimHelpers planSpillBounds
  stackOpSim stackModel stackPlanGen stackPlanOps stackPlanTypes planExec
  asmSem venomExecSemantics venomState venomInst
  sorting list rich_list arithmetic

(* regularPostfixSim's regular_generated_postfix_sim_structural on the
   numeric do_swap simulation. *)
Theorem regular_generated_postfix_sim_numeric:
  !dfg inst next_liveness is_halting next_is_term ps7 pop_ops ps8 opt_ops ps9 ps'
   initial_fmp lo o2pc prog vs st.
  LENGTH inst.inst_outputs <= 1 /\
  (!out. inst.inst_outputs = [out] ==>
    stack_get_depth (Var out) ps7.ps_stack = SOME 0) /\
  spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  (if inst.inst_outputs = [] \/ is_halting then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out next_liveness)
     inst.inst_outputs)) ps7) = (pop_ops,ps8) /\
  (if FILTER (\out. MEM out next_liveness) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst next_liveness next_is_term ps8) = (opt_ops,ps9) /\
  ps' = release_dead_spills next_liveness ps9 /\
  EVERY (\s. case s of SOSpill k => k < dimword(:256)
    | SORestore k => k < dimword(:256) | _ => T) opt_ops /\
  venom_asm_rel lo ps7 vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (pop_ops ++ opt_ops)) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (pop_ops ++ opt_ops))) st =
    AsmOK st' /\ venom_asm_rel lo ps' vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (pop_ops ++ opt_ops))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[]
  >- (qexists_tac `st` >> simp[execute_plan_def, asm_steps_def] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  rename1 `inst.inst_outputs = out::outs` >>
  `outs = []` by (Cases_on `outs` >> gvs[]) >> gvs[] >>
  Cases_on `MEM out next_liveness` >> gvs[]
  >- (Cases_on `is_halting` >> gvs[popmany_plan_def] >>
      drule_all optimistic_swap_sim_numeric >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qexists_tac `st'` >> simp[] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  Cases_on `is_halting` >> gvs[]
  >- (qexists_tac `st` >> simp[execute_plan_def, asm_steps_def] >>
      irule venom_asm_rel_release_dead_spills >> simp[]) >>
  drule_all popmany_plan_top_singleton_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >> simp[] >>
  irule venom_asm_rel_release_dead_spills >> simp[]
QED

Theorem regular_inst_prepared_emit_marked:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label spill_base ps vs as ops ps' name initial_fmp.
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked spill_base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_regular_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) /\
    step_inst fuel ctx inst vs = OK vs' /\
    inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?iops prepared selected rops arranged emitted popops popped optops tail mid after_emit.
        emit_input_plan inst.inst_opcode (compute_operands inst) next_liveness ps =
          (iops, prepared) /\
        reorder_plan dfg selected prepared = (rops, arranged) /\
        (selected = compute_operands inst \/
         (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
          selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
            [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
             EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
        LENGTH selected = LENGTH (compute_operands inst) /\
        arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
        emitted = arranged with ps_stack :=
          FOLDL (\stk out. stack_push (Var out) stk)
            (stack_pop (LENGTH selected) arranged.ps_stack) inst.inst_outputs /\
        (if inst.inst_outputs = [] \/ (is_halting /\ ~(LENGTH inst.inst_outputs > 1))
         then (popops,popped) = ([],emitted)
         else popmany_plan (MAP Var (FILTER (\out. ~MEM out next_liveness)
           inst.inst_outputs)) emitted = (popops,popped)) /\
        (if inst.inst_outputs = [] \/ FILTER (\out. MEM out next_liveness) inst.inst_outputs = []
         then (optops,tail) = ([],popped)
         else optimistic_swap_plan dfg inst next_liveness next_is_term popped = (optops,tail)) /\
        ps' = release_dead_spills next_liveness tail /\
        ops = iops ++ rops ++ [SOEmit name] ++ popops ++ optops /\
        LENGTH inst.inst_outputs <= 1 /\
        (!out. inst.inst_outputs = [out] ==>
          stack_get_depth (Var out) emitted.ps_stack = SOME 0) /\
        generated_plan_state_wf_marked spill_base emitted /\
        asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops))) as =
          AsmOK mid /\
        venom_asm_rel lo arranged vs mid /\
        mid.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
        asm_step_op o2pc name mid = AsmOK after_emit /\
        asm_step lo o2pc (AsmOp name) mid = AsmOK after_emit /\
        asm_steps lo o2pc prog 1 mid = AsmOK after_emit /\
        venom_asm_rel lo emitted vs' after_emit /\
        after_emit.as_pc = mid.as_pc + 1 /\
        asm_block_at prog mid.as_pc [AsmOp name] /\
        asm_block_at prog after_emit.as_pc (execute_plan initial_fmp (popops ++ optops))
Proof
  rpt strip_tac >>
  drule_all regular_plan_selected_prefix >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `PERM (compute_operands inst) selected` by
    (irule regular_plan_selected_perm >> metis_tac[]) >>
  `LENGTH selected = LENGTH (compute_operands inst)` by metis_tac[sortingTheory.PERM_LENGTH] >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (fs[stack_get_depth_def, optionTheory.IS_SOME_EXISTS] >> drule stack_find_el >>
         drule planWfTheory.stack_find_bound >>
         metis_tac[MEM_EL, MEM_REVERSE]) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  `residual_budget_wf_marked spill_base [] ps` by
    metis_tac[generated_plan_state_wf_marked_residual_nil] >>
  `plan_slots_bounded spill_base ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by gvs[] >>
  `EVERY (\s. case s of SOSpill k => k < dimword(:256)
    | SORestore k => k < dimword(:256) | _ => T) (iops ++ rops)` by
    gvs[EVERY_APPEND] >>
  `asm_block_at prog as.as_pc (execute_plan initial_fmp (iops ++ rops)) /\
   asm_block_at prog (as.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)))
     (execute_plan initial_fmp ([SOEmit name] ++ popops ++ optops))` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     qpat_x_assum `ops = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[execute_plan_append, asm_block_at_append, LENGTH_APPEND,
       APPEND_ASSOC, ADD_ASSOC] >> strip_tac >> asm_rewrite_tac[]) >>
  `arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected` by
    (drule_all selected_input_arranged_marked >> simp[]) >>
  drule_all selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo arranged vs mid` >>
  suspend "prepared"
QED

Resume regular_inst_prepared_emit_marked[prepared]:
  drule_all emit_input_plan_output_exclusion >> strip_tac >>
  `LENGTH selected <= 17 /\ LENGTH selected <= LENGTH prepared.ps_stack` by decide_tac >>
  drule_all reorder_plan_output_exclusion >> strip_tac >>
  `emitted = arranged with ps_stack :=
    FOLDL (\stk out. stack_push (Var out) stk)
      (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) inst.inst_outputs` by
    simp[emit_output_fold_stack] >>
  `LENGTH inst.inst_outputs <= 1` by metis_tac[regular_named_output_bound] >>
  drule_all materialised_emit_resources_marked >> strip_tac >>
  `!out. inst.inst_outputs = [out] ==>
    stack_get_depth (Var out) emitted.ps_stack = SOME 0` by
    (rpt strip_tac >> irule materialised_emit_singleton_depth >> metis_tac[]) >>
  `arranged.ps_alloc.sa_spill_base = ps'.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset` by
    (drule_all regular_postfix_alloc_frame >>
     simp[emit_output_fold_alloc]) >>
  `EVERY (\(off,len). len = 0 \/ off + len <= arranged.ps_alloc.sa_spill_base \/
      arranged.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
   inst_memory_safe arranged.ps_alloc inst vs vs'` by
    (irule regular_emit_memory_transport >> qexists `ps'` >> simp[]) >>
  `~is_pre_codegen_opcode inst.inst_opcode` by
    (`!bbs. EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions) bbs ==>
        EVERY codegen_ready_inst (fn_insts_blocks bbs)` by
       (Induct >> simp[fn_insts_blocks_def]) >>
     `codegen_ready_inst inst` by
       (qpat_x_assum `codegen_ready_fn fn` mp_tac >>
        qpat_x_assum `MEM inst (fn_insts fn)` mp_tac >>
        qpat_x_assum `!bbs. _ ==> EVERY codegen_ready_inst _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[codegen_ready_fn_def, fn_insts_def, EVERY_MEM] >>
        metis_tac[]) >>
     qpat_x_assum `codegen_ready_inst inst` mp_tac >>
     simp[codegen_ready_inst_def]) >>
  `plan_slots_bounded spill_base arranged` by
    fs[plan_state_residual_wf_marked_def] >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  suspend "emit_ready"
QED

Resume regular_inst_prepared_emit_marked[emit_ready]:
  drule_all regular_emit_ok_sim >>
  disch_then (qspec_then `o2pc` (qx_choose_then `after_emit` strip_assume_tac)) >>
  `venom_asm_rel lo emitted vs' after_emit` by metis_tac[] >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp ([SOEmit name] ++ popops ++ optops))` by
    metis_tac[] >>
  `asm_block_at prog mid.as_pc [AsmOp name] /\
   asm_block_at prog after_emit.as_pc (execute_plan initial_fmp (popops ++ optops))` by
    (qpat_x_assum `asm_block_at prog mid.as_pc _` mp_tac >>
     qpat_x_assum `after_emit.as_pc = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[execute_plan_append, execute_plan_def, exec_stack_op_def,
       MAP, FLAT, APPEND, asm_block_at_append, asm_block_at_cons] >>
     rpt strip_tac >> asm_rewrite_tac[asm_block_at_nil] >> decide_tac) >>
  suspend "emitted"
QED

Resume regular_inst_prepared_emit_marked[emitted]:
  `asm_step lo o2pc (AsmOp name) mid = AsmOK after_emit` by
    simp[asm_step_def] >>
  `asm_steps lo o2pc prog 1 mid = AsmOK after_emit` by
    (qpat_x_assum `asm_block_at prog mid.as_pc [AsmOp name]` mp_tac >>
     qpat_x_assum `asm_step_op o2pc name mid = AsmOK after_emit` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     once_rewrite_tac[arithmeticTheory.ONE] >>
     simp[asm_steps_def, asm_step_def, asm_block_at_def]) >>
  qexistsl [`iops`, `prepared`, `selected`, `rops`, `arranged`, `emitted`,
    `popops`, `popped`, `optops`, `tail`, `mid`, `after_emit`] >> simp[]
QED

Finalise regular_inst_prepared_emit_marked

Theorem regular_inst_ok_sim_marked_count:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label spill_base ps vs as ops ps' name initial_fmp.
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked spill_base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_regular_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) /\
    step_inst fuel ctx inst vs = OK vs' /\
    inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops)) /\
        (~is_terminator inst.inst_opcode ==>
         n = LENGTH (execute_plan initial_fmp ops))
Proof
  rpt strip_tac >> drule_all regular_inst_prepared_emit_marked >>
  disch_then (qspec_then `o2pc`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >>
  suspend "emitted"
QED

Resume regular_inst_ok_sim_marked_count[emitted]:
  `EVERY (\s. case s of SOSpill k => k < dimword(:256)
     | SORestore k => k < dimword(:256) | _ => T) optops` by
    gvs[EVERY_APPEND] >>
  `spill_alloc_layout_wf emitted.ps_alloc emitted.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  `(if inst.inst_outputs = [] \/ is_halting then ([],emitted)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out next_liveness)
      inst.inst_outputs)) emitted) = (popops,popped)` by
    (`~(LENGTH inst.inst_outputs > 1)` by decide_tac >>
     qpat_x_assum `if inst.inst_outputs = [] \/ _ then (popops,popped) = _ else _` mp_tac >>
     qpat_x_assum `~(LENGTH inst.inst_outputs > 1)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> IF_CASES_TAC >> gvs[]) >>
  `(if FILTER (\out. MEM out next_liveness) inst.inst_outputs = [] then ([],popped)
    else optimistic_swap_plan dfg inst next_liveness next_is_term popped) = (optops,tail)` by
    (qpat_x_assum `if inst.inst_outputs = [] \/ FILTER _ _ = [] then _ else _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `inst.inst_outputs = []` >> simp[] >> IF_CASES_TAC >> simp[]) >>
  drule_all regular_generated_postfix_sim_numeric >>
  disch_then (qspec_then `o2pc` (qx_choose_then `endpoint` strip_assume_tac)) >>
  suspend "postfix_done"
QED

Resume regular_inst_ok_sim_marked_count[postfix_done]:
  qexistsl_tac [`LENGTH (execute_plan initial_fmp (iops ++ rops)) +
    (1 + LENGTH (execute_plan initial_fmp (popops ++ optops)))`, `endpoint`] >>
  conj_tac
  >- (irule asm_steps_compose_ok >> qexists `mid` >> conj_tac
      >- asm_rewrite_tac[] >>
      irule asm_steps_compose_ok >> qexists `after_emit` >> asm_rewrite_tac[]) >>
  conj_tac >- asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `ops = _` SUBST1_TAC >>
  qpat_x_assum `endpoint.as_pc = _` mp_tac >>
  qpat_x_assum `after_emit.as_pc = _` mp_tac >>
  qpat_x_assum `mid.as_pc = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac[execute_plan_append, execute_plan_def, APPEND, LENGTH_APPEND, LENGTH] >>
  simp[exec_stack_op_def] >> decide_tac
QED

Finalise regular_inst_ok_sim_marked_count

Theorem regular_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label spill_base ps vs as ops ps' name initial_fmp.
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked spill_base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_regular_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) /\
    step_inst fuel ctx inst vs = OK vs' /\
    inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all regular_inst_ok_sim_marked_count >> metis_tac[]
QED

Theorem marked_operand_owned:
  !op ps.
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op) ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled
Proof
  rpt strip_tac
  >- (fs[stack_get_depth_def, optionTheory.IS_SOME_EXISTS] >>
      drule stack_find_el >> drule planWfTheory.stack_find_bound >>
      metis_tac[MEM_EL, MEM_REVERSE]) >>
  Cases_on `op IN FDOM ps.ps_spilled` >> fs[finite_mapTheory.FLOOKUP_DEF]
QED

(* The marked input preparation of a single operand, leaving its value on
   top of the assembly stack. *)
Theorem marked_single_prefix_top:
  !opc op nl ps inp p1 dfg reo p2 lo vs st o2pc prog initial_fmp suffix v sb.
    emit_input_plan opc [op] nl ps = (inp,p1) /\
    reorder_plan dfg [op] p1 = (reo,p2) /\
    opc <> INVOKE /\
    generated_plan_state_wf_marked sb ps /\
    (is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) /\
    op <> dead_stack_marker /\
    (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
    (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ at = op) /\
      operand_equiv dfg op at ==>
      operand_val vs lo op = operand_val vs lo at) /\
    eval_operand op vs = operand_val vs lo op /\
    eval_operand op vs = SOME v /\
    1 <= LENGTH p1.ps_stack /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) (inp ++ reo) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp (inp ++ reo ++ suffix)) ==>
    ?st2 rest.
      asm_steps lo o2pc prog
        (LENGTH (execute_plan initial_fmp (inp ++ reo))) st = AsmOK st2 /\
      venom_asm_rel lo p2 vs st2 /\
      st2.as_stack = v :: rest /\
      asm_block_at prog st2.as_pc (execute_plan initial_fmp suffix) /\
      st2.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (inp ++ reo)) /\
      plan_state_residual_wf_marked sb [op] 1 p2 /\
      p2.ps_stack = stack_pop 1 p2.ps_stack ++ [op]
Proof
  rpt gen_tac >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp (inp ++ reo)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp (inp ++ reo)))
     (execute_plan initial_fmp suffix)` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[execute_plan_append, asm_block_at_append, LENGTH_APPEND,
       APPEND_ASSOC, ADD_ASSOC] >> strip_tac >> asm_rewrite_tac[]) >>
  `!x. MEM x [op] /\ is_var_operand x ==>
     MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled` by
    (rw[] >> irule marked_operand_owned >> fs[]) >>
  `residual_budget_wf_marked sb [] ps` by
    metis_tac[generated_plan_state_wf_marked_residual_nil] >>
  `plan_slots_bounded sb ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  `PERM [op] [op]` by simp[] >>
  `LENGTH [op] <= 16 /\ LENGTH [op] <= LENGTH p1.ps_stack` by simp[] >>
  `!l. MEM (Label l) [op] ==> IS_SOME (FLOOKUP lo l)` by
    (rw[] >> metis_tac[]) >>
  `EVERY (\x. x <> dead_stack_marker /\
     !at. operand_equiv dfg x at ==> at <> dead_stack_marker) [op]` by
    (rw[] >> metis_tac[]) >>
  `!x at. MEM x [op] /\
     (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [op]) /\
     operand_equiv dfg x at ==>
     operand_val vs lo x = operand_val vs lo at` by
    (rw[] >> metis_tac[]) >>
  `eval_operands [op] vs = SOME [v]` by
    (qpat_x_assum `eval_operand op vs = SOME v` (fn th =>
       PURE_REWRITE_TAC [eval_operands_def, th]) >> simp[]) >>
  `!x. MEM x [op] ==> eval_operand x vs = operand_val vs lo x` by
    (PURE_REWRITE_TAC [MEM, OR_CLAUSES] >> rpt strip_tac >>
     BasicProvers.VAR_EQ_TAC >> first_assum ACCEPT_TAC) >>
  `EVERY (\x. x <> dead_stack_marker) [op]` by
    (PURE_REWRITE_TAC [EVERY_DEF, AND_CLAUSES] >> BETA_TAC >>
     first_assum ACCEPT_TAC) >>
  `LENGTH [op:operand] = 1` by simp[] >>
  drule_all selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `st'.as_stack = [v] ++ DROP (LENGTH [op]) st'.as_stack` by
    (mp_tac (Q.SPECL [`lo`, `p2`, `vs`, `st'`,
       `stack_pop (LENGTH [op:operand]) p2.ps_stack`, `[op]`, `[v]`]
       (Q.GENL [`lo`, `ps`, `vs`, `st`, `residual`, `operands`, `values`]
          arranged_eval_operands_stack)) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         PURE_REWRITE_TAC [REVERSE_DEF, APPEND] >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `LENGTH [op:operand] = 1` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qexistsl_tac [`st'`, `DROP 1 st'.as_stack`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_x_assum `st'.as_stack = _` (fn th =>
        CONV_TAC (LAND_CONV (REWR_CONV th))) >>
      REWRITE_TAC [APPEND]) >>
  qpat_x_assum `st'.as_pc = _` (fn th => REWRITE_TAC [th]) >>
  first_assum ACCEPT_TAC
QED

(* The marked input preparation of operands kept in their own order. *)
Theorem marked_prefix_sim:
  !opc operands nl ps iops prepared dfg rops arranged lo vs st o2pc prog
   initial_fmp sb.
    opc <> INVOKE /\
    generated_plan_state_wf_marked sb ps /\
    (!op. MEM op operands /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
    (!op at. MEM op operands /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
      operand_equiv dfg op at ==>
      operand_val vs lo op = operand_val vs lo at) /\
    emit_input_plan opc operands nl ps = (iops,prepared) /\
    reorder_plan dfg operands prepared = (rops,arranged) /\
    LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) (iops ++ rops) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
    plan_state_residual_wf_marked sb operands (LENGTH operands) arranged /\
    arranged.ps_stack =
      stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
    ?st'. asm_steps lo o2pc prog
            (LENGTH (execute_plan initial_fmp (iops ++ rops))) st = AsmOK st' /\
      venom_asm_rel lo arranged vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[marked_operand_owned] >>
  `residual_budget_wf_marked sb [] ps` by
    metis_tac[generated_plan_state_wf_marked_residual_nil] >>
  `plan_slots_bounded sb ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  `PERM operands operands` by simp[] >>
  drule_all selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  goal_assum drule >> simp[]
QED

(* genBlockSim's assign_postfix_sim on the numeric cleanup chain. *)
Theorem assign_postfix_sim_numeric:
  !ps6 out nl halting dfg inst term pops ps8 opts ps9 lo o2pc prog vs st
   initial_fmp.
    spill_alloc_layout_wf ps6.ps_alloc ps6.ps_spilled /\
    (if halting then ([], ps6)
     else popmany_plan (if MEM out nl then [] else [Var out]) ps6) =
      (pops, ps8) /\
    (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
     else ([], ps8)) = (opts, ps9) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) (pops ++ opts) /\
    venom_asm_rel lo ps6 vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp (pops ++ opts)) ==>
    ?st9.
      asm_steps lo o2pc prog
        (LENGTH (execute_plan initial_fmp (pops ++ opts))) st = AsmOK st9 /\
      venom_asm_rel lo (release_dead_spills nl ps9) vs st9 /\
      st9.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (pops ++ opts))
Proof
  rpt gen_tac >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp pops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp pops))
     (execute_plan initial_fmp opts)` by
    fs[execute_plan_append, asm_block_at_append] >>
  `?st8. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp pops)) st =
       AsmOK st8 /\
     venom_asm_rel lo ps8 vs st8 /\
     st8.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp pops) /\
     spill_alloc_layout_wf ps8.ps_alloc ps8.ps_spilled` by
    (Cases_on `halting` >> gvs[]
     >- (qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
     drule popmany_plan_sim_numeric >>
     disch_then (qspecl_then [`lo`, `o2pc`, `prog`, `vs`, `st`,
       `initial_fmp`] mp_tac) >>
     impl_tac >- fs[EVERY_APPEND] >>
     strip_tac >> qexists `st'` >> simp[]) >>
  `?st9. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp opts)) st8 =
       AsmOK st9 /\
     venom_asm_rel lo ps9 vs st9 /\
     st9.as_pc = st8.as_pc + LENGTH (execute_plan initial_fmp opts)` by
    (Cases_on `MEM out nl` >> gvs[]
     >- (drule optimistic_swap_sim_numeric >>
         disch_then (qspecl_then [`lo`, `o2pc`, `prog`, `vs`, `st8`,
           `initial_fmp`] mp_tac) >>
         impl_tac >- fs[EVERY_APPEND] >>
         strip_tac >> qexists `st'` >> simp[]) >>
     qexists `st8` >> simp[execute_plan_def, asm_steps_def]) >>
  qexists `st9` >> rpt conj_tac
  >- (PURE_REWRITE_TAC [execute_plan_append, LENGTH_APPEND] >>
      irule asm_steps_compose_ok >> qexists `st8` >> simp[])
  >- (irule venom_asm_rel_release_dead_spills >> simp[]) >>
  simp[execute_plan_append]
QED

(* The ASSIGN case of gen_inst_ok_sim_marked. *)
Theorem assign_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ASSIGN /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `vs'` >> strip_tac >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  drule_all step_inst_assign_ok >> strip_tac >>
  Cases_on `emit_input_plan ASSIGN [op] next_liveness ps` >>
  rename1 `emit_input_plan ASSIGN [op] next_liveness ps = (iops, ps1)` >>
  Cases_on `reorder_plan dfg [op] ps1` >>
  rename1 `reorder_plan dfg [op] ps1 = (rops, ps4)` >>
  drule_all assign_plan_decompose >>
  disch_then (qspecl_then
    [`liveness`, `cfg`, `fn`, `is_halting`, `next_is_term`, `bb_label`]
    strip_assume_tac) >>
  gvs[compute_operands_def, python_stack_operands_def] >>
  qmatch_asmsub_abbrev_tac `popmany_plan _ ps6` >>
  `asm_block_at prog as.as_pc (execute_plan initial_fmp (iops ++ rops)) /\
   asm_block_at prog
     (as.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)))
     (execute_plan initial_fmp (pops ++ opts))` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     pure_rewrite_tac[execute_plan_append, asm_block_at_append, LENGTH_APPEND,
                      ADD_ASSOC] >>
     disch_then strip_assume_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~MEM (Var out) ps.ps_stack` by
    (qpat_x_assum `EVERY _ ps.ps_stack` mp_tac >>
     rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `Var out` mp_tac) >> simp[]) >>
  `Var out NOTIN FDOM ps.ps_spilled` by
    (qpat_x_assum `!op'. op' IN FDOM ps.ps_spilled ==> _`
       (qspec_then `Var out` mp_tac) >> simp[]) >>
  `operand_val vs lo op = SOME v` by (sym_tac >> first_assum ACCEPT_TAC) >>
  `EVERY (\s. case s of SOSpill k => k < dimword(:256)
     | SORestore k => k < dimword(:256) | _ => T) (iops ++ rops) /\
   EVERY (\s. case s of SOSpill k => k < dimword(:256)
     | SORestore k => k < dimword(:256) | _ => T) (pops ++ opts)` by
    fs[EVERY_APPEND] >>
  qspecl_then [`ASSIGN`, `[op]`, `next_liveness`, `ps`, `iops`, `ps1`,
    `dfg`, `rops`, `ps4`, `lo`, `vs`, `as`, `o2pc`, `prog`,
    `initial_fmp`, `base'`] mp_tac marked_prefix_sim >>
  (impl_tac >- (ASM_REWRITE_TAC[] >> fs[] >> metis_tac[])) >>
  strip_tac >>
  rename1 `venom_asm_rel lo ps4 vs st4` >>
  `ps4.ps_stack = stack_pop 1 ps4.ps_stack ++ [op] /\
   spill_alloc_layout_wf ps4.ps_alloc ps4.ps_spilled` by
    fs[plan_state_residual_wf_marked_def] >>
  `~MEM (Var out) ps1.ps_stack /\ Var out NOTIN FDOM ps1.ps_spilled` by
    (drule_all emit_input_plan_preserves_not_mem >> simp[]) >>
  `~MEM (Var out) ps4.ps_stack /\ Var out NOTIN FDOM ps4.ps_spilled` by
    (drule (SIMP_RULE (srw_ss()) []
       (Q.SPECL [`dfg`, `[op]`] reorder_plan_preserves_not_mem_reachable)) >>
     disch_then drule_all >> simp[]) >>
  `0 < LENGTH ps4.ps_stack /\ stack_peek 0 ps4.ps_stack = op` by
    (qpat_x_assum `ps4.ps_stack = _` (fn th => once_rewrite_tac[th]) >>
     simp[stack_peek_def, EL_APPEND_EQN]) >>
  `stack_push (Var out) (stack_pop 1 ps4.ps_stack) =
   stack_poke 0 (Var out) ps4.ps_stack` by
    (Cases_on `ps4.ps_stack` using SNOC_CASES >>
     gvs[stack_push_def, stack_pop_def, stack_poke_def, LUPDATE_SNOC,
         SNOC_APPEND, TAKE_APPEND]) >>
  `venom_asm_rel lo ps6 (update_var out v vs) st4` by
    (simp[Abbr `ps6`] >>
     qpat_x_assum `stack_push _ _ = stack_poke _ _ _`
       (fn th => rewrite_tac[th]) >>
     irule venom_asm_rel_poke_update_var >>
     rpt conj_tac
     >- (Cases >> simp[] >> metis_tac[])
     >- (qpat_x_assum `stack_peek 0 ps4.ps_stack = op`
           (fn th => REWRITE_TAC [th]) >> metis_tac[])
     >- first_assum ACCEPT_TAC
     >- (qpat_x_assum `stack_peek 0 ps4.ps_stack = op`
           (fn th => REWRITE_TAC [th]) >> first_assum ACCEPT_TAC)
     >- (simp[EVERY_MEM] >> Cases >> simp[] >> metis_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `spill_alloc_layout_wf ps6.ps_alloc ps6.ps_spilled` by
    simp[Abbr `ps6`] >>
  `asm_block_at prog st4.as_pc (execute_plan initial_fmp (pops ++ opts))` by
    (qpat_x_assum `st4.as_pc = _` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all assign_postfix_sim_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexistsl [`LENGTH (execute_plan initial_fmp (iops ++ rops)) +
             LENGTH (execute_plan initial_fmp (pops ++ opts))`, `st9`] >>
  conj_tac >- (irule asm_steps_compose_ok >> goal_assum drule >> simp[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[execute_plan_append, LENGTH_APPEND] >>
  qpat_x_assum `st9.as_pc = _` SUBST1_TAC >>
  qpat_x_assum `st4.as_pc = _` SUBST1_TAC >>
  pure_rewrite_tac[execute_plan_append, LENGTH_APPEND] >> decide_tac
QED

(* The LOG case of gen_inst_ok_sim_marked. *)
Theorem log_inst_ok_sim_marked_count:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = LOG /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops)) /\
        n = LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  drule_all step_inst_log_ok >> strip_tac >>
  drule_all log_plan_decompose >> strip_tac >>
  `compute_operands inst = rest` by simp[compute_operands_def] >>
  `asm_block_at prog as.as_pc
     (execute_plan initial_fmp (input_ops ++ reorder_ops))` by
    (fs[execute_plan_append, asm_block_at_append]) >>
  `EVERY (\s. case s of SOSpill k => k < dimword(:256)
     | SORestore k => k < dimword(:256) | _ => T)
     (input_ops ++ reorder_ops)` by fs[EVERY_APPEND] >>
  `LENGTH rest <= LENGTH ps1.ps_stack /\ LENGTH rest <= 16` by
    (qpat_x_assum `LENGTH (compute_operands inst) <= LENGTH _`
       mp_tac >> simp[] >> strip_tac >>
     qpat_x_assum `LENGTH (compute_operands inst) <= 16` mp_tac >> simp[]) >>
  qpat_assum `compute_operands inst = rest`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `LOG <> INVOKE` by simp[] >>
  drule_all marked_prefix_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps4 vs mid` >>
  drule_all log_runtime_stack >> strip_tac >>
  drule_all log_read_disjoint_emit >> disch_then assume_tac >>
  `w2n tc <= 4` by fs[] >>
  `asm_block_at prog mid.as_pc
     [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))]` by
    (qpat_x_assum `ps4.ps_stack = _` kall_tac >>
     fs[execute_plan_append, execute_plan_def, exec_stack_op_def,
        asm_block_at_append]) >>
  drule_all log_emit_step_rel >>
  disch_then (qspecl_then [`o2pc`, `next_liveness`] strip_assume_tac) >>
  qpat_x_assum `ps4.ps_stack = _` kall_tac >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops)) + 1`, `st'`] >>
  conj_tac >- simp[asm_steps_add] >>
  conj_tac >- (qpat_x_assum `venom_asm_rel lo (release_dead_spills _ _) _ st'`
                 mp_tac >> simp[]) >>
  simp[execute_plan_append, execute_plan_def, exec_stack_op_def]
QED

Theorem log_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = LOG /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
      ps'.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    inst_wf inst /\
    (inst.inst_opcode = LOG ==>
      ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <= LENGTH (SND (emit_input_plan inst.inst_opcode
      (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
      EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
      ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
        FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==> eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
      operand_equiv dfg op at ==> operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==> EVERY
      (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    (!dist prev val_op. inst.inst_opcode = PHI /\
      stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
      vs.vs_prev_bb = SOME prev /\ resolve_phi prev inst.inst_operands = SOME val_op ==>
      operand_val vs lo (stack_peek dist ps.ps_stack) = eval_operand val_op vs) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\ n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting next_is_term
      bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
      inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
          as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all log_inst_ok_sim_marked_count >> metis_tac[]
QED

(* The ASSERT case of gen_inst_ok_sim_marked. *)
Theorem assert_inst_ok_sim_marked_count:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ASSERT /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops)) /\
        n = LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  drule_at (Pat `step_inst _ _ _ _ = OK _`) step_inst_assert_ok >>
  simp[] >> strip_tac >>
  drule_all assert_plan_decompose >> strip_tac >> gvs[] >>
  `?st2 rest.
     asm_steps lo o2pc prog
       (LENGTH (execute_plan initial_fmp (inp ++ reo))) as = AsmOK st2 /\
     venom_asm_rel lo p2 vs st2 /\ st2.as_stack = v :: rest /\
     asm_block_at prog st2.as_pc
       (execute_plan initial_fmp
         [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]) /\
     st2.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp (inp ++ reo))` by
    (mp_tac (Q.SPECL [`ASSERT`, `cond`, `next_liveness`, `ps`, `inp`, `p1`,
       `dfg`, `reo`, `p2`, `lo`, `vs`, `as`, `o2pc`, `prog`, `initial_fmp`,
       `[SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]`, `v`, `base'`] marked_single_prefix_top) >>
     impl_tac >- (fs[EVERY_APPEND] >> metis_tac[]) >>
     strip_tac >> metis_tac[]) >>
  `asm_block_at prog st2.as_pc
     [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]` by
    fs[execute_plan_def, exec_stack_op_def] >>
  drule_all asm_assert_nonzero >>
  disch_then (qspecl_then [`o2pc`] assume_tac) >>
  `LENGTH (execute_plan initial_fmp
      (inp ++ reo ++ [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"])) =
    LENGTH (execute_plan initial_fmp (inp ++ reo)) + 3` by
    simp[execute_plan_append, execute_plan_def, exec_stack_op_def] >>
  qpat_x_assum `LENGTH (execute_plan initial_fmp (inp ++ reo ++ _)) = _`
    (rewrite_tac o single) >>
  qexists `st2 with <|as_stack := rest; as_pc := st2.as_pc + 3|>` >>
  conj_tac
  >- (irule asm_steps_compose_ok >> goal_assum $ drule_at Any >> simp[]) >>
  conj_tac
  >- (irule venom_asm_rel_release_dead_spills >>
      irule venom_asm_rel_consume_one >> goal_assum $ drule_at Any >> simp[]) >>
  simp[execute_plan_append, execute_plan_def, exec_stack_op_def] >> decide_tac
QED

Theorem assert_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ASSERT /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
      ps'.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    inst_wf inst /\
    (inst.inst_opcode = LOG ==>
      ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <= LENGTH (SND (emit_input_plan inst.inst_opcode
      (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
      EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
      ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
        FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==> eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
      operand_equiv dfg op at ==> operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==> EVERY
      (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    (!dist prev val_op. inst.inst_opcode = PHI /\
      stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
      vs.vs_prev_bb = SOME prev /\ resolve_phi prev inst.inst_operands = SOME val_op ==>
      operand_val vs lo (stack_peek dist ps.ps_stack) = eval_operand val_op vs) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\ n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting next_is_term
      bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
      inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
          as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all assert_inst_ok_sim_marked_count >> metis_tac[]
QED

(* The ASSERT_UNREACHABLE case of gen_inst_ok_sim_marked. *)
Theorem assert_unreachable_inst_ok_sim_marked_count:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ASSERT_UNREACHABLE /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops)) /\
        n = LENGTH (execute_plan initial_fmp ops) - 1
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  drule_at (Pat `step_inst _ _ _ _ = OK _`) step_inst_assert_ok >>
  simp[] >> strip_tac >>
  drule_all assert_unreachable_plan_decompose >> strip_tac >> gvs[] >>
  `?st2 rest.
     asm_steps lo o2pc prog
       (LENGTH (execute_plan initial_fmp (inp ++ reo))) as = AsmOK st2 /\
     venom_asm_rel lo p2 vs st2 /\ st2.as_stack = v :: rest /\
     asm_block_at prog st2.as_pc
       (execute_plan initial_fmp
         [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl]) /\
     st2.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp (inp ++ reo))` by
    (mp_tac (Q.SPECL [`ASSERT_UNREACHABLE`, `cond`, `next_liveness`, `ps`, `inp`, `p1`,
       `dfg`, `reo`, `p2`, `lo`, `vs`, `as`, `o2pc`, `prog`, `initial_fmp`,
       `[SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl]`, `v`, `base'`] marked_single_prefix_top) >>
     impl_tac >- (fs[EVERY_APPEND] >> metis_tac[]) >>
     strip_tac >> metis_tac[]) >>
  qpat_x_assum `!lbl' i. _` (qspecl_then
    [`lbl`, `LENGTH (execute_plan initial_fmp (inp ++ reo)) + 3`] mp_tac) >>
  simp[execute_plan_append, execute_plan_def, exec_stack_op_def,
       EL_APPEND_EQN] >> strip_tac >>
  `FLOOKUP o2pc off = SOME (st2.as_pc + 3)` by
    (qpat_x_assum `FLOOKUP o2pc off = _` mp_tac >>
     fs[execute_plan_append, execute_plan_def] >> strip_tac >>
     AP_TERM_TAC >> decide_tac) >>
  `asm_block_at prog st2.as_pc
     [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl]` by
    fs[execute_plan_def, exec_stack_op_def] >>
  drule_all asm_assert_unreachable_nonzero >> strip_tac >>
  `asm_steps lo o2pc prog
      (LENGTH (execute_plan initial_fmp (inp ++ reo)) + 3) as =
    AsmOK (st2 with <|as_stack := rest; as_pc := st2.as_pc + 4|>)` by
    (irule asm_steps_compose_ok >> goal_assum $ drule_at Any >> simp[]) >>
  `LENGTH (execute_plan initial_fmp
      (inp ++ reo ++ [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl])) =
    LENGTH (execute_plan initial_fmp (inp ++ reo)) + 4` by
    simp[execute_plan_append, execute_plan_def, exec_stack_op_def] >>
  qpat_x_assum `LENGTH (execute_plan initial_fmp (inp ++ reo ++ _)) = _`
    (rewrite_tac o single) >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_SUB] >>
  qexists `st2 with <|as_stack := rest; as_pc := st2.as_pc + 4|>` >>
  conj_tac
  >- gvs[execute_plan_append, execute_plan_def] >>
  conj_tac
  >- (irule venom_asm_rel_release_dead_spills >>
      irule venom_asm_rel_fresh_label >> goal_assum $ drule_at Any >>
      irule venom_asm_rel_consume_one >> goal_assum $ drule_at Any >> simp[]) >>
  simp[execute_plan_append, execute_plan_def, exec_stack_op_def] >> decide_tac
QED

Theorem assert_unreachable_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ASSERT_UNREACHABLE /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
      ps'.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    inst_wf inst /\
    (inst.inst_opcode = LOG ==>
      ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <= LENGTH (SND (emit_input_plan inst.inst_opcode
      (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
      EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
      ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
        FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==> eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
      operand_equiv dfg op at ==> operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==> EVERY
      (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    (!dist prev val_op. inst.inst_opcode = PHI /\
      stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
      vs.vs_prev_bb = SOME prev /\ resolve_phi prev inst.inst_operands = SOME val_op ==>
      operand_val vs lo (stack_peek dist ps.ps_stack) = eval_operand val_op vs) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\ n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting next_is_term
      bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
      inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
          as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all assert_unreachable_inst_ok_sim_marked_count >> metis_tac[]
QED

(* genBlockSim's phi_dup_rename_sim on the numeric do_dup simulation. *)
Theorem phi_dup_rename_sim_numeric:
  !d ps ds p lo o2pc prog vs st out v tail initial_fmp.
    do_dup d ps = (ds,p) /\ d < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    operand_val vs lo (stack_peek d ps.ps_stack) = SOME v /\
    stack_peek d ps.ps_stack <> dead_stack_marker /\
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
      case op of Var x => x <> out | _ => T) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ds /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp (ds ++ tail)) ==>
    ?mid. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ds)) st = AsmOK mid /\
      venom_asm_rel lo (p with ps_stack := stack_poke 0 (Var out) p.ps_stack)
        (update_var out v vs) mid /\
      mid.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ds) /\
      asm_block_at prog mid.as_pc (execute_plan initial_fmp tail)
Proof
  rpt strip_tac >>
  gvs[execute_plan_append, asm_block_at_append] >>
  drule_all do_dup_venom_asm_rel_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `p.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
    (drule do_dup_stack_exact >> simp[]) >>
  `p.ps_spilled = ps.ps_spilled` by
    (qspecl_then [`d`, `ps`] mp_tac do_dup_layout_wf >> simp[]) >>
  `venom_asm_rel lo (p with ps_stack := stack_poke 0 (Var out) p.ps_stack)
     (update_var out v vs) st'` by
    (irule venom_asm_rel_poke_update_var >>
     qpat_x_assum `p.ps_stack = _` (fn th => REWRITE_TAC [th]) >>
     qpat_x_assum `p.ps_spilled = _` (fn th => REWRITE_TAC [th]) >>
     simp[stack_peek_def, EVERY_APPEND, EL_APPEND_EQN] >>
     `MEM (stack_peek d ps.ps_stack) ps.ps_stack` by
       (simp[stack_peek_def, MEM_EL] >>
        qexists `LENGTH ps.ps_stack - 1 - d` >> simp[]) >>
     gvs[EVERY_MEM, stack_peek_def] >> metis_tac[]) >>
  qpat_x_assum `p.ps_stack = _` kall_tac >>
  qpat_x_assum `p.ps_spilled = _` kall_tac >>
  qexists `st'` >> simp[]
QED

(* The PHI case of gen_inst_ok_sim_marked. *)
Theorem phi_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = PHI /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_inst_plan_def, is_param_opcode_def] >>
  strip_tac >> gvs[] >>
  (* Extract vs' from step_inst PHI = OK vs' *)
  `?out prev val_op v.
     inst.inst_outputs = [out] /\
     vs.vs_prev_bb = SOME prev /\
     resolve_phi prev inst.inst_operands = SOME val_op /\
     eval_operand val_op vs = SOME v /\
     vs' = update_var out v vs` by (
    qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
    simp[Once step_inst_def] >>
    `inst.inst_opcode <> INVOKE` by simp[] >> simp[] >>
    simp[step_inst_base_def] >>
    `?h. inst.inst_outputs = [h]` by (
      qpat_x_assum `inst_wf _` mp_tac >>
      simp[inst_wf_def] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      Cases_on `t` >> simp[]) >>
    simp[] >>
    Cases_on `vs.vs_prev_bb` >> simp[] >>
    Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
    Cases_on `eval_operand x' vs` >> simp[] >>
    strip_tac >> gvs[] >>
    metis_tac[]) >>
  gvs[] >>
  (* Unfold generate_phi_plan and case split *)
  qpat_x_assum `generate_phi_plan _ _ _ _ = _` mp_tac >>
  simp[generate_phi_plan_def, LET_THM] >>
  suspend "phi_cases"
QED

Resume phi_inst_ok_sim_marked[phi_cases]:
  strip_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
              ps.ps_stack`
  >- (
    (* NONE case: ops = [], ps' = ps *)
    gvs[] >>
    Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `as` >>
    simp[asm_steps_def, execute_plan_def] >>
    irule venom_asm_rel_update_var >>
    gvs[EVERY_MEM] >>
    rpt strip_tac >> res_tac >> gvs[]
  )
  >- (
    (* SOME dist case: stack has a phi var at depth x *)
    gvs[] >> pairarg_tac >> gvs[] >>
    `x < LENGTH ps.ps_stack` by
      (fs[stack_get_phi_depth_def] >> drule stack_find_bound >> simp[]) >>
    `stack_peek x ps.ps_stack <> dead_stack_marker` by
      (drule stack_get_phi_depth_var_not_marker >> simp[]) >>
    qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
    IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
    >- suspend "phi_live"
    >- suspend "phi_dead"
  )
QED

Resume phi_inst_ok_sim_marked[phi_dead]:
  `venom_asm_rel lo
     (ps with ps_stack := stack_poke x (Var out) ps.ps_stack)
     (update_var out v vs) as` by
    (irule venom_asm_rel_poke_update_var >> simp[]) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  IF_CASES_TAC >> simp[]
  >- suspend "phi_dead_pop"
  >> strip_tac >> gvs[] >>
  qexistsl [`0`, `as`] >>
  simp[asm_steps_def, execute_plan_def, exec_stack_op_def]
QED

Resume phi_inst_ok_sim_marked[phi_dead_pop]:
  pairarg_tac >> strip_tac >> gvs[] >>
  `asm_block_at prog as.as_pc (execute_plan initial_fmp pop_ops)` by
    fs[execute_plan_def, exec_stack_op_def] >>
  drule popmany_plan_sim_numeric >>
  disch_then (qspecl_then [`lo`, `o2pc`, `prog`, `update_var out v vs`,
    `as`, `initial_fmp`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
  strip_tac >>
  qexistsl [`LENGTH (execute_plan initial_fmp pop_ops)`, `st'`] >>
  simp[execute_plan_def, exec_stack_op_def]
QED

Resume phi_inst_ok_sim_marked[phi_live]:
  pairarg_tac >> gvs[] >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  IF_CASES_TAC >> simp[]
  >- suspend "phi_live_pop"
  >> strip_tac >> gvs[] >>
  drule_all phi_dup_rename_sim_numeric >>
  disch_then (qspecl_then [`o2pc`] mp_tac) >>
  strip_tac >> qexistsl [`LENGTH (execute_plan initial_fmp dup_ops)`, `mid`] >>
  simp[execute_plan_append, execute_plan_def, exec_stack_op_def]
QED

Resume phi_inst_ok_sim_marked[phi_live_pop]:
  pairarg_tac >> strip_tac >> gvs[] >>
  `ps1.ps_stack = ps.ps_stack ++ [stack_peek x ps.ps_stack]` by
    (drule do_dup_stack_exact >> simp[]) >>
  `stack_poke 0 (Var out) ps1.ps_stack = ps.ps_stack ++ [Var out]` by
    simp[stack_poke_def, LUPDATE_APPEND2] >>
  qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
  simp[popmany_plan_def, is_contiguous_top_def, stack_get_depth_def,
       stack_find_def, REVERSE_APPEND, stack_pop_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF, popmany_individual_def, do_swap_def] >>
  strip_tac >> gvs[] >>
  `asm_block_at prog as.as_pc
     (execute_plan initial_fmp (dup_ops ++ [SOPoke 0 (Var out); SOPop 1]))` by
    fs[execute_plan_append, execute_plan_def, exec_stack_op_def] >>
  drule_all phi_dup_rename_sim_numeric >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "phi_live_pop_finish"
QED

Resume phi_inst_ok_sim_marked[phi_live_pop_finish]:
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp [SOPop 1])` by
    gvs[execute_plan_def, exec_stack_op_def] >>
  qspecl_then [`[SOPop 1]`, `initial_fmp`, `lo`, `o2pc`, `prog`,
    `ps1 with ps_stack := stack_poke 0 (Var out) ps1.ps_stack`,
    `update_var out v vs`, `mid`] mp_tac simple_prefix_venom_asm_rel >>
  (impl_tac >-
    simp[is_simple_stack_op_def, prefix_wf_def, stack_op_wf_def,
         stack_poke_def]) >>
  strip_tac >>
  qexistsl [`LENGTH (execute_plan initial_fmp dup_ops) +
              LENGTH (execute_plan initial_fmp [SOPop 1])`, `st'`] >>
  conj_tac
  >- (irule asm_steps_compose_ok >> qexists `mid` >> simp[]) >>
  gvs[apply_simple_ops_def, apply_simple_op_def, stack_pop_def,
      execute_plan_append, execute_plan_def, exec_stack_op_def]
QED

Finalise phi_inst_ok_sim_marked

(* The INITIAL_FMP case of gen_inst_ok_sim_marked. *)
Theorem initial_fmp_inst_ok_sim_marked_count:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = INITIAL_FMP /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops)) /\
        n = LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  CONV_TAC (BINDER_CONV (BINDER_CONV
    (RAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV arithmeticTheory.EQ_LESS_EQ)))))) >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_marked_def] >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_inst_plan_def, is_param_opcode_def] >>
  strip_tac >> gvs[is_param_opcode_def] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       python_stack_operands_def,
       ir_specific_operand_order_def, is_commutative_def,
       generate_emit_ops_def] >>
  `?out. inst.inst_outputs = [out]` by (
    Cases_on `inst.inst_outputs` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[] >> rpt strip_tac >>
  `~MEM (Var out) ps.ps_stack` by (
    qpat_x_assum `EVERY _ ps.ps_stack`
      (fn th => assume_tac (REWRITE_RULE [EVERY_MEM] th)) >>
    strip_tac >>
    qpat_x_assum `!op. MEM op ps.ps_stack ==> _`
      (qspec_then `Var out` mp_tac) >>
    simp[]) >>
  `Var out NOTIN FDOM ps.ps_spilled` by (
    strip_tac >> qpat_x_assum `!op. op IN FDOM _ ==> _`
      (qspec_then `Var out` mp_tac) >> simp[]) >>
  Cases_on `is_halting`
  >- (reverse (Cases_on `MEM out next_liveness`)
      >- (gvs[initial_fmp_dead_popmany] >>
          qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
            `initial_fmp`, `out`] mp_tac initial_fmp_emit_update_var_bridge >>
          (impl_tac >- ASM_REWRITE_TAC[]) >> strip_tac >>
          qexistsl [`1`, `as'`] >> ASM_REWRITE_TAC[] >>
          conj_tac
          >- (irule venom_asm_rel_release_dead_spills >>
              simp[stack_push_def, stack_pop_def]) >>
          simp[execute_plan_def, exec_stack_op_def]) >>
      gvs[initial_fmp_dead_popmany] >>
      pairarg_tac >> gvs[] >>
      qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
        `initial_fmp`, `out`] mp_tac initial_fmp_emit_update_var_bridge >>
      (impl_tac >-
        (ASM_REWRITE_TAC[] >>
         qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
         simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons])) >>
      strip_tac >>
      `venom_asm_rel lo
         (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))
         (update_var out vs.vs_initial_fmp vs) as'` by
        (qpat_x_assum `venom_asm_rel lo (ps with ps_stack := SNOC _ _) _ _`
           mp_tac >> simp[stack_push_def, stack_pop_def]) >>
      `asm_block_at prog as'.as_pc (execute_plan initial_fmp opt_ops)` by
        (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
         simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
         ASM_REWRITE_TAC[]) >>
      drule optimistic_swap_sim_numeric >>
      disch_then (qspecl_then [`lo`, `o2pc`, `prog`,
        `update_var out vs.vs_initial_fmp vs`, `as'`, `initial_fmp`] mp_tac) >>
      impl_tac >- fs[] >> strip_tac >>
      `venom_asm_rel lo (release_dead_spills next_liveness ps9)
         (update_var out vs.vs_initial_fmp vs) st'` by
        (irule venom_asm_rel_release_dead_spills >> ASM_REWRITE_TAC[]) >>
      qexistsl [`1 + LENGTH (execute_plan initial_fmp opt_ops)`, `st'`] >>
      gvs[asm_steps_add, execute_plan_def, exec_stack_op_def]) >>
  Cases_on `MEM out next_liveness`
  >- (gvs[initial_fmp_dead_popmany, popmany_plan_def] >>
      pairarg_tac >> gvs[] >>
      qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
        `initial_fmp`, `out`] mp_tac initial_fmp_emit_update_var_bridge >>
      (impl_tac >-
        (ASM_REWRITE_TAC[] >>
         qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
         simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons])) >>
      strip_tac >>
      `venom_asm_rel lo
         (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))
         (update_var out vs.vs_initial_fmp vs) as'` by
        (qpat_x_assum `venom_asm_rel lo (ps with ps_stack := SNOC _ _) _ _`
           mp_tac >> simp[stack_push_def, stack_pop_def]) >>
      `asm_block_at prog as'.as_pc (execute_plan initial_fmp opt_ops)` by
        (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
         simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
         ASM_REWRITE_TAC[]) >>
      drule optimistic_swap_sim_numeric >>
      disch_then (qspecl_then [`lo`, `o2pc`, `prog`,
        `update_var out vs.vs_initial_fmp vs`, `as'`, `initial_fmp`] mp_tac) >>
      impl_tac >- fs[] >> strip_tac >>
      `venom_asm_rel lo (release_dead_spills next_liveness ps9)
         (update_var out vs.vs_initial_fmp vs) st'` by
        (irule venom_asm_rel_release_dead_spills >> ASM_REWRITE_TAC[]) >>
      qexistsl [`1 + LENGTH (execute_plan initial_fmp opt_ops)`, `st'`] >>
      gvs[asm_steps_add, execute_plan_def, exec_stack_op_def]) >>
  gvs[initial_fmp_dead_popmany, stack_push_def, stack_pop_def] >>
  qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
    `initial_fmp`, `out`] mp_tac initial_fmp_emit_update_var_bridge >>
  (impl_tac >-
    (ASM_REWRITE_TAC[] >>
     qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
     simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons])) >>
  strip_tac >>
  `asm_block_at prog as'.as_pc (execute_plan initial_fmp [SOPop 1])` by
    (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
     simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
     ASM_REWRITE_TAC[]) >>
  qspecl_then [`lo`, `o2pc`, `prog`, `initial_fmp`, `next_liveness`,
    `[SOPop 1]`,
    `ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack)`,
    `ps`, `release_dead_spills next_liveness ps`,
    `update_var out vs.vs_initial_fmp vs`, `as'`]
    mp_tac initial_fmp_generated_postfix_sim >>
  impl_tac
  >- (ASM_REWRITE_TAC[] >>
      simp[prefix_wf_def, stack_op_wf_def, is_prefix_op_def,
           prefix_spill_wf_def, spill_op_wf_def,
           apply_prefix_ops_def, apply_prefix_op_def, apply_simple_op_def,
           stack_push_def, stack_pop_def, SNOC_APPEND, TAKE_APPEND1,
           plan_state_component_equality] >>
      qpat_x_assum `venom_asm_rel lo (ps with ps_stack := SNOC _ _) _ _`
        mp_tac >> simp[SNOC_APPEND]) >>
  strip_tac >>
  qexistsl [`1 + LENGTH (execute_plan initial_fmp [SOPop 1])`, `as''`] >>
  gvs[asm_steps_add, execute_plan_def, exec_stack_op_def]
QED

Theorem initial_fmp_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = INITIAL_FMP /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
      ps'.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    inst_wf inst /\
    (inst.inst_opcode = LOG ==>
      ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <= LENGTH (SND (emit_input_plan inst.inst_opcode
      (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
      EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
      ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
        FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==> eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
      operand_equiv dfg op at ==> operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==> EVERY
      (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    (!dist prev val_op. inst.inst_opcode = PHI /\
      stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
      vs.vs_prev_bb = SOME prev /\ resolve_phi prev inst.inst_operands = SOME val_op ==>
      operand_val vs lo (stack_peek dist ps.ps_stack) = eval_operand val_op vs) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\ n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting next_is_term
      bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
      inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
          as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all initial_fmp_inst_ok_sim_marked_count >> metis_tac[]
QED

(* The BUMP case of gen_inst_ok_sim_marked. *)
Theorem bump_inst_ok_sim_marked_count:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = BUMP /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops)) /\
        n = LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  CONV_TAC (BINDER_CONV (BINDER_CONV
    (RAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV arithmeticTheory.EQ_LESS_EQ)))))) >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_inst_plan_def, is_param_opcode_def] >> strip_tac >>
  gvs[is_param_opcode_def] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       is_commutative_def, generate_emit_ops_def,
       bump_emit_ops_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[] >>
  rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  `compute_operands inst = [h;h']` by
    simp[compute_operands_def, python_stack_operands_def,
         ir_specific_operand_order_def] >>
  fs[python_stack_operands_def, ir_specific_operand_order_def] >>
  `asm_block_at prog as.as_pc
     (execute_plan initial_fmp (input_ops ++ reorder_ops))` by
    (qpat_x_assum `asm_block_at prog as.as_pc
       (execute_plan initial_fmp _)` mp_tac >>
     simp[APPEND_ASSOC, execute_plan_append, asm_block_at_append]) >>
  `EVERY (\s. case s of SOSpill k => k < dimword(:256)
     | SORestore k => k < dimword(:256) | _ => T)
     (input_ops ++ reorder_ops)` by fs[EVERY_APPEND] >>
  qspecl_then [`BUMP`, `[h;h']`, `next_liveness`, `ps`, `input_ops`, `ps1`,
    `dfg`, `reorder_ops`, `ps4`, `lo`, `vs`, `as`, `o2pc`, `prog`,
    `initial_fmp`, `base'`] mp_tac marked_prefix_sim >>
  (impl_tac >- (ASM_REWRITE_TAC[] >> fs[] >> metis_tac[])) >>
  strip_tac >>
  rename1 `venom_asm_rel lo ps4 vs as'` >>
  qpat_x_assum `(case eval_operand h vs of _ => _) = OK vs'` mp_tac >>
  Cases_on `eval_operand h vs` >> gvs[] >>
  Cases_on `eval_operand h' vs` >> gvs[] >>
  `ps4.ps_stack = stack_pop 2 ps4.ps_stack ++ [h;h'] /\
   spill_alloc_layout_wf ps4.ps_alloc ps4.ps_spilled` by
    fs[plan_state_residual_wf_marked_def] >>
  `h'' <> h'³'` by
    metis_tac[codegen_ready_bump_outputs_distinct] >>
  `~MEM (Var h'') ps.ps_stack /\
   Var h'' NOTIN FDOM ps.ps_spilled` by
    (conj_tac
     >- (strip_tac >>
         qpat_assum `EVERY _ ps.ps_stack`
           (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         disch_then (qspec_then `Var h''` mp_tac) >> simp[])
     >> strip_tac >>
        qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
          (qspec_then `Var h''` mp_tac) >> simp[]) >>
  `~MEM (Var h'³') ps.ps_stack /\
   Var h'³' NOTIN FDOM ps.ps_spilled` by
    (conj_tac
     >- (strip_tac >>
         qpat_assum `EVERY _ ps.ps_stack`
           (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         disch_then (qspec_then `Var h'³'` mp_tac) >> simp[])
     >> strip_tac >>
        qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
          (qspec_then `Var h'³'` mp_tac) >> simp[]) >>
  `~MEM (Var h'') ps1.ps_stack /\
   Var h'' NOTIN FDOM ps1.ps_spilled` by
    (qspecl_then [`BUMP`, `[h;h']`, `next_liveness`, `ps`,
       `input_ops`, `ps1`, `h''`] mp_tac emit_input_plan_preserves_not_mem >>
     simp[]) >>
  `~MEM (Var h'³') ps1.ps_stack /\
   Var h'³' NOTIN FDOM ps1.ps_spilled` by
    (qspecl_then [`BUMP`, `[h;h']`, `next_liveness`, `ps`,
       `input_ops`, `ps1`, `h'³'`] mp_tac emit_input_plan_preserves_not_mem >>
     simp[]) >>
  `~MEM (Var h'') ps4.ps_stack /\
   Var h'' NOTIN FDOM ps4.ps_spilled` by
    (qspecl_then [`dfg`, `[h;h']`, `ps1`, `reorder_ops`, `ps4`, `h''`]
       mp_tac reorder_plan_preserves_not_mem_reachable >> simp[]) >>
  `~MEM (Var h'³') ps4.ps_stack /\
   Var h'³' NOTIN FDOM ps4.ps_spilled` by
    (qspecl_then [`dfg`, `[h;h']`, `ps1`, `reorder_ops`, `ps4`, `h'³'`]
       mp_tac reorder_plan_preserves_not_mem_reachable >> simp[]) >>
  `operand_val vs lo h = SOME x` by metis_tac[] >>
  `operand_val vs lo h' = SOME x'` by metis_tac[] >>
  `asm_block_at prog
     (as.as_pc + LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops)))
     (execute_plan initial_fmp (bump_emit_ops ++ pop_ops ++ opt_ops))` by
    (qspecl_then [`prog`, `as.as_pc`, `initial_fmp`, `input_ops`,
       `reorder_ops`, `bump_emit_ops ++ pop_ops ++ opt_ops`] mp_tac
       bump_asm_block_at_after_two_prefixes >>
     simp[bump_emit_ops_def] >> ASM_REWRITE_TAC[]) >>
  `as'.as_pc =
     as.as_pc + LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops))` by
    decide_tac >>
  `asm_block_at prog as'.as_pc
     (execute_plan initial_fmp (bump_emit_ops ++ pop_ops ++ opt_ops))` by
    (qpat_x_assum `asm_block_at prog (as.as_pc + _) _` mp_tac >>
     qpat_assum `as'.as_pc = as.as_pc + _`
       (fn th => rewrite_tac[GSYM th])) >>
  qpat_x_assum `asm_block_at prog as'.as_pc
     (execute_plan initial_fmp (bump_emit_ops ++ pop_ops ++ opt_ops))`
    mp_tac >>
  PURE_REWRITE_TAC[execute_plan_append, asm_block_at_append] >> strip_tac >>
  `EVERY (\op. case op of Var v => v <> h'' /\ v <> h'³' | _ => T)
     ps4.ps_stack` by
    (simp[EVERY_MEM] >> rpt strip_tac >> Cases_on `op` >> gvs[] >>
     metis_tac[]) >>
  `!op. op IN FDOM ps4.ps_spilled ==>
     (case op of Var v => v <> h'' /\ v <> h'³' | _ => T)` by
    (rpt strip_tac >> Cases_on `op` >> gvs[] >> metis_tac[]) >>
  `asm_block_at prog as'.as_pc
     (execute_plan initial_fmp bump_emit_ops)` by
    (qpat_assum `asm_block_at prog as'.as_pc _` mp_tac >>
     simp[bump_emit_ops_def]) >>
  qspecl_then [`lo`, `o2pc`, `prog`, `initial_fmp`, `ps4`, `ps4`, `vs`,
    `as'`, `stack_pop 2 ps4.ps_stack`, `h`, `h'`, `h''`, `h'³'`, `x`, `x'`]
    mp_tac bump_emit_sim_sem_stack >>
  (impl_tac >-
    (rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, simp[plan_stack_sem_eq_def]])) >>
  strip_tac >>
  `LENGTH (execute_plan initial_fmp bump_emit_ops) = 2` by
    simp[bump_emit_ops_def, execute_plan_def, exec_stack_op_def] >>
  `as''.as_pc =
     as'.as_pc + LENGTH (execute_plan initial_fmp bump_emit_ops)` by
    (qpat_assum `as''.as_pc = as'.as_pc + 2` mp_tac >>
     ASM_REWRITE_TAC[]) >>
  `asm_block_at prog as''.as_pc
     (execute_plan initial_fmp pop_ops)` by
    (qpat_x_assum `asm_block_at prog
       (as'.as_pc + LENGTH (execute_plan initial_fmp bump_emit_ops))
       (execute_plan initial_fmp pop_ops)` mp_tac >>
     qpat_assum `as''.as_pc = as'.as_pc + _`
       (fn th => rewrite_tac[GSYM th])) >>
  `?npop as8.
     asm_steps lo o2pc prog npop as'' = AsmOK as8 /\
     venom_asm_rel lo ps8
       (update_var h'³' (x + x')
         (update_var h'' x vs)) as8 /\
     as8.as_pc = as''.as_pc + LENGTH (execute_plan initial_fmp pop_ops) /\
     spill_alloc_layout_wf ps8.ps_alloc ps8.ps_spilled /\
     npop = LENGTH (execute_plan initial_fmp pop_ops)` by
    (drule popmany_plan_sim_numeric >>
     disch_then (qspecl_then [`lo`, `o2pc`, `prog`,
       `update_var h'³' (x + x') (update_var h'' x vs)`, `as''`,
       `initial_fmp`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
     strip_tac >> metis_tac[]) >>
  `asm_block_at prog as8.as_pc (execute_plan initial_fmp opt_ops)` by
    (qpat_x_assum `asm_block_at prog _
       (execute_plan initial_fmp opt_ops)` mp_tac >>
     qpat_assum `as8.as_pc = as''.as_pc + _` mp_tac >>
     qpat_assum `as''.as_pc = as'.as_pc + _` mp_tac >>
     simp[]) >>
  strip_tac >> gvs[] >>
  `?nopt st'.
     asm_steps lo o2pc prog nopt as8 = AsmOK st' /\
     venom_asm_rel lo ps9
       (update_var h'³' (x + x') (update_var h'' x vs)) st' /\
     st'.as_pc = as8.as_pc + LENGTH (execute_plan initial_fmp opt_ops) /\
     nopt = LENGTH (execute_plan initial_fmp opt_ops)` by
    (qpat_x_assum `(if _ = [] then _ else _) = (opt_ops,ps9)` mp_tac >>
     IF_CASES_TAC >> strip_tac
     >- (gvs[] >> qexists_tac `as8` >>
         simp[asm_steps_def, execute_plan_def]) >>
     drule optimistic_swap_sim_numeric >>
     disch_then (qspecl_then [`lo`, `o2pc`, `prog`,
       `update_var h'³' (x + x') (update_var h'' x vs)`, `as8`,
       `initial_fmp`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
     strip_tac >> metis_tac[]) >>
  `venom_asm_rel lo (release_dead_spills next_liveness ps9)
     (update_var h'³' (x + x') (update_var h'' x vs)) st'` by
    (irule venom_asm_rel_release_dead_spills >> ASM_REWRITE_TAC[]) >>
  qexistsl [`LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops)) +
             (2 + (LENGTH (execute_plan initial_fmp pop_ops) +
                   LENGTH (execute_plan initial_fmp opt_ops)))`, `st'`] >>
  gvs[asm_steps_add, execute_plan_append, LENGTH_APPEND] >>
  simp[execute_plan_def, exec_stack_op_def, bump_emit_ops_def] >> decide_tac
QED

Theorem bump_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = BUMP /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
      ps'.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    inst_wf inst /\
    (inst.inst_opcode = LOG ==>
      ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <= LENGTH (SND (emit_input_plan inst.inst_opcode
      (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
      EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
      ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
        FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==> eval_operand op vs = operand_val vs lo op) /\
    (!op at. MEM op (compute_operands inst) /\
      (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
      operand_equiv dfg op at ==> operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==> EVERY
      (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    (!dist prev val_op. inst.inst_opcode = PHI /\
      stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
      vs.vs_prev_bb = SOME prev /\ resolve_phi prev inst.inst_operands = SOME val_op ==>
      operand_val vs lo (stack_peek dist ps.ps_stack) = eval_operand val_op vs) /\
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\ n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting next_is_term
      bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
      inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
          as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all bump_inst_ok_sim_marked_count >> metis_tac[]
QED

(* The ISTORE case of gen_inst_ok_sim_marked. *)
Theorem istore_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = ISTORE /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `lo = _` kall_tac >> qpat_x_assum `o2pc = _` kall_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_inst_plan_def, is_param_opcode_def] >> strip_tac >>
  gvs[venom_to_evm_name_def, is_pre_codegen_opcode_def,
      is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
      is_raw_fmp_opcode_def, is_fmp_param_opcode_def, is_param_opcode_def] >>
  fs[inst_wf_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `eval_operand h vs` >> gvs[] >>
  Cases_on `eval_operand h' vs` >> gvs[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       generate_emit_ops_def, is_commutative_def,
       venom_to_evm_name_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  fs[python_stack_operands_def, ir_specific_operand_order_def] >>
  qpat_x_assum `inst.inst_opcode = ISTORE` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [ir_specific_operand_order_def]) >>
  `asm_block_at prog as.as_pc
     (execute_plan initial_fmp (input_ops ++ reorder_ops))` by
    (qpat_x_assum `asm_block_at prog as.as_pc (execute_plan initial_fmp _)` mp_tac >>
     simp[execute_plan_append, asm_block_at_append]) >>
  `!l. MEM (Label l) [h;h'] ==> IS_SOME (FLOOKUP lo l)` by (
    rpt strip_tac >>
    qpat_assum `!l. MEM (Label l) (compute_operands inst) ==> _`
      (qspec_then `l` mp_tac) >>
    (impl_tac >-
      gvs[compute_operands_def, python_stack_operands_def,
          ir_specific_operand_order_def]) >> simp[]) >>
  `EVERY (\s. case s of SOSpill k => k < dimword(:256)
     | SORestore k => k < dimword(:256) | _ => T)
     (input_ops ++ reorder_ops)` by fs[EVERY_APPEND] >>
  qspecl_then [`ISTORE`, `[h;h']`, `next_liveness`, `ps`, `input_ops`, `ps1`,
    `dfg`, `reorder_ops`, `ps4`, `lo`, `vs`, `as`, `o2pc`, `prog`,
    `initial_fmp`, `base'`] mp_tac marked_prefix_sim >>
  (impl_tac >- (ASM_REWRITE_TAC[] >>
    fs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
    metis_tac[])) >>
  strip_tac >>
  rename1 `venom_asm_rel lo ps4 vs as'` >>
  `ps4.ps_stack = stack_pop 2 ps4.ps_stack ++ [h;h'] /\
   spill_alloc_layout_wf ps4.ps_alloc ps4.ps_spilled` by
    fs[plan_state_residual_wf_marked_def] >>
  `operand_val vs lo h = SOME x /\ operand_val vs lo h' = SOME x'` by
    (conj_tac
     >- (qpat_assum `!op. MEM op (compute_operands inst) ==> _`
           (qspec_then `h` mp_tac) >>
         gvs[compute_operands_def, python_stack_operands_def,
             ir_specific_operand_order_def])
     >> qpat_assum `!op. MEM op (compute_operands inst) ==> _`
          (qspec_then `h'` mp_tac) >>
        gvs[compute_operands_def, python_stack_operands_def,
            ir_specific_operand_order_def]) >>
  `2 <= LENGTH ps4.ps_stack` by
    (qpat_assum `ps4.ps_stack = stack_pop 2 ps4.ps_stack ++ [h;h']`
       (mp_tac o AP_TERM ``LENGTH : operand list -> num``) >>
     pure_rewrite_tac[LENGTH_APPEND, LENGTH] >> decide_tac) >>
  `2 <= LENGTH as'.as_stack` by
    (fs[venom_asm_rel_def, plan_stack_rel_def] >> decide_tac) >>
  `plan_stack_rel lo vs (stack_pop 2 ps4.ps_stack)
     (DROP 2 as'.as_stack)` by
    (simp[stack_pop_def] >> irule plan_stack_rel_pop >>
     fs[venom_asm_rel_def]) >>
  `h <> dead_stack_marker /\ h' <> dead_stack_marker` by
    fs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  `EL 0 as'.as_stack = x'` by
    (qspecl_then [`lo`, `vs`, `ps4.ps_stack`, `as'.as_stack`, `0`]
       mp_tac plan_stack_rel_el >>
     (impl_tac >- fs[venom_asm_rel_def]) >>
     qpat_assum `ps4.ps_stack = stack_pop 2 ps4.ps_stack ++ [h;h']`
       (fn th => once_rewrite_tac[th]) >>
     simp[REVERSE_APPEND]) >>
  `EL 1 as'.as_stack = x` by
    (qspecl_then [`lo`, `vs`, `ps4.ps_stack`, `as'.as_stack`, `1`]
       mp_tac plan_stack_rel_el >>
     (impl_tac >- fs[venom_asm_rel_def]) >>
     qpat_assum `ps4.ps_stack = stack_pop 2 ps4.ps_stack ++ [h;h']`
       (fn th => once_rewrite_tac[th]) >>
     simp[REVERSE_APPEND]) >>
  `?rest. as'.as_stack = x'::x::rest /\
          plan_stack_rel lo vs (stack_pop 2 ps4.ps_stack) rest` by
    (qexists `DROP 2 as'.as_stack` >> ASM_REWRITE_TAC[] >>
     Cases_on `as'.as_stack` >- gvs[] >>
     Cases_on `t` >- gvs[] >> gvs[]) >>
  `as'.as_pc = as.as_pc +
     (LENGTH (FLAT (MAP (exec_stack_op initial_fmp) input_ops)) +
      LENGTH (FLAT (MAP (exec_stack_op initial_fmp) reorder_ops)))` by
    (qpat_assum `as'.as_pc = _` mp_tac >>
     simp[execute_plan_append, execute_plan_def]) >>
  `asm_block_at prog as'.as_pc [AsmOp "SWAP1"; AsmOp "MSTORE"]` by
    (qpat_assum `asm_block_at prog as.as_pc
       (execute_plan initial_fmp
         (input_ops ++ reorder_ops ++ [SOEmit "SWAP1"; SOEmit "MSTORE"]))`
       mp_tac >>
     PURE_REWRITE_TAC[APPEND_ASSOC, execute_plan_append,
       asm_block_at_append] >> strip_tac >>
     qpat_assum `asm_block_at prog (as.as_pc + LENGTH (_ ++ _)) _`
       (fn th => mp_tac (SIMP_RULE (srw_ss())
         [execute_plan_def, exec_stack_op_def, LENGTH_APPEND] th)) >>
     qpat_assum `as'.as_pc = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  qabbrev_tac `as2 = as' with <|
    as_stack := rest;
    as_memory := mem_write32 (w2n x) x' as'.as_memory;
    as_pc := as'.as_pc + 2 |>` >>
  `asm_steps lo o2pc prog 2 as' = AsmOK as2` by
    (unabbrev_all_tac >> irule istore_emit_steps >> ASM_REWRITE_TAC[]) >>
  `inst_memory_safe ps4.ps_alloc inst vs (istore (w2n x) x' vs)` by
    (irule inst_memory_safe_alloc_fields >>
     qexists `(release_dead_spills next_liveness
       (ps4 with ps_stack := stack_pop 2 ps4.ps_stack)).ps_alloc` >>
     simp[release_dead_spills_spill_base,
          release_dead_spills_next_offset] >>
     first_assum ACCEPT_TAC) >>
  `w2n x + 32 <= ps4.ps_alloc.sa_spill_base \/
   ps4.ps_alloc.sa_next_offset <= w2n x` by
    (qpat_x_assum `inst_memory_safe ps4.ps_alloc inst vs _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, fixed_source_write_range_def]) >>
  `!op. operand_val (istore (w2n x) x' vs) lo op = operand_val vs lo op` by
    (Cases >> simp[operand_val_def, istore_def, mstore_def]) >>
  `plan_spill_rel lo vs ps4.ps_spilled as'.as_memory` by
    (qpat_assum `venom_asm_rel lo ps4 vs as'`
       (fn th => ACCEPT_TAC (cj 2 (REWRITE_RULE[venom_asm_rel_def] th)))) >>
  `venom_asm_rel lo
     (ps4 with ps_stack := stack_pop 2 ps4.ps_stack)
     (istore (w2n x) x' vs) as2` by
    (unabbrev_all_tac >> simp[venom_asm_rel_def] >>
     conj_tac
     >- (qpat_x_assum `plan_stack_rel lo vs (stack_pop 2 ps4.ps_stack) rest`
           mp_tac >> simp[plan_stack_rel_def]) >>
     conj_tac
     >- (irule plan_spill_rel_preserved >>
         qexistsl [`as'.as_memory`, `vs`] >>
         conj_tac
         >- (rpt strip_tac >> irule mem_write32_read32_disjoint >>
             `ps4.ps_alloc.sa_spill_base <= off /\
              off + 32 <= ps4.ps_alloc.sa_next_offset` by
               (qpat_x_assum `spill_alloc_layout_wf ps4.ps_alloc _` mp_tac >>
                simp[spill_alloc_layout_wf_def] >> metis_tac[]) >>
             decide_tac) >>
         simp[]) >>
     conj_tac
     >- (irule memory_rel_mstore_mem_write32 >>
         qpat_assum `venom_asm_rel lo ps4 vs as'`
           (fn th => ACCEPT_TAC (cj 3 (REWRITE_RULE[venom_asm_rel_def] th)))) >>
     qpat_assum `venom_asm_rel lo ps4 vs as'`
       (fn th => STRIP_ASSUME_TAC (REWRITE_RULE[venom_asm_rel_def] th)) >>
     ASM_REWRITE_TAC[] >> simp[istore_def, mstore_def]) >>
  `venom_asm_rel lo
     (release_dead_spills next_liveness
       (ps4 with ps_stack := stack_pop 2 ps4.ps_stack))
     (istore (w2n x) x' vs) as2` by
    (irule venom_asm_rel_release_dead_spills >> ASM_REWRITE_TAC[]) >>
  qexistsl [`LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops)) + 2`,
             `as2`] >>
  gvs[asm_steps_add, execute_plan_append, LENGTH_APPEND,
      execute_plan_def, exec_stack_op_def] >>
  simp[Abbr `as2`]
QED

fun ok_case_lemma_tac th =
  mp_tac th >>
  disch_then (qspecl_then [`fuel`, `ctx`, `lo`, `o2pc`, `prog`, `liveness`,
    `dfg`, `cfg`, `fn`, `inst`, `next_liveness`, `is_halting`,
    `next_is_term`, `bb_label`, `base'`, `ps`, `vs`, `as`, `ops`, `ps'`,
    `initial_fmp`]
    mp_tac) >>
  impl_tac >- ASM_REWRITE_TAC[] >>
  disch_then (qspec_then `vs'` mp_tac) >> ASM_REWRITE_TAC[];

Theorem gen_inst_ok_sim_marked:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps' initial_fmp.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    (* GAS readings are opaque at this level: venom_asm_rel deliberately does
       not relate them to Venom's GAS value.  The frame-aware invariant owns
       GAS, as it owns INVOKE. *)
    inst.inst_opcode <> GAS /\
    (* inst_wf fixes only the output count of the zero-operand reads; extra
       operands would be left on the assembly stack by the EVM opcode. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* Source memory reads avoid the compiler-owned spill interval, mirroring
       source_memory_writes_disjoint and the context-level
       source_memory_reads_disjoint; memory_rel says nothing inside it. *)
    EVERY (\(off,len). len = 0 \/ off + len <= ps'.ps_alloc.sa_spill_base \/
                       ps'.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst vs) /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    (* Jumps are simulated against the frame invariant (genFrameSim), whose
       statements carry the join-reorder and target-resolution premises a
       jump needs and land at the target block's pc.  DJMP is outside
       unit_shape_ok, and Venom's DJMP indexes its label list while the
       generated code jumps to the selector value. *)
    ~MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input is on the stack at any depth or spilled. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan initial_fmp ops) /\
             EL i (execute_plan initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val vs lo op = operand_val vs lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill and restore offsets fit a PUSH. *)
    EVERY (\s. case s of SOSpill k => k < dimword(:256)
      | SORestore k => k < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          inst_memory_safe ps'.ps_alloc inst vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        (~is_terminator inst.inst_opcode ==>
         as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- ok_case_lemma_tac assign_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = LOG`
  >- ok_case_lemma_tac log_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = ASSERT`
  >- ok_case_lemma_tac assert_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- ok_case_lemma_tac assert_unreachable_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = PHI`
  >- ok_case_lemma_tac phi_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- ok_case_lemma_tac initial_fmp_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = BUMP`
  >- ok_case_lemma_tac bump_inst_ok_sim_marked >>
  Cases_on `inst.inst_opcode = ISTORE`
  >- ok_case_lemma_tac istore_inst_ok_sim_marked >>
  (* Do not substitute concrete maps into the preserved map-parametric proofs. *)
  qpat_x_assum `lo = SND (compute_label_offsets prog)` kall_tac >>
  qpat_x_assum `o2pc = build_offset_to_pc prog` kall_tac >>
  (* Dispatch on generate_inst_plan cases *)
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_inst_plan_def, is_param_opcode_def] >>
  strip_tac >>
  (* is_pre_codegen eliminated by SOME <> NONE *)
  (* Now case split on opcode *)
  Cases_on `inst.inst_opcode = PHI` >- gvs[] >>
  Cases_on `inst.inst_opcode = OFFSET` >- (gvs[] >> suspend "offset") >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "param") >>
  Cases_on `inst.inst_opcode = FMP_PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "fmp_param") >>
  Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "retpc_param") >>
  `~is_param_opcode inst.inst_opcode` by simp[is_param_opcode_iff] >>
  gvs[] >>
  Cases_on `inst.inst_opcode = NOP`
  >- (
    gvs[] >> imp_res_tac step_inst_nop_ok >> gvs[] >>
    qexistsl_tac [`0`, `as`] >> simp[asm_steps_def, execute_plan_def]
  ) >>
  (* Regular instruction: dispatch by opcode family *)
  Cases_on `inst.inst_opcode = INVOKE` >- gvs[] >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >- (
    (* NONE case: ASSIGN, ISTORE, JMP, JNZ, DJMP, LOG, ASSERT, etc. *)
    gvs[] >> suspend "none"
  ) >>
  rename1 `venom_to_evm_name _ = SOME name` >>
  (* SOME name case: 3-phase plan (prefix + emit + postfix) *)
  gvs[] >>
  suspend "some_name"
QED

Resume gen_inst_ok_sim_marked[offset]:
  drule_all inst_wf_offset_shape >> strip_tac >> gvs[] >>
  qpat_x_assum `generate_offset_plan _ _ = _` mp_tac >>
  simp[generate_offset_plan_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
       eval_operand_def] >>
  strip_tac >> gvs[] >>
  `?off. FLOOKUP lo lbl = SOME off` by
    (Cases_on `FLOOKUP lo lbl` >> gvs[compute_operands_def]) >>
  `FLOOKUP vs.vs_labels lbl = SOME (n2w off)` by
    (qpat_x_assum `!op. MEM op (compute_operands inst) ==> _`
       (qspec_then `Label lbl` mp_tac) >>
     simp[compute_operands_def, eval_operand_def, operand_val_def]) >>
  gvs[] >>
  `v + n2w off = n2w (off + w2n v)` by
    simp[wordsTheory.word_add_def, arithmeticTheory.ADD_COMM] >>
  `~MEM (Var out) ps.ps_stack` by
    (strip_tac >>
     qpat_x_assum `EVERY _ ps.ps_stack`
       (fn th => mp_tac (REWRITE_RULE [EVERY_MEM] th)) >>
     disch_then (qspec_then `Var out` mp_tac) >> gvs[]) >>
  `Var out NOTIN FDOM ps.ps_spilled` by
    (strip_tac >>
     qpat_x_assum `!op. op IN FDOM _ ==> _`
       (qspec_then `Var out` mp_tac) >> simp[]) >>
  qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`, `lbl`,
               `w2n v`, `off`] mp_tac simple_op_push_ofst >>
  (impl_tac >-
    (ASM_REWRITE_TAC[] >>
     qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
     simp[execute_plan_def, exec_stack_op_def])) >>
  strip_tac >>
  `venom_asm_rel lo
      (ps with ps_stack := stack_push (Var out) ps.ps_stack)
      (update_var out (v + n2w off) vs) st'` by
    (simp[stack_push_def] >>
     irule venom_asm_rel_push_lit_as_fresh_var >>
     ASM_REWRITE_TAC[]) >>
  qexistsl [`1`, `st'`] >> ASM_REWRITE_TAC[] >>
  simp[execute_plan_def, exec_stack_op_def]
QED

Resume gen_inst_ok_sim_marked[param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[step_inst_base_def, compute_operands_def, eval_operand_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED

Resume gen_inst_ok_sim_marked[fmp_param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = FMP_PARAM`
    (fn th => PURE_REWRITE_TAC[th]) >>
  asm_simp_tac (srw_ss()) [] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED

Resume gen_inst_ok_sim_marked[retpc_param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  gvs[step_inst_base_def, compute_operands_def, eval_operand_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED

Resume gen_inst_ok_sim_marked[none]:
  (* Opcodes with an EVM name contradict the NONE case; drop them with a
     goal-only rewrite before the full gvs, which is slow on 100+ goals. *)
  qpat_x_assum `venom_to_evm_name _ = NONE` mp_tac >>
  Cases_on `inst.inst_opcode` >>
  simp_tac (srw_ss()) [venom_to_evm_name_def] >>
  gvs[venom_to_evm_name_def, is_pre_codegen_opcode_def,
      is_unlowered_fmp_opcode_def,
      is_unlowered_internal_call_opcode_def,
      is_raw_fmp_opcode_def, is_fmp_param_opcode_def]
  >> TRY (`inst.inst_opcode <> ISTORE /\
           inst.inst_opcode <> JMP /\
           inst.inst_opcode <> JNZ /\
           inst.inst_opcode <> DJMP /\
           inst.inst_opcode <> ASSIGN /\
           inst.inst_opcode <> LOG /\
           inst.inst_opcode <> ASSERT /\
           inst.inst_opcode <> ASSERT_UNREACHABLE` by simp[] >>
          qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
          simp[step_inst_non_invoke, Once step_inst_base_def] >>
          BasicProvers.every_case_tac >> simp[] >> NO_TAC)
  >> gvs[]
QED

Resume gen_inst_ok_sim_marked[some_name]:
  qspecl_then [`fuel`, `ctx`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`, `cfg`,
    `fn`, `inst`, `next_liveness`, `is_halting`, `next_is_term`, `bb_label`,
    `base'`, `ps`, `vs`, `as`, `ops`, `ps'`, `name`, `initial_fmp`]
    mp_tac regular_inst_ok_sim_marked >>
  ASM_REWRITE_TAC[] >>
  impl_tac >- (
    fs[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
    res_tac >> gvs[]) >>
  strip_tac >> qexistsl [`n`, `as'`] >> simp[]
QED

Finalise gen_inst_ok_sim_marked
