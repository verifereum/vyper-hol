Theory fnPlanLineageObserverTransport
Ancestors fnPlanLineageWide fnPlanLineagePhiResources fnPlanLineageNativeTerminal
Libs stackPlanGenTheory stackModelTheory stackPlanOpsTheory listTheory rich_listTheory

Theorem mark_dead_stack_elem_count_nonincrease:
  !stk retained x. x <> dead_stack_marker ==>
    LIST_ELEM_COUNT x (mark_dead_stack retained stk) <= LIST_ELEM_COUNT x stk
Proof
  Induct >- simp[mark_dead_stack_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`retained`,`x`] mp_tac) >>
  Cases_on `MEM h retained` >> Cases_on `h = x` >>
  simp[mark_dead_stack_def, LIST_ELEM_COUNT_THM]
QED

Theorem clean_stack_plan_resource_nonincrease:
  !lv cfg fn bb ps ops qs v.
    clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[] >>
  Cases_on `t` >> simp[]
  >- (IF_CASES_TAC >> simp[] >>
      Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
      IF_CASES_TAC
      >- (strip_tac >> gvs[] >>
          `~MEM (Var v) (MAP (K dead_stack_marker) ps.ps_stack)` by
            simp[MEM_MAP, dead_stack_marker_def] >>
          gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
      IF_CASES_TAC >> simp[]
      >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          drule fnPlanLineageInventoryTheory.popmany_plan_resource_nonincrease >>
          disch_then (qspec_then `Var v` mp_tac) >>
          qmatch_goalsub_abbrev_tac `mark_dead_stack retained ps'.ps_stack` >>
          mp_tac (Q.SPECL [`ps'.ps_stack`,`retained`,`Var v`]
            mark_dead_stack_elem_count_nonincrease) >>
          simp[dead_stack_marker_def] >> decide_tac) >>
      strip_tac >> drule fnPlanLineageInventoryTheory.popmany_plan_resource_nonincrease >>
      disch_then (qspec_then `Var v` mp_tac) >> simp[]) >>
  strip_tac >> gvs[]
QED

Theorem generate_phi_plan_nondefining_resource_nonincrease:
  !inst next halt ps ops qs v.
    generate_phi_plan inst next halt ps = (ops,qs) /\
    v <> HD inst.inst_outputs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- gvs[generate_phi_plan_def] >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule planAlignTheory.stack_find_bound >> simp[]) >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`,`halt`] mp_tac) >>
  Cases_on `fnPlanLineagePhiTemporal$phi_write_phase inst next d ps` >>
  rename1 `phi_write_phase inst next d ps = (writes,ws)` >>
  simp[] >> strip_tac >>
  `ws.ps_spilled = ps.ps_spilled /\
   LIST_ELEM_COUNT (Var v) ws.ps_stack <= LIST_ELEM_COUNT (Var v) ps.ps_stack` by
    (qpat_x_assum `phi_write_phase _ _ _ _ = _` mp_tac >>
     simp[fnPlanLineagePhiTemporalTheory.phi_write_phase_def] >> IF_CASES_TAC
     >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
         drule deepResidualBudgetTheory.do_dup_spilled_eq >> strip_tac >>
         drule doSwapSimTheory.do_dup_stack_exact >> simp[] >> strip_tac >>
         simp[stack_poke_def, LUPDATE_APPEND2, LUPDATE_def,
              LIST_ELEM_COUNT_DEF, FILTER_APPEND]) >>
     strip_tac >> gvs[] >> drule stack_poke_count_balance >>
     disch_then (qspecl_then [`Var v`,`Var (HD inst.inst_outputs)`] mp_tac) >>
     Cases_on `Var v = stack_peek d ps.ps_stack` >> simp[]) >>
  Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) next` >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      drule fnPlanLineageInventoryTheory.popmany_plan_resource_nonincrease >>
      disch_then (qspec_then `Var v` mp_tac) >> simp[] >> decide_tac) >>
  simp[]
QED

(* Exact copy of deepResidualBudgetTheory.count_le_one_all_distinct (local),
   under the TASK's inaccessible-helper copy exception. *)
Theorem count_le_one_all_distinct:
  !(xs : 'a list). (!x. LIST_ELEM_COUNT x xs <= 1) ==> ALL_DISTINCT xs
Proof
  Induct >> rw[]
  >- (qpat_x_assum `!x. LIST_ELEM_COUNT x (h::xs) <= 1`
        (qspec_then `h` mp_tac) >>
      simp[LIST_ELEM_COUNT_THM] >> strip_tac >>
      fs[GSYM LIST_ELEM_COUNT_MEM]) >>
  first_x_assum irule >> gen_tac >>
  qpat_x_assum `!x. LIST_ELEM_COUNT x (h::xs) <= 1`
    (qspec_then `x` mp_tac) >>
  Cases_on `h = x` >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem generate_inst_plan_jmp_resource_nonincrease:
  !lv dfg cfg fn inst next halt term cur ps targets ops qs x.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops lv fn cur inst = SOME targets /\ ALL_DISTINCT targets /\
    (!at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs) ==>
    LIST_ELEM_COUNT x qs.ps_stack + (if x IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack + (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `?target. inst.inst_operands = [Label target]` by
    (gvs[join_target_ops_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def, venomInstTheory.is_param_opcode_def] >>
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, emit_input_plan_def,
       stackPlanTypesTheory.is_label_operand_def, venomEffectsTheory.is_commutative_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  Cases_on `restore_spilled_plan targets ps` >> simp[] >>
  rename1 `restore_spilled_plan targets ps = (rOps,psR)` >>
  Cases_on `reorder_plan dfg targets psR` >> simp[stack_pop_def] >>
  strip_tac >> gvs[] >>
  rename1 `reorder_plan dfg targets psR = (qOps,psQ)` >>
  `LENGTH targets <= LENGTH psR.ps_stack` by
    (drule_all restore_spilled_plan_distinct_materialised >> simp[]) >>
  drule fnPlanLineageInventoryTheory.restore_spilled_plan_inventory_count >> strip_tac >>
  drule_all fnPlanLineageInventoryTheory.reorder_plan_resource_nonincrease >>
  disch_then (qspec_then `x` mp_tac) >>
  qpat_x_assum `!x. LIST_ELEM_COUNT x psR.ps_stack + _ = _`
    (qspec_then `x` mp_tac) >>
  mp_tac (Q.SPECL [`next`,`psQ`,`x`]
    fnPlanLineageInventoryTheory.release_dead_spills_resource_nonincrease) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  rpt strip_tac >> gvs[] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem native_terminal_jmp_observer_upper:
  !fn bb dfg ps ops qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    (!w. MEM w (live_vars_at (liveness_analyze fn) bb.bb_label
      (PRE (LENGTH bb.bb_instructions))) ==>
      MEM (Var w) ps.ps_stack \/ Var w IN FDOM ps.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (LAST bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
      (bb_is_halting bb) F bb.bb_label ps = SOME (ops,qs) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ] /\
    (LAST bb.bb_instructions).inst_outputs = []` by gvs[venomWfTheory.inst_wf_def] >>
  Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label (LAST bb.bb_instructions)`
  >- (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        fnPlanLineageEntryProductionTheory.jmp_no_target_state >>
      simp[] >> strip_tac >> gvs[] >>
      irule arithmeticTheory.LESS_EQ_TRANS >>
      irule_at Any fnPlanLineageInventoryTheory.release_dead_spills_resource_nonincrease >>
      simp[]) >>
  rename1 `join_target_ops _ _ _ _ = SOME targets` >>
  `!at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (drule_at (Pat `join_target_ops _ _ _ _ = _`) native_terminal_jmp_target_available >> simp[]) >>
  `ALL_DISTINCT targets` by
    (irule count_le_one_all_distinct >> gen_tac >>
     Cases_on `lookup_block succ fn.fn_blocks`
     >- gvs[join_target_ops_def] >>
     `!w. LIST_ELEM_COUNT (Var w) targets <= 1` by
       (gen_tac >> drule_at (Pat `join_target_ops _ _ _ _ = _`)
          fnPlanLineageNativeTargetsTheory.ready_join_target_count_le_one >> simp[]) >>
     `?vars. targets = MAP Var vars` by
       (gvs[join_target_ops_def] >> metis_tac[]) >>
     Cases_on `x` >> gvs[LIST_ELEM_COUNT_DEF, FILTER_MAP, combinTheory.o_DEF]) >>
  drule_all generate_inst_plan_jmp_resource_nonincrease >>
  disch_then (qspec_then `Var v` assume_tac) >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem prepare_params_plan_nondefining_resource_nonincrease:
  !lv fn ps ops qs v.
    prepare_params_plan lv fn ps = (ops,qs) /\
    EVERY (\inst. v <> HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `get_params (HD fn.fn_blocks).bb_instructions = []`
  >- gvs[prepare_params_plan_def] >>
  qpat_x_assum `prepare_params_plan _ _ _ = _` mp_tac >>
  simp[prepare_params_plan_def, fnPlanLineageSetupTheory.parameter_push_fold, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule fnPlanLineageInventoryTheory.optimistic_swap_plan_resource_count >>
  disch_then (qspec_then `Var v` mp_tac) >>
  drule fnPlanLineageInventoryTheory.popmany_plan_resource_nonincrease >>
  disch_then (qspec_then `Var v` mp_tac) >>
  `~MEM (Var v) (MAP (\inst. Var (HD inst.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions))` by
    (gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `LIST_ELEM_COUNT (Var v) (MAP (\inst. Var (HD inst.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions)) = 0` by
    (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  fs[LIST_ELEM_COUNT_DEF] >> simp[FILTER_APPEND]
QED
