Theory fnPlanLineageObserverTransport
Ancestors fnPlanLineageWide fnPlanLineagePhiResources fnPlanLineageNativeTerminal
  fnPlanLineagePhiSuffixResources
Libs stackPlanGenTheory stackModelTheory stackPlanOpsTheory listTheory rich_listTheory

Theorem nonentry_setup_resource_absent:
  !lv cfg fn bb ps ops qs v.
    bb <> HD fn.fn_blocks /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps
     else if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
       clean_stack_plan lv cfg fn bb ps else ([],ps)) = (ops,qs) ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[] >>
  drule fnPlanLineageChronologicalPrefixTheory.clean_stack_plan_inventory >>
  disch_then (qspec_then `Var v` mp_tac) >> gvs[dead_stack_marker_def]
QED

Theorem get_params_mem:
  !insts inst. MEM inst (get_params insts) ==>
    MEM inst insts /\ is_param_opcode inst.inst_opcode
Proof
  Induct >> simp[get_params_def] >> rpt gen_tac >>
  Cases_on `is_param_opcode h.inst_opcode` >> simp[] >> metis_tac[]
QED

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

Theorem generate_phi_plan_resource_bound:
  !inst next halt ps ops qs v.
    generate_phi_plan inst next halt ps = (ops,qs) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) +
      (if v = HD inst.inst_outputs then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- (gvs[generate_phi_plan_def] >> decide_tac) >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule planAlignTheory.stack_find_bound >> simp[]) >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`,`halt`] mp_tac) >>
  Cases_on `fnPlanLineagePhiTemporal$phi_write_phase inst next d ps` >>
  rename1 `phi_write_phase inst next d ps = (writes,ws)` >>
  simp[] >> strip_tac >>
  `ws.ps_spilled = ps.ps_spilled /\
   LIST_ELEM_COUNT (Var v) ws.ps_stack <= LIST_ELEM_COUNT (Var v) ps.ps_stack +
     (if v = HD inst.inst_outputs then 1 else 0)` by
    (qpat_x_assum `phi_write_phase _ _ _ _ = _` mp_tac >>
     simp[fnPlanLineagePhiTemporalTheory.phi_write_phase_def] >> IF_CASES_TAC
     >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
         drule deepResidualBudgetTheory.do_dup_spilled_eq >> strip_tac >>
         drule doSwapSimTheory.do_dup_stack_exact >> simp[] >> strip_tac >>
         Cases_on `v = HD inst.inst_outputs` >>
         simp[stack_poke_def, LUPDATE_APPEND2, LUPDATE_def,
              LIST_ELEM_COUNT_DEF, FILTER_APPEND]) >>
     strip_tac >> gvs[] >> drule stack_poke_count_balance >>
     disch_then (qspecl_then [`Var v`,`Var (HD inst.inst_outputs)`] mp_tac) >>
     Cases_on `Var v = stack_peek d ps.ps_stack` >>
     Cases_on `v = HD inst.inst_outputs` >> simp[]) >>
  Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) next` >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      drule fnPlanLineageInventoryTheory.popmany_plan_resource_nonincrease >>
      disch_then (qspec_then `Var v` mp_tac) >> simp[] >>
      Cases_on `v = HD inst.inst_outputs` >> gvs[] >> decide_tac) >>
  Cases_on `v = HD inst.inst_outputs` >> gvs[] >> decide_tac
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
  rpt gen_tac >> strip_tac >> drule generate_phi_plan_resource_bound >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
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

Theorem prepare_params_plan_resource_bound:
  !lv fn ps ops qs v.
    prepare_params_plan lv fn ps = (ops,qs) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) +
      LIST_ELEM_COUNT (Var v) (MAP (\inst. Var (HD inst.inst_outputs))
        (get_params (HD fn.fn_blocks).bb_instructions))
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
  fs[LIST_ELEM_COUNT_DEF] >> simp[FILTER_APPEND]
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
  drule prepare_params_plan_resource_bound >>
  disch_then (qspec_then `v` mp_tac) >>
  `~MEM (Var v) (MAP (\inst. Var (HD inst.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions))` by
    (gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `LIST_ELEM_COUNT (Var v) (MAP (\inst. Var (HD inst.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions)) = 0` by
    gvs[GSYM LIST_ELEM_COUNT_MEM] >> simp[]
QED

Theorem prepare_params_plan_fresh_output_resource_bound:
  !lv fn ps ops qs v.
    prepare_params_plan lv fn ps = (ops,qs) /\
    ALL_DISTINCT (MAP (\inst. HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions)) /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  drule prepare_params_plan_resource_bound >>
  disch_then (qspec_then `v` mp_tac) >>
  `ALL_DISTINCT (MAP (\inst. Var (HD inst.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions))` by
    (`MAP (\inst. Var (HD inst.inst_outputs))
        (get_params (HD fn.fn_blocks).bb_instructions) =
      MAP Var (MAP (\inst. HD inst.inst_outputs)
        (get_params (HD fn.fn_blocks).bb_instructions))` by simp[MAP_MAP_o, combinTheory.o_DEF] >>
     asm_rewrite_tac[] >> irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  drule fnPlanLineageInventoryTheory.all_distinct_elem_count_le_one >>
  disch_then (qspec_then `Var v` mp_tac) >>
  `LIST_ELEM_COUNT (Var v) ps.ps_stack = 0` by
    gvs[GSYM LIST_ELEM_COUNT_MEM] >> simp[] >> decide_tac
QED

Theorem resource_zero_iff_absent:
  !ps x. (LIST_ELEM_COUNT x ps.ps_stack +
    (if x IN FDOM ps.ps_spilled then 1 else 0) <= 0) <=>
    (~MEM x ps.ps_stack /\ x NOTIN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> Cases_on `x IN FDOM ps.ps_spilled` >>
  simp[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem elem_count_zero_iff:
  !x xs. (LIST_ELEM_COUNT x xs = 0) <=> ~MEM x xs
Proof
  simp[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem indicator_zero_iff:
  !p. ((if p then 1n else 0) = 0) <=> ~p
Proof
  Cases >> simp[]
QED

Theorem native_terminal_jmp_nondefining_absent:
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
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ] /\
    (LAST bb.bb_instructions).inst_outputs = []` by gvs[venomWfTheory.inst_wf_def] >>
  Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label (LAST bb.bb_instructions)`
  >- (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        fnPlanLineageEntryProductionTheory.jmp_no_target_state >>
      simp[] >> strip_tac >> gvs[fnPlanLineageInventoryTheory.release_dead_spills_domain,
          fnPlanLineageInventoryTheory.release_dead_spills_stack]) >>
  rename1 `join_target_ops _ _ _ _ = SOME targets` >>
  `!at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (drule_at (Pat `join_target_ops _ _ _ _ = _`) native_terminal_jmp_target_available >> simp[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    fnPlanLineageInventoryTheory.generate_inst_plan_jmp_variable_support >>
  disch_then (qspecl_then [`targets`,`(\w. w <> v)`,`v`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem native_indexed_step_layout:
  !fn bb k inst rest.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    DROP k (non_param_insts bb) = inst::rest ==>
    k < LENGTH (non_param_insts bb) /\
    inst = EL k (non_param_insts bb) /\
    inst = EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions /\
    MEM inst bb.bb_instructions /\ ~is_param_opcode inst.inst_opcode /\
    inst_wf inst /\ codegen_ready_inst inst /\ ALL_DISTINCT inst.inst_outputs /\
    (inst.inst_opcode <> PHI ==> LENGTH (collect_phis bb.bb_instructions) <= k)
Proof
  rpt gen_tac >> strip_tac >>
  `k < LENGTH (non_param_insts bb)` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k (non_param_insts bb)` by metis_tac[HD_DROP, HD] >>
  `inst = EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions` by
    metis_tac[fnPlanLineageCallersTheory.ready_block_suffix_index] >>
  `MEM inst bb.bb_instructions /\ ~is_param_opcode inst.inst_opcode` by
    (`MEM inst (non_param_insts bb)` by metis_tac[EL_MEM] >>
     gvs[non_param_insts_def, MEM_FILTER]) >>
  `inst_wf inst /\ codegen_ready_inst inst` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT inst.inst_outputs` by
    (irule fnPlanLineageCallersTheory.codegen_ready_inst_outputs_distinct >>
     qexists_tac `fn` >> simp[] >>
     gvs[venomInstTheory.fn_insts_def] >>
     metis_tac[venomInstTheory.fmp_fn_insts_blocks_intro]) >>
  gvs[] >> strip_tac >> spose_not_then assume_tac >>
  qspec_then `bb` (qx_choose_then `tail` assume_tac)
    fnPlanLineageEntryProductionTheory.non_param_insts_phi_prefix >>
  `k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `EL k (non_param_insts bb) = EL k (collect_phis bb.bb_instructions)` by
    simp[EL_APPEND1] >>
  metis_tac[livenessTransferProofsTheory.collect_phis_mem, EL_MEM]
QED

Theorem native_indexed_step_nondefining_observer_bound:
  !fn bb dfg k before inst rest ops after v b.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    DROP k (non_param_insts bb) = inst::rest /\
    ~MEM v inst.inst_outputs /\ b <= 1 /\
    LIST_ELEM_COUNT (Var v) before.ps_stack +
      (if Var v IN FDOM before.ps_spilled then 1 else 0) <= b /\
    (LENGTH (collect_phis bb.bb_instructions) <= k ==>
      (!w. MEM w (live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH (get_params bb.bb_instructions)+k)) ==>
        MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
      (!w. MEM (Var w) (compute_operands inst) ==>
        MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled)) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1))
      (bb_is_halting bb)
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label before = SOME (ops,after) ==>
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= b
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_indexed_step_layout >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (`v <> HD inst.inst_outputs` by
        gvs[venomWfTheory.inst_wf_def, LENGTH_EQ_NUM_compute] >>
      qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
           is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
           venomInstTheory.is_raw_fmp_opcode_def, venomInstTheory.is_param_opcode_def] >>
      strip_tac >>
      qpat_x_assum `inst = EL (_ + k) bb.bb_instructions`
        (fn th => qpat_x_assum `generate_phi_plan _ _ _ _ = _`
          (mp_tac o REWRITE_RULE [Once arithmeticTheory.ADD_COMM, GSYM th])) >>
      strip_tac >> drule_all generate_phi_plan_nondefining_resource_nonincrease >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `LENGTH (collect_phis bb.bb_instructions) <= k` by metis_tac[] >>
  qpat_x_assum `(LENGTH (collect_phis _) <= k ==> _)` mp_tac >> simp[] >> strip_tac >>
  Cases_on `inst.inst_opcode = JMP`
  >- (`SUC k = LENGTH (non_param_insts bb)` by
        (qspecl_then [`fn`,`bb`,`k`] mp_tac
           fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
         simp[] >> disch_then (qspec_then `k` mp_tac) >> simp[] >> gvs[]) >>
      `bb.bb_instructions = get_params bb.bb_instructions ++ non_param_insts bb` by
        metis_tac[fnPlanLineageCallersTheory.ready_block_parameter_suffix] >>
      `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) + SUC k` by
        metis_tac[LENGTH_APPEND] >>
      `rest = []` by
        (qpat_x_assum `DROP k _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
         Cases_on `rest` >> simp[] >> decide_tac) >>
      `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> fs[]) >>
      `PRE (LENGTH bb.bb_instructions) = LENGTH (get_params bb.bb_instructions) + k` by decide_tac >>
      `LAST bb.bb_instructions = inst` by metis_tac[LAST_EL] >>
      Cases_on `b = 0` >> gvs[]
      >- (gvs[elem_count_zero_iff, indicator_zero_iff] >>
          irule native_terminal_jmp_nondefining_absent >>
          qexistsl_tac [`bb`,`dfg`,`fn`,`ops`,`before`] >>
          `PRE (LENGTH (get_params bb.bb_instructions) + LENGTH (non_param_insts bb)) =
             k + LENGTH (get_params bb.bb_instructions)` by decide_tac >> simp[] >> gvs[]) >>
      `b = 1` by decide_tac >> gvs[] >>
      irule native_terminal_jmp_observer_upper >>
      qexistsl_tac [`bb`,`dfg`,`fn`,`ops`,`before`] >>
      `PRE (LENGTH (get_params bb.bb_instructions) + LENGTH (non_param_insts bb)) =
         k + LENGTH (get_params bb.bb_instructions)` by decide_tac >> simp[] >> gvs[]) >>
  Cases_on `b = 0` >> gvs[]
  >- (gvs[elem_count_zero_iff, indicator_zero_iff] >>
      drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        fnPlanLineageNativeOriginsTheory.native_inst_variable_origins >>
      disch_then (qspec_then `v` mp_tac) >> simp[] >>
      `LENGTH (compute_operands (EL k (non_param_insts bb))) <= 16 /\
       ((EL k (non_param_insts bb)).inst_opcode = OFFSET ==>
        (EL k (non_param_insts bb)).inst_outputs <> [])` by
        (conj_tac >- fs[codegen_ready_inst_def] >>
         strip_tac >> gvs[venomWfTheory.inst_wf_def] >>
         Cases_on `(EL k (non_param_insts bb)).inst_outputs` >> gvs[]) >> metis_tac[]) >>
  `b = 1` by decide_tac >> gvs[] >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    fnPlanLineageSetupTheory.native_inst_observer_upper >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> gvs[codegen_ready_inst_def]
QED

Theorem ordinary_inst_uses_compute_operands:
  !inst v. inst_wf inst /\ MEM v (inst_uses inst) ==>
    MEM (Var v) (compute_operands inst)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compute_operands_def, venomInstTheory.inst_uses_def,
      passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  IF_CASES_TAC
  >- simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER] >>
  IF_CASES_TAC
  >- (gvs[venomWfTheory.inst_wf_def] >>
      Cases_on `inst.inst_operands` >> gvs[]) >>
  simp[]
QED

Theorem analyzed_live_loss_compute_operand:
  !fn bb i v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    MEM (Var v) (compute_operands (EL i bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >>
     metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label i =
    liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`bb.bb_label`,`bb`,`i`] mp_tac) >> simp[]) >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, EVERY_MEM] >>
     metis_tac[EL_MEM]) >>
  irule ordinary_inst_uses_compute_operands >> simp[] >>
  gvs[livenessDefsTheory.liveness_transfer_def, livenessProofsTheory.live_update_mem,
      livenessDefsTheory.MEM_ordered_inst_uses]
QED

(* Terminal JMPs neither consume nor define variables.  Reuse the native
   absence boundary rather than duplicating the target restoration proof. *)

Theorem native_indexed_ordinary_step_demand_support:
  !fn bb dfg k before inst rest ops after v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    DROP k (non_param_insts bb) = inst::rest /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
    ~is_param_opcode inst.inst_opcode /\ ~MEM v inst.inst_outputs /\
    (!w. MEM (Var w) (compute_operands inst) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
    LIST_ELEM_COUNT (Var v) before.ps_stack +
      (if Var v IN FDOM before.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+k))) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1))
      (bb_is_halting bb)
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label before = SOME (ops,after) ==>
    ((MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) ==>
      MEM v (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1)))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  drule_all native_indexed_step_layout >> strip_tac >>
  `LENGTH (compute_operands inst) <= 16 /\
   ((inst.inst_opcode = PHI \/ inst.inst_opcode = OFFSET) ==> inst.inst_outputs <> [])` by
    (conj_tac >- fs[codegen_ready_inst_def] >>
     strip_tac >> gvs[venomWfTheory.inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled` by
    (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
       fnPlanLineageNativeOriginsTheory.native_inst_variable_origins >>
     disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  `LENGTH (get_params bb.bb_instructions)+k < LENGTH bb.bb_instructions` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) +
      k + SUC (LENGTH rest)` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     qpat_x_assum `DROP k _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  ` (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1)) =
      live_vars_at (liveness_analyze fn) bb.bb_label
        (SUC (LENGTH (get_params bb.bb_instructions)+k))` by
    (Cases_on `rest` >> simp[NoAsms] >> AP_TERM_TAC >> gvs[NoAsms] >> decide_tac) >>
  gvs[] >> spose_not_then assume_tac >>
  `MEM (Var v) (compute_operands (EL (k + LENGTH (get_params bb.bb_instructions)) bb.bb_instructions))` by
    (irule analyzed_live_loss_compute_operand >> simp[] >> metis_tac[]) >>
  gvs[] >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    fnPlanLineageSetupTheory.native_inst_last_use_extinction >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem native_indexed_ordinary_step_dead_absent:
  !fn bb dfg k before inst rest ops after v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    DROP k (non_param_insts bb) = inst::rest /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
    ~is_param_opcode inst.inst_opcode /\ ~MEM v inst.inst_outputs /\
    (!w. MEM (Var w) (compute_operands inst) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
    LIST_ELEM_COUNT (Var v) before.ps_stack +
      (if Var v IN FDOM before.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+k))) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1))
      (bb_is_halting bb)
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label before = SOME (ops,after) /\
    ~MEM v (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1)) ==>
    ~MEM (Var v) after.ps_stack /\ Var v NOTIN FDOM after.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_indexed_ordinary_step_demand_support >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem native_indexed_step_fresh_output_resource_bound:
  !fn bb dfg k before inst rest ops after v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    DROP k (non_param_insts bb) = inst::rest /\ MEM v inst.inst_outputs /\
    ~MEM (Var v) before.ps_stack /\ Var v NOTIN FDOM before.ps_spilled /\
    (LENGTH (collect_phis bb.bb_instructions) <= k ==>
      !w. MEM (Var w) (compute_operands inst) ==>
        MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1))
      (bb_is_halting bb)
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label before = SOME (ops,after) ==>
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_indexed_step_layout >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
           is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
           venomInstTheory.is_raw_fmp_opcode_def, venomInstTheory.is_param_opcode_def] >>
      strip_tac >>
      qpat_x_assum `inst = EL (_ + k) bb.bb_instructions`
        (fn th => qpat_x_assum `generate_phi_plan _ _ _ _ = _`
          (mp_tac o REWRITE_RULE [Once arithmeticTheory.ADD_COMM, GSYM th])) >>
      strip_tac >> drule generate_phi_plan_resource_bound >>
      disch_then (qspec_then `v` mp_tac) >>
      `LIST_ELEM_COUNT (Var v) before.ps_stack = 0` by
        gvs[GSYM LIST_ELEM_COUNT_MEM] >> simp[] >>
      Cases_on `v = HD inst.inst_outputs` >> gvs[]) >>
  `inst.inst_opcode <> JMP` by (strip_tac >> gvs[venomWfTheory.inst_wf_def]) >>
  `!w. MEM (Var w) (compute_operands inst) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by metis_tac[] >>
  `~MEM (Var v) (compute_operands inst)` by metis_tac[] >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    fnPlanLineageSetupTheory.native_inst_fresh_output_resource_bound >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem distinct_flat_map_prefix_exclusion:
  !f xs k x rest v.
    ALL_DISTINCT (FLAT (MAP f xs)) /\ DROP k xs = x::rest /\ MEM v (f x) ==>
    ~EXISTS (\y. MEM v (f y)) (TAKE k xs)
Proof
  rpt gen_tac >> strip_tac >>
  `xs = TAKE k xs ++ DROP k xs` by simp[] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  once_asm_rewrite_tac[] >>
  simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP,
       EVERY_MEM, combinTheory.o_DEF] >>
  metis_tac[]
QED

Theorem native_inst_prefix_phase_resource_bound:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !bb v b.
      b <= 1 /\ lv = liveness_analyze fn /\ cfg = cfg_analyze fn /\ lbl = bb.bb_label /\
      halt = bb_is_halting bb /\ n = LENGTH (get_params bb.bb_instructions) /\
      len = LENGTH bb.bb_instructions /\ xs = non_param_insts bb /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
      (EXISTS (\i. MEM v i.inst_outputs) xs ==> b = 0) /\
      LIST_ELEM_COUNT (Var v) incoming.ps_stack +
        (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= b /\
      (!j before w. j < k /\ LENGTH (collect_phis bb.bb_instructions) <= j /\
        fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming j before ==>
        (MEM w (live_vars_at lv lbl (n+j)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
        (MEM (Var w) (compute_operands (EL j xs)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled)) ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
      (if b = 1 \/ EXISTS (\i. MEM v i.inst_outputs) (TAKE k xs) then 1 else 0)
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_strongind >>
  conj_tac >- (rpt strip_tac >> Cases_on `b = 1` >> gvs[] >>
    `b = 0` by decide_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ before = SOME (ops,after)` >>
  `LIST_ELEM_COUNT (Var v) before.ps_stack +
    (if Var v IN FDOM before.ps_spilled then 1 else 0) <=
    (if b = 1 \/ EXISTS (\i. MEM v i.inst_outputs) (TAKE k (non_param_insts bb)) then 1 else 0)` by
    (first_x_assum irule >> simp[] >>
     rpt strip_tac >> `j < SUC k` by decide_tac >> metis_tac[]) >>
  `k < LENGTH (non_param_insts bb) /\ inst = EL k (non_param_insts bb)` by
    (drule_all native_indexed_step_layout >> simp[]) >>
  `TAKE (SUC k) (non_param_insts bb) = TAKE k (non_param_insts bb) ++ [inst]` by
    simp[TAKE_SUC_BY_TAKE] >>
  Cases_on `MEM v inst.inst_outputs`
  >- (`~EXISTS (\i. MEM v i.inst_outputs) (TAKE k (non_param_insts bb))` by
        (irule distinct_flat_map_prefix_exclusion >> metis_tac[]) >>
      `b = 0` by
        (qpat_x_assum `(EXISTS _ _ ==> _)` irule >>
         simp[EXISTS_MEM] >> qexists_tac `inst` >> simp[] >> metis_tac[EL_MEM]) >>
      gvs[elem_count_zero_iff, indicator_zero_iff] >>
      irule native_indexed_step_fresh_output_resource_bound >> simp[] >>
      goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `DROP _ _ = _`)) >> simp[] >>
      rpt strip_tac >> qpat_x_assum `!j before w. _` (qspecl_then [`k`,`before`,`w`] mp_tac) >>
      simp[]) >>
  gvs[] >>
  irule native_indexed_step_nondefining_observer_bound >> simp[] >>
  (conj_tac >- (IF_CASES_TAC >> simp[])) >>
  goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `DROP _ _ = _`)) >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!j before w. _` (qspecl_then [`k`,`before`,`w`] mp_tac) >>
  simp[]
QED

Theorem native_inst_prefix_nondefining_observer_bound:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !bb v b.
      b <= 1 /\ lv = liveness_analyze fn /\ cfg = cfg_analyze fn /\ lbl = bb.bb_label /\
      halt = bb_is_halting bb /\ n = LENGTH (get_params bb.bb_instructions) /\
      len = LENGTH bb.bb_instructions /\ xs = non_param_insts bb /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions /\
      LIST_ELEM_COUNT (Var v) incoming.ps_stack +
        (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= b /\
      (!j before w. j < k /\ LENGTH (collect_phis bb.bb_instructions) <= j /\
        fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming j before ==>
        (MEM w (live_vars_at lv lbl (n+j)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
        (MEM (Var w) (compute_operands (EL j xs)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled)) ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= b
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_strongind >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ before = SOME (ops,after)` >>
  `LIST_ELEM_COUNT (Var v) before.ps_stack +
    (if Var v IN FDOM before.ps_spilled then 1 else 0) <= b` by
    (first_x_assum irule >> simp[] >> qexists_tac `bb` >> simp[] >>
     rpt strip_tac >> `j < SUC k` by decide_tac >> metis_tac[]) >>
  irule native_indexed_step_nondefining_observer_bound >> simp[] >>
  goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `DROP _ _ = _`)) >> simp[] >>
  `k < LENGTH (non_param_insts bb)` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k (non_param_insts bb)` by metis_tac[HD_DROP, HD] >>
  conj_tac
  >- (`MEM (EL k (non_param_insts bb)) (non_param_insts bb)` by simp[EL_MEM] >>
      `MEM (EL k (non_param_insts bb)) bb.bb_instructions` by
        gvs[non_param_insts_def, MEM_FILTER] >>
      gvs[EVERY_MEM]) >>
  strip_tac >>
  qpat_x_assum `!j before w. _` (qspecl_then [`k`,`before`] mp_tac) >>
  simp[] >> metis_tac[]
QED


Theorem native_inst_prefix_nondefining_observer_upper:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !bb v.
      lv = liveness_analyze fn /\ cfg = cfg_analyze fn /\ lbl = bb.bb_label /\
      halt = bb_is_halting bb /\ n = LENGTH (get_params bb.bb_instructions) /\
      len = LENGTH bb.bb_instructions /\ xs = non_param_insts bb /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions /\
      LIST_ELEM_COUNT (Var v) incoming.ps_stack +
        (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1 /\
      (!j before w. j < k /\ LENGTH (collect_phis bb.bb_instructions) <= j /\
        fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming j before ==>
        (MEM w (live_vars_at lv lbl (n+j)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
        (MEM (Var w) (compute_operands (EL j xs)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled)) ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule native_inst_prefix_nondefining_observer_bound >>
  disch_then (qspecl_then [`bb`,`v`,`1`] mp_tac) >> gvs[] >> metis_tac[]
QED

Theorem native_inst_prefix_nondefining_absent:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !bb v.
      lv = liveness_analyze fn /\ cfg = cfg_analyze fn /\ lbl = bb.bb_label /\
      halt = bb_is_halting bb /\ n = LENGTH (get_params bb.bb_instructions) /\
      len = LENGTH bb.bb_instructions /\ xs = non_param_insts bb /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions /\
      ~MEM (Var v) incoming.ps_stack /\ Var v NOTIN FDOM incoming.ps_spilled /\
      (!j before w. j < k /\ LENGTH (collect_phis bb.bb_instructions) <= j /\
        fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming j before ==>
        (MEM w (live_vars_at lv lbl (n+j)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
        (MEM (Var w) (compute_operands (EL j xs)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled)) ==>
      ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule native_inst_prefix_nondefining_observer_bound >>
  disch_then (qspecl_then [`bb`,`v`,`0`] mp_tac) >>
  gvs[elem_count_zero_iff, indicator_zero_iff] >> metis_tac[]
QED

(* A selected physical cell, unlike mere PHI operand membership, consumes
   the entire unit resource budget. Reuse the existing PHI erasure boundary. *)
Theorem generate_phi_plan_selected_unit_extinction:
  !inst ps d v next halting ops qs.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = Var v /\
    ~MEM v next /\ v <> HD inst.inst_outputs /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 /\
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (Var v) ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >>
     drule planAlignTheory.stack_find_bound >> strip_tac >>
     fs[stack_peek_def] >>
     `LENGTH ps.ps_stack - (d+1) < LENGTH ps.ps_stack` by decide_tac >>
     metis_tac[EL_MEM]) >>
  `0 < LIST_ELEM_COUNT (Var v) ps.ps_stack` by
    metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF] >>
  `Var v NOTIN FDOM ps.ps_spilled` by
    (strip_tac >> gvs[] >> decide_tac) >>
  `LENGTH (FILTER (\op. op = Var v) ps.ps_stack) = 1` by
    (fs[LIST_ELEM_COUNT_DEF] >> decide_tac) >>
  irule fnPlanLineagePhiResourcesTheory.dead_phi_selected_erased >>
  qexistsl_tac [`d`,`halting`,`inst`,`next`,`ops`,`ps`] >> simp[]
QED

(* D describes the actual incoming path demand. Selection on demand loss
   is explicit: union-of-alternatives PHI liveness alone cannot supply it. *)
Theorem generate_phi_plan_observer_demand_transport:
  !inst ps v next halting ops qs D.
    v <> HD inst.inst_outputs /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> D v) /\
    (D v /\ ~MEM v next ==>
      ?d. stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
          stack_peek d ps.ps_stack = Var v) /\
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==> MEM v next)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `MEM v next` >- simp[] >>
  Cases_on `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled`
  >- (`D v` by metis_tac[] >>
      `?d. stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
           stack_peek d ps.ps_stack = Var v` by metis_tac[] >>
      drule_all generate_phi_plan_selected_unit_extinction >> simp[]) >>
  `LIST_ELEM_COUNT (Var v) ps.ps_stack +
    (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 0` by
    (simp[resource_zero_iff_absent] >> metis_tac[]) >>
  drule_all generate_phi_plan_nondefining_resource_nonincrease >>
  simp[] >> strip_tac >>
  `LIST_ELEM_COUNT (Var v) qs.ps_stack +
    (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 0` by gvs[] >>
  fs[resource_zero_iff_absent]
QED

(* Active branch cleanup erases unsupported unique stack cells, but leaves
   spill debt unchanged. This is an exact boundary, not spill extinction. *)
Theorem clean_stack_plan_unsupported_spill_debt:
  !lv cfg fn bb pred pred_bb v ps ops qs.
    cfg_preds_of cfg bb.bb_label = [pred] /\
    1 < LENGTH (cfg_succs_of cfg pred) /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)) /\
    ~MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack <= 1 /\
    clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) <=>
      Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnPlanLineageInventoryTheory.clean_stack_plan_branch_unique_absent >>
  strip_tac >>
  drule fnPlanLineageInventoryTheory.clean_stack_plan_spilled_unchanged >> simp[]
QED

Theorem clean_stack_plan_observer_support_iff_spill_support:
  !lv cfg fn bb pred pred_bb v ps ops qs.
    cfg_preds_of cfg bb.bb_label = [pred] /\
    1 < LENGTH (cfg_succs_of cfg pred) /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack <= 1 /\
    ((MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
      MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions))) /\
    clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
    (((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
       MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0))) <=>
     (Var v IN FDOM ps.ps_spilled ==>
       MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0))))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0))`
  >- simp[] >>
  Cases_on `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled`
  >- (`MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions))` by metis_tac[] >>
      drule_all clean_stack_plan_unsupported_spill_debt >> simp[] >> metis_tac[]) >>
  `LIST_ELEM_COUNT (Var v) ps.ps_stack +
    (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 0` by
    (simp[resource_zero_iff_absent] >> metis_tac[]) >>
  drule clean_stack_plan_resource_nonincrease >> disch_then (qspec_then `v` mp_tac) >>
  strip_tac >>
  `LIST_ELEM_COUNT (Var v) qs.ps_stack +
    (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 0` by gvs[] >>
  fs[resource_zero_iff_absent] >> metis_tac[]
QED

(* Every regular instruction has a release cut, irrespective of incoming
   spill debt or transient resources created by its planning operations. *)
Theorem generate_regular_inst_plan_spill_support:
  !lv dfg cfg fn inst next halt term lbl ps ops qs v.
    generate_regular_inst_plan lv dfg cfg fn inst next halt term lbl ps = (ops,qs) ==>
    (Var v IN FDOM qs.ps_spilled ==> MEM v next)
Proof
  rpt gen_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  simp[fnPlanLineageInventoryTheory.release_dead_spills_domain, MEM_MAP]
QED

Theorem generate_regular_inst_plan_dead_stack_absence_total:
  !lv dfg cfg fn inst next halt term lbl ps ops qs v.
    generate_regular_inst_plan lv dfg cfg fn inst next halt term lbl ps = (ops,qs) /\
    ~MEM v next /\ ~MEM (Var v) qs.ps_stack ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_regular_inst_plan_spill_support >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem native_inst_prefix_phi_resource_nonincrease:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !v. (!i. i < k ==> (EL i xs).inst_opcode = PHI /\
          v <> HD (EL i xs).inst_outputs) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
      (if Var v IN FDOM incoming.ps_spilled then 1 else 0)
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_ind >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ mid = SOME (ops,final)` >>
  `k < LENGTH xs` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k xs` by metis_tac[HD_DROP, HD] >>
  `LIST_ELEM_COUNT (Var v) mid.ps_stack +
    (if Var v IN FDOM mid.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
    (if Var v IN FDOM incoming.ps_spilled then 1 else 0)` by
    (first_x_assum irule >> rpt strip_tac >> `i < SUC k` by decide_tac >> metis_tac[]) >>
  qpat_x_assum `!i. i < SUC k ==> _` (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def] >>
  drule generate_phi_plan_nondefining_resource_nonincrease >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Extinction uses the actual selected stack cell, not the predecessor's pair. *)
Theorem native_indexed_phi_selected_unit_extinction:
  !fn bb dfg j before inst rest ops after v d.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    DROP j (non_param_insts bb) = inst::rest /\
    MEM v (inst_uses inst) /\ v <> HD inst.inst_outputs /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) before.ps_stack = SOME d /\
    stack_peek d before.ps_stack = Var v /\
    LIST_ELEM_COUNT (Var v) before.ps_stack +
      (if Var v IN FDOM before.ps_spilled then 1 else 0) <= 1 /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (j + LENGTH (get_params bb.bb_instructions) + 1))
      (bb_is_halting bb)
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label before = SOME (ops,after) ==>
    ~MEM (Var v) after.ps_stack /\ Var v NOTIN FDOM after.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_indexed_step_layout >> strip_tac >>
  qspec_then `bb` (qx_choose_then `tail` assume_tac)
    fnPlanLineageEntryProductionTheory.non_param_insts_phi_prefix >>
  `inst = EL j (collect_phis bb.bb_instructions)` by gvs[EL_APPEND1] >>
  `inst.inst_opcode = PHI` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem, EL_MEM] >>
  `get_params bb.bb_instructions = []` by
    (`collect_phis bb.bb_instructions <> []` by
       (Cases_on `collect_phis bb.bb_instructions` >> gvs[]) >>
     drule_all fnPlanLineagePhiScheduleTheory.ready_phi_block_suffix >> simp[]) >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC j))` by
    (`wf_function fn` by fs[codegen_ready_fn_def] >>
     irule fnPlanLineageLivenessTheory.analyzed_phi_incoming_dead_after >>
     simp[] >> qexists_tac `j` >> simp[] >>
     metis_tac[fnPlanLineagePhiInputExclusionTheory.phi_codegen_block_ready]) >>
  `rest <> []` by
    (`collect_phis bb.bb_instructions <> []` by
       (Cases_on `collect_phis bb.bb_instructions` >> gvs[]) >>
     drule_all fnPlanLineagePhiScheduleTheory.ready_phi_block_suffix >>
     strip_tac >>
     `LENGTH (collect_phis bb.bb_instructions) < LENGTH (non_param_insts bb)` by
       (gvs[] >>
        qpat_x_assum `bb.bb_instructions = _ ++ rest'`
          (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
        simp[] >> Cases_on `rest'` >> gvs[] >> decide_tac) >>
     qpat_x_assum `DROP j _ = _`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     Cases_on `rest` >> gvs[] >> decide_tac) >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, arithmeticTheory.ADD1] >>
  drule_all generate_phi_plan_selected_unit_extinction >> simp[]
QED

Theorem native_inst_prefix_phi_selected_extinction:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !bb v j before d.
      lv = liveness_analyze fn /\ cfg = cfg_analyze fn /\
      lbl = bb.bb_label /\ halt = bb_is_halting bb /\
      n = LENGTH (get_params bb.bb_instructions) /\
      len = LENGTH bb.bb_instructions /\ xs = non_param_insts bb /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
      k <= LENGTH (collect_phis bb.bb_instructions) /\ j < k /\
      (!i. i < k ==> v <> HD (EL i xs).inst_outputs) /\
      MEM v (inst_uses (EL j xs)) /\
      fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming j before /\
      stack_get_phi_depth (FILTER is_var_operand (EL j xs).inst_operands) before.ps_stack = SOME d /\
      stack_peek d before.ps_stack = Var v /\
      LIST_ELEM_COUNT (Var v) incoming.ps_stack +
        (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1 ==>
      ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_strongind >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ mid = SOME (ops,final)` >>
  `inst = EL k xs /\ k < LENGTH xs` by
    (`k < LENGTH xs` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
        simp[] >> decide_tac) >> metis_tac[HD_DROP, HD]) >>
  qspec_then `bb` (qx_choose_then `tail` assume_tac)
    fnPlanLineageEntryProductionTheory.non_param_insts_phi_prefix >>
  `!i. i < SUC k ==> (EL i xs).inst_opcode = PHI /\ v <> HD (EL i xs).inst_outputs` by
    (rpt gen_tac >> strip_tac >> conj_tac >-
       (`i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
        `EL i xs = EL i (collect_phis bb.bb_instructions)` by gvs[EL_APPEND1] >>
        metis_tac[livenessTransferProofsTheory.collect_phis_mem, EL_MEM]) >> metis_tac[]) >>
  Cases_on `j < k`
  >- (`~MEM (Var v) mid.ps_stack /\ Var v NOTIN FDOM mid.ps_spilled` by
        (first_x_assum irule >> simp[] >>
         conj_tac >- (qexists_tac `bb` >> simp[] >> decide_tac) >>
         qexistsl [`before`,`d`,`j`] >> gvs[]) >>
      `inst.inst_opcode = PHI /\ v <> HD inst.inst_outputs` by
        (qpat_x_assum `!i. i < SUC k ==> _ /\ _` (qspec_then `k` mp_tac) >> gvs[]) >>
      gvs[generate_inst_plan_def, is_pre_codegen_opcode_def] >>
      drule generate_phi_plan_nondefining_resource_nonincrease >>
      disch_then (qspec_then `v` mp_tac) >>
      `LIST_ELEM_COUNT (Var v) mid.ps_stack = 0` by
        metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
      simp[resource_zero_iff_absent] >> metis_tac[]) >>
  `j = k` by decide_tac >>
  `before = mid` by metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_deterministic] >>
  `LIST_ELEM_COUNT (Var v) mid.ps_stack +
    (if Var v IN FDOM mid.ps_spilled then 1 else 0) <= 1` by
    (drule native_inst_prefix_phi_resource_nonincrease >>
     disch_then (qspec_then `v` mp_tac) >>
     impl_tac >- (rpt strip_tac >> `i < SUC k` by decide_tac >> metis_tac[]) >>
     gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `!bb v j before d. _` kall_tac >>
  gvs[] >>
  irule (SRULE [arithmeticTheory.ADD_ASSOC] native_indexed_phi_selected_unit_extinction) >>
  qexists_tac `bb` >> simp[GSYM arithmeticTheory.ADD_ASSOC] >>
  goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_SUC_REFL, arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

(* Both stack survival and spill survival leave an unselected alternative;
   neither form of survival is claimed impossible. *)
Theorem native_inst_prefix_phi_survivor_unselected:
  !fn bb dfg incoming k qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k qs /\
    k <= LENGTH (collect_phis bb.bb_instructions) /\
    (!i. i < k ==> v <> HD (EL i (non_param_insts bb)).inst_outputs) /\
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
      (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1 /\
    (MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
    !j before d.
      j < k /\ MEM v (inst_uses (EL j (non_param_insts bb))) /\
      fnPlanLineageEntryProduction$native_inst_prefix
        (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) incoming j before ==>
      ~(stack_get_phi_depth
          (FILTER is_var_operand (EL j (non_param_insts bb)).inst_operands)
          before.ps_stack = SOME d /\
        stack_peek d before.ps_stack = Var v)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  strip_tac >>
  qpat_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs`
    (mp_then Any mp_tac native_inst_prefix_phi_selected_extinction) >>
  disch_then (qspecl_then [`bb`,`v`] mp_tac) >>
  disch_then (qspecl_then [`j`,`before`,`d`] mp_tac) >> simp[]
QED

(* Dead spill entries are allowed here: only analyzed reads, not spill
   membership, control whether an ordinary step can recreate a stack cell. *)
Theorem native_ordinary_dead_stack_step:
  !fn bb i inst dfg ps ops qs v halt term.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
    inst.inst_opcode <> PHI /\ ~MEM v inst.inst_outputs /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) /\
    ~MEM (Var v) ps.ps_stack /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halt term bb.bb_label ps = SOME (ops,qs) ==>
    ~MEM (Var v) qs.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf inst /\ codegen_ready_inst inst` by
    (irule fnPlanLineageQuarantineTheory.ready_member_instruction_shape >>
     metis_tac[EL_MEM]) >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    metis_tac[fnPlanLineageCallersTheory.analyzed_computed_operand_demand] >>
  `~MEM (Var v) inst.inst_operands` by
    (strip_tac >>
     `MEM v (inst_uses inst)` by
       gvs[venomInstTheory.inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     `MEM (Var v) (compute_operands inst)` by
       metis_tac[ordinary_inst_uses_compute_operands] >>
     metis_tac[fnPlanLineageCallersTheory.analyzed_computed_operand_demand]) >>
  `!targets. inst.inst_opcode = JMP /\
    join_target_ops (liveness_analyze fn) fn bb.bb_label inst = SOME targets ==>
    ~MEM (Var v) targets` by
    (rpt gen_tac >> strip_tac >>
     `LAST bb.bb_instructions = inst /\ SUC i = LENGTH bb.bb_instructions` by
       (`wf_function fn` by fs[codegen_ready_fn_def] >>
        `~(i < LENGTH bb.bb_instructions - 1)` by
          (strip_tac >>
           drule passSimulationPropsTheory.wf_non_terminator_prefix >>
           disch_then (qspec_then `bb` mp_tac) >> simp[] >>
           metis_tac[venomInstTheory.is_terminator_def]) >>
        `i = PRE (LENGTH bb.bb_instructions)` by decide_tac >>
        `SUC i = LENGTH bb.bb_instructions` by decide_tac >>
        simp[] >> Cases_on `bb.bb_instructions` >> fs[] >> simp[LAST_EL]) >>
     `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
     `set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH bb.bb_instructions))) = set targets` by
       (irule fnPlanLineageEntryProductionTheory.native_terminal_jmp_target_set >>
        gvs[]) >>
     gvs[pred_setTheory.EXTENSION, MEM_MAP] >>
     qpat_x_assum `!x. _ <=> MEM x targets`
       (qspec_then `Var v` mp_tac) >> simp[]) >>
  conj_tac >-
    (drule_all fnPlanLineageQuarantineTheory.native_inst_stack_quarantine >> simp[]) >>
  simp[]
QED

(* Actual native scheduling, with demand exclusion propagated rather than
   supplied as a list of future read exclusions. JMP is allowed, including
   wide target restoration. *)
Theorem native_ordinary_interval_dead_stack:
  !lv dfg cfg fn label halt n len xs ps0 k ps.
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn label halt n len xs ps0 k ps ==>
    !bb a v. lv = liveness_analyze fn /\ cfg = cfg_analyze fn /\
      label = bb.bb_label /\ n = LENGTH (get_params bb.bb_instructions) + a /\
      len = LENGTH bb.bb_instructions /\ xs = DROP a (non_param_insts bb) /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      ~MEM v (live_vars_at lv label n) /\ ~MEM (Var v) ps0.ps_stack /\
      (!j. j < k ==> (EL j xs).inst_opcode <> PHI /\
        ~MEM v (EL j xs).inst_outputs) ==>
      ~MEM (Var v) ps.ps_stack /\ ~MEM v (live_vars_at lv label (n+k))
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_ind >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  `DROP (a+k) (non_param_insts bb) = inst::rest` by
    gvs[DROP_DROP_T, arithmeticTheory.ADD_COMM] >>
  `a+k < LENGTH (non_param_insts bb)` by
    (qpat_x_assum `DROP (a+k) _ = _`
      (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[] >> decide_tac) >>
  `inst = EL (a+k) (non_param_insts bb)` by metis_tac[HD_DROP, HD] >>
  `inst = EL (LENGTH (get_params bb.bb_instructions)+(a+k)) bb.bb_instructions` by
    metis_tac[fnPlanLineageCallersTheory.ready_block_suffix_index] >>
  `LENGTH (get_params bb.bb_instructions)+(a+k) < LENGTH bb.bb_instructions` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `EL k (DROP a (non_param_insts bb)) = inst` by
    (`k < LENGTH (DROP a (non_param_insts bb))` by simp[] >> metis_tac[HD_DROP, HD]) >>
  `inst.inst_opcode <> PHI /\ ~MEM v inst.inst_outputs` by
    (qpat_x_assum `!j. j < SUC k ==> _` (qspec_then `k` mp_tac) >>
     pure_asm_rewrite_tac[] >> simp[]) >>
  `~MEM (Var v) ps.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+(a+k)))` by
    (first_x_assum (qspecl_then [`bb`,`a`,`v`] mp_tac) >>
     asm_simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
     impl_tac >- (rpt strip_tac >> `j < SUC k` by decide_tac >> metis_tac[]) >> simp[]) >>
  `(if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at (liveness_analyze fn) bb.bb_label
       (k + (LENGTH (get_params bb.bb_instructions)+a) + 1)) =
     live_vars_at (liveness_analyze fn) bb.bb_label
       (SUC (LENGTH (get_params bb.bb_instructions)+(a+k)))` by
    (`k + (LENGTH (get_params bb.bb_instructions)+a) + 1 =
      (a+k) + LENGTH (get_params bb.bb_instructions) + 1` by decide_tac >>
     pop_assum (fn th => pure_rewrite_tac[th]) >>
     irule fnPlanLineageCallersTheory.ready_block_suffix_next_live >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  rule_assum_tac (SIMP_RULE bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `_ = live_vars_at _ _ (SUC _)`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  drule_all native_ordinary_dead_stack_step >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_CLAUSES]
QED

(* A PHI never restores an absent alternative from spill debt. In particular,
   no exclusion from the PHI's unfiltered operands is needed. *)
Theorem native_phi_interval_stack_absent:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !v. ~MEM (Var v) incoming.ps_stack /\
      (!i. i < k ==> (EL i xs).inst_opcode = PHI /\
        (EL i xs).inst_outputs <> [] /\ ~MEM v (EL i xs).inst_outputs) ==>
      ~MEM (Var v) qs.ps_stack
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_ind >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `k < LENGTH xs` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k xs` by metis_tac[HD_DROP, HD] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ mid = SOME (ops,final)` >>
  `~MEM (Var v) mid.ps_stack` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     `i < SUC k` by decide_tac >> metis_tac[]) >>
  qpat_x_assum `!i. i < SUC k ==> _` (qspec_then `k` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def] >>
  metis_tac[fnPlanLineageQuarantineTheory.phi_declared_output_stack_support]
QED

Theorem native_ordinary_dead_stack_release:
  !fn bb i inst dfg ps ops qs v halt term.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> OFFSET /\
    ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> NOP /\
    ~MEM v inst.inst_outputs /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) /\
    ~MEM (Var v) ps.ps_stack /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halt term bb.bb_label ps = SOME (ops,qs) ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_ordinary_dead_stack_step >> strip_tac >> simp[] >>
  `generate_regular_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
    halt term bb.bb_label ps = (ops,qs)` by
    gvs[generate_inst_plan_def, AllCaseEqs()] >>
  drule generate_regular_inst_plan_spill_support >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem native_inst_prefix_between:
  !lv dfg cfg fn lbl halt n len xs incoming a seed k qs.
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt n len xs incoming a seed /\
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt n len xs incoming k qs /\ a <= k ==>
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt (n+a) len (DROP a xs) seed (k-a) qs
Proof
  rpt gen_tac >> strip_tac >>
  `k = a + (k-a)` by decide_tac >>
  `?mid. fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt n len xs incoming a mid /\
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt (n+a) len (DROP a xs) mid (k-a) qs` by
    (irule fnPlanLineageEntryProductionTheory.native_inst_prefix_split >> simp[]) >>
  metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_deterministic]
QED

Theorem native_seeded_ordinary_dead_stack:
  !fn bb dfg a k incoming seed qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= k /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming a seed /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k qs /\
    ~MEM (Var v) seed.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+a)) /\
    (!j. a <= j /\ j < k ==> (EL j (non_param_insts bb)).inst_opcode <> PHI /\
      ~MEM v (EL j (non_param_insts bb)).inst_outputs) ==>
    ~MEM (Var v) qs.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+k))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_inst_prefix_between >> strip_tac >>
  `!j. j < k-a ==> (EL j (DROP a (non_param_insts bb))).inst_opcode <> PHI /\
      ~MEM v (EL j (DROP a (non_param_insts bb))).inst_outputs` by
    (rpt strip_tac >>
     `a+j < k /\ a <= a+j` by decide_tac >>
     `k <= LENGTH (non_param_insts bb)` by
       metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_bound] >>
     `j < LENGTH (DROP a (non_param_insts bb))` by (simp[] >> decide_tac) >>
     gvs[EL_DROP] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule native_ordinary_interval_dead_stack >>
  disch_then (qspecl_then [`bb`,`a`,`v`] mp_tac) >> simp[]
QED

Theorem native_seeded_phi_stack_absent:
  !lv dfg cfg fn lbl halt n len xs incoming a seed k qs v.
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt n len xs incoming a seed /\
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt n len xs incoming k qs /\ a <= k /\
    ~MEM (Var v) seed.ps_stack /\
    (!j. a <= j /\ j < k ==> (EL j xs).inst_opcode = PHI /\
      (EL j xs).inst_outputs <> [] /\ ~MEM v (EL j xs).inst_outputs) ==>
    ~MEM (Var v) qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `k <= LENGTH xs` by
    metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_bound] >>
  drule_all native_inst_prefix_between >> strip_tac >>
  drule native_phi_interval_stack_absent >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  impl_tac >- (rpt strip_tac >>
    `i < LENGTH (DROP a xs)` by (simp[] >> decide_tac) >>
    gvs[EL_DROP] >> first_x_assum irule >> decide_tac) >> simp[]
QED

Theorem native_seeded_phi_body_dead_stack:
  !fn bb dfg a k incoming seed qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ a <= k /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming a seed /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k qs /\
    ~MEM (Var v) seed.ps_stack /\
    (LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+k ==>
      ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (MAX (LENGTH (get_params bb.bb_instructions)+a)
          (LENGTH (collect_phis bb.bb_instructions))))) /\
    (!j. a <= j /\ j < k ==> ~MEM v (EL j (non_param_insts bb)).inst_outputs) ==>
    ~MEM (Var v) qs.ps_stack /\
    (LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+k ==>
      ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `k <= LENGTH (non_param_insts bb)` by
    metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_bound] >>
  Cases_on `LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+a`
  >- suspend "ordinary" >>
  `collect_phis bb.bb_instructions <> []` by (strip_tac >> gvs[]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    metis_tac[fnPlanLineagePhiScheduleTheory.ready_phi_block_suffix] >>
  gvs[] >>
  `!j. j < LENGTH (collect_phis bb.bb_instructions) ==>
    (EL j bb.bb_instructions).inst_opcode = PHI /\
    (EL j bb.bb_instructions).inst_outputs <> []` by
    suspend "phi_shape" >>
  Cases_on `k <= LENGTH (collect_phis bb.bb_instructions)`
  >- suspend "phi_only" >>
  suspend "crossing"
QED

Resume native_seeded_phi_body_dead_stack[ordinary]:
  `MAX (LENGTH (get_params bb.bb_instructions)+a)
    (LENGTH (collect_phis bb.bb_instructions)) = LENGTH (get_params bb.bb_instructions)+a` by simp[arithmeticTheory.MAX_DEF] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+k` by decide_tac >>
  gvs[] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] native_seeded_ordinary_dead_stack) >>
  simp[] >> qexistsl [`a`,`dfg`,`incoming`,`seed`] >> simp[] >>
  rpt strip_tac >>
  qspecl_then [`fn`,`bb`,`a`] mp_tac
    fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
  simp[] >> qexists `j` >> simp[] >> decide_tac
QED

Resume native_seeded_phi_body_dead_stack[phi_shape]:
  qspec_then `bb.bb_instructions` (qx_choose_then `tail` assume_tac)
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  rpt gen_tac >> strip_tac >>
  `EL j bb.bb_instructions = EL j (collect_phis bb.bb_instructions)` by (qpat_assum `bb.bb_instructions = _ ++ _`
      (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
      simp[EL_APPEND1]) >>
  `(EL j bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem, EL_MEM] >>
  `j < LENGTH bb.bb_instructions` by
    (qpat_x_assum `bb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst_wf (EL j bb.bb_instructions)` by
    metis_tac[fnPlanLineageQuarantineTheory.ready_member_instruction_shape, EL_MEM] >>
  gvs[venomWfTheory.inst_wf_def] >> Cases_on `(EL j bb.bb_instructions).inst_outputs` >> gvs[]
QED

Resume native_seeded_phi_body_dead_stack[phi_only]:
  reverse conj_tac >-
    (strip_tac >> `k = LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
     gvs[arithmeticTheory.MAX_DEF]) >>
  `!j. a <= j /\ j < k ==> (EL j bb.bb_instructions).inst_opcode = PHI /\
    (EL j bb.bb_instructions).inst_outputs <> [] /\
    ~MEM v (EL j bb.bb_instructions).inst_outputs` by
    (rpt strip_tac >>
     `j < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >> metis_tac[]) >>
  drule_all native_seeded_phi_stack_absent >> simp[]
QED

Resume native_seeded_phi_body_dead_stack[crossing]:
  qabbrev_tac `p = LENGTH (collect_phis bb.bb_instructions)` >>
  `a <= p /\ p <= k /\ k = p + (k-p)` by (simp[Abbr `p`] >> decide_tac) >>
  `?mid. fnPlanLineageEntryProduction$native_inst_prefix
    (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
    0 (LENGTH bb.bb_instructions) bb.bb_instructions incoming p mid` by
    (`fnPlanLineageEntryProduction$native_inst_prefix
       (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
       0 (LENGTH bb.bb_instructions) bb.bb_instructions incoming (p+(k-p)) qs` by
       metis_tac[] >>
     drule fnPlanLineageEntryProductionTheory.native_inst_prefix_split >>
     metis_tac[]) >>
  `!j. a <= j /\ j < p ==> (EL j bb.bb_instructions).inst_opcode = PHI /\
    (EL j bb.bb_instructions).inst_outputs <> [] /\
    ~MEM v (EL j bb.bb_instructions).inst_outputs` by
    (rpt strip_tac >> `j < k` by decide_tac >> metis_tac[]) >>
  `~MEM (Var v) mid.ps_stack` by
    (drule_all native_seeded_phi_stack_absent >> simp[]) >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label p)` by
    gvs[arithmeticTheory.MAX_DEF] >>
  `!j. p <= j /\ j < k ==> (EL j bb.bb_instructions).inst_opcode <> PHI /\
    ~MEM v (EL j bb.bb_instructions).inst_outputs` by
    (rpt gen_tac >> strip_tac >> reverse conj_tac >- metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
     qspecl_then [`fn`,`bb`,`p`] mp_tac
       fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
     simp[]) >>
  simp[] >>
  qspecl_then [`fn`,`bb`] mp_tac native_seeded_ordinary_dead_stack >>
  simp[] >> disch_then drule >>
  metis_tac[]
QED

Finalise native_seeded_phi_body_dead_stack

(* The demand bridge is used only after all PHIs have executed without a
   definition of the observer; it says nothing about raw PHI alternatives. *)
Theorem native_edge_phi_body_dead:
  !fn bb pred v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    ~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0)) /\
    EVERY (\inst. ~MEM v inst.inst_outputs) (collect_phis bb.bb_instructions) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (collect_phis bb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `phi_block_ready (liveness_analyze fn) bb` by
    metis_tac[fnPlanLineagePhiInputExclusionTheory.phi_codegen_block_ready] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >>
     metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze]) >>
  `EVERY (\inst. ~MEM v (inst_defs inst)) (collect_phis bb.bb_instructions)` by
    gvs[venomInstTheory.inst_defs_def] >>
  gvs[fnPlanLineageLivenessTheory.analyzed_ready_phi_live_through_edge]
QED

Theorem clean_stack_plan_stack_absent:
  !lv cfg fn bb ps ops qs v.
    clean_stack_plan lv cfg fn bb ps = (ops,qs) /\
    ~MEM (Var v) ps.ps_stack ==> ~MEM (Var v) qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  drule clean_stack_plan_resource_nonincrease >>
  disch_then (qspec_then `v` mp_tac) >>
  drule fnPlanLineageInventoryTheory.clean_stack_plan_spilled_unchanged >>
  strip_tac >> gvs[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem prepare_params_plan_stack_absent:
  !lv fn ps ops qs v.
    prepare_params_plan lv fn ps = (ops,qs) /\
    EVERY (\inst. v <> HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions) /\
    ~MEM (Var v) ps.ps_stack ==> ~MEM (Var v) qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `get_params (HD fn.fn_blocks).bb_instructions = []`
  >- gvs[prepare_params_plan_def] >>
  qpat_x_assum `prepare_params_plan _ _ _ = _` mp_tac >>
  simp[prepare_params_plan_def, fnPlanLineageSetupTheory.parameter_push_fold, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  strip_tac >>
  `MEM (Var v) ps''.ps_stack` by
    (qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _`
       (mp_tac o AP_TERM ``SND : stack_op list # plan_state -> plan_state``) >>
     simp[] >> disch_then (SUBST_ALL_TAC o SYM) >>
     gvs[SRULE [pred_setTheory.EXTENSION]
       fnPlanLineageSetupTheory.optimistic_swap_plan_slots]) >>
  drule_all fnPlanLineageQuarantineTheory.popmany_plan_stack_support >>
  gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem native_block_setup_stack_absent:
  !lv cfg fn bb ps ops qs v.
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps
     else if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
       clean_stack_plan lv cfg fn bb ps else ([],ps)) = (ops,qs) /\
    EVERY (\inst. v <> HD inst.inst_outputs) (get_params bb.bb_instructions) /\
    ~MEM (Var v) ps.ps_stack ==> ~MEM (Var v) qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bb = HD fn.fn_blocks`
  >- (gvs[] >> metis_tac[prepare_params_plan_stack_absent]) >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[] >>
  metis_tac[clean_stack_plan_stack_absent]
QED

(* A setup cut traverses every parameter push but only the specified worker
   prefix. No premise constrains outputs of the unexecuted worker tail. *)
Theorem native_setup_prefix_dead_stack:
  !fn bb dfg ps setup_ops start k qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    (if bb = HD fn.fn_blocks then prepare_params_plan (liveness_analyze fn) fn ps
     else if LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb ps
     else ([],ps)) = (setup_ops,start) /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    ~MEM (Var v) ps.ps_stack /\
    EVERY (\inst. v <> HD inst.inst_outputs) (get_params bb.bb_instructions) /\
    (LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+k ==>
      ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (MAX (LENGTH (get_params bb.bb_instructions))
          (LENGTH (collect_phis bb.bb_instructions))))) /\
    (!j. j < k ==> ~MEM v (EL j (non_param_insts bb)).inst_outputs) ==>
    ~MEM (Var v) qs.ps_stack /\
    (LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+k ==>
      ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (Var v) start.ps_stack` by
    (drule_all native_block_setup_stack_absent >> simp[]) >>
  irule native_seeded_phi_body_dead_stack >>
  simp[] >> qexistsl_tac [`0`, `dfg`, `start`, `start`] >>
  simp[fnPlanLineageEntryProductionTheory.native_inst_prefix_rules]
QED

Theorem native_incoming_prefix_dead_stack:
  !fn bb pred dfg ps setup_ops start k qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb ps
     else ([],ps)) = (setup_ops,start) /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    ~MEM (Var v) ps.ps_stack /\
    ~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0)) /\
    (!j. j < k ==> ~MEM v (EL j (non_param_insts bb)).inst_outputs) ==>
    ~MEM (Var v) qs.ps_stack /\
    (LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+k ==>
      ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageEntryProductionTheory.nonentry_block_no_params >>
     gvs[codegen_ready_fn_def] >> metis_tac[]) >>
  irule native_setup_prefix_dead_stack >> simp[] >>
  reverse conj_tac
  >- (qexistsl_tac [`dfg`, `ps`, `setup_ops`, `start`] >> gvs[]) >>
  strip_tac >>
  irule native_edge_phi_body_dead >> simp[] >>
  conj_tac >- (qexists_tac `pred` >> simp[]) >>
  simp[EVERY_EL] >> rpt strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  `n < k` by decide_tac >>
  `EL n (collect_phis bb.bb_instructions) = EL n bb.bb_instructions` by
    metis_tac[EL_APPEND1] >>
  gvs[] >> metis_tac[]
QED

Theorem ready_incoming_block_nonentry:
  !fn pred bb.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) ==>
    bb <> HD fn.fn_blocks
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  `fn.fn_blocks <> []` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  gvs[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  gvs[fnPlanLineageCallersTheory.ready_entry_no_clean]
QED

(* Stack support crosses an edge independently of spill debt. *)
Theorem analyzed_edge_setup_stack_support:
  !fn pred pb bb v ps ops qs.
    codegen_ready_fn fn /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
    (MEM (Var v) ps.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack <= 1 /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb ps
     else ([],ps)) = (ops,qs) ==>
    (MEM (Var v) qs.ps_stack ==>
      MEM v (input_vars_from pred bb.bb_instructions
        (live_vars_at (liveness_analyze fn) bb.bb_label 0)))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1`
  >- (gvs[] >>
      `MEM (Var v) ps.ps_stack` by metis_tac[clean_stack_plan_stack_absent] >>
      `MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by
        metis_tac[] >>
      Cases_on `1 < LENGTH (cfg_succs_of (cfg_analyze fn) pred)`
      >- (`cfg_preds_of (cfg_analyze fn) bb.bb_label = [pred]` by
            (Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> gvs[] >>
             Cases_on `t` >> gvs[]) >>
          spose_not_then assume_tac >>
          drule_all fnPlanLineageInventoryTheory.clean_stack_plan_branch_unique_absent >> simp[]) >>
      `cfg_succs_of (cfg_analyze fn) pred = [bb.bb_label]` by
        (Cases_on `cfg_succs_of (cfg_analyze fn) pred` >> gvs[] >>
         Cases_on `t` >> gvs[]) >>
      `wf_function fn` by fs[codegen_ready_fn_def] >>
      drule_all fnPlanLineageLivenessTheory.analyzed_live_out_singleton >>
      simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  gvs[] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  drule_all fnPlanLineageEdgeTheory.ready_join_edge_terminator >> strip_tac >>
  metis_tac[fnPlanLineageLivenessTheory.analyzed_live_out_jmp]
QED

Theorem native_inst_prefix_phi_schedule:
  !phis lv dfg cfg fn lbl halting np len rest ps qs.
    EVERY (\inst. inst.inst_opcode = PHI) phis /\ rest <> [] /\
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halting np len
      (phis ++ rest) ps (LENGTH phis) qs ==>
    ?ops. phi_schedule_run
      (MAPi (\j inst. (inst, live_vars_at lv lbl (j + np + 1), halting)) phis) ps = (ops,qs)
Proof
  Induct >> simp[fnPlanLineageEntryProductionTheory.native_inst_prefix_zero,
    fnPlanLineagePhiTemporalTheory.phi_schedule_run_def] >>
  rpt gen_tac >> strip_tac >>
  `1 + LENGTH phis = SUC (LENGTH phis)` by decide_tac >>
  `?mid. fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halting np len
       ((h::phis) ++ rest) ps 1 mid /\
     fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halting (np+1) len
       (phis ++ rest) mid (LENGTH phis) qs` by
    (qpat_x_assum `1 + _ = _` (fn eq =>
       drule (REWRITE_RULE [eq] (Q.SPECL [`LENGTH (phis : instruction list)`, `1`]
         fnPlanLineageEntryProductionTheory.native_inst_prefix_split))) >> simp[]) >>
  gvs[fnPlanLineageEntryProductionTheory.native_inst_prefix_one,
    generate_inst_plan_def, is_pre_codegen_opcode_def] >>
  first_x_assum (drule_at Any) >> strip_tac >>
  gvs[combinTheory.o_DEF, arithmeticTheory.ADD_CLAUSES,
    GSYM arithmeticTheory.ADD_ASSOC] >>
  `(\j (inst:instruction). (inst,live_vars_at lv lbl (SUC (np + (j + 1))),halting)) =
   (\j inst. (inst,live_vars_at lv lbl (j + (np + 2)),halting))` by
    (simp_tac bool_ss [FUN_EQ_THM, pairTheory.PAIR_EQ] >> rpt gen_tac >>
     AP_TERM_TAC >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  qexists_tac `ops ++ ops'` >> simp[]
QED

Theorem ready_native_inst_prefix_phi_schedule:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  collect_phis bb.bb_instructions <> [] /\
  fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halting 0 len
    bb.bb_instructions ps (LENGTH (collect_phis bb.bb_instructions)) qs ==>
  ?ops. phi_schedule_run
    (MAPi (\j inst. (inst,live_vars_at lv lbl (j+1),halting))
      (collect_phis bb.bb_instructions)) ps = (ops,qs)
Proof
  strip_tac >>
  drule_all fnPlanLineagePhiScheduleTheory.ready_phi_block_suffix >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode = PHI) (collect_phis bb.bb_instructions)` by
    (simp[EVERY_MEM] >> metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  `fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halting 0 len
    (collect_phis bb.bb_instructions ++ rest) ps
    (LENGTH (collect_phis bb.bb_instructions)) qs` by metis_tac[] >>
  drule_all native_inst_prefix_phi_schedule >> simp[]
QED

Theorem native_phi_schedule_endpoint:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  collect_phis bb.bb_instructions <> [] /\
  fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt 0 len
    bb.bb_instructions incoming (LENGTH (collect_phis bb.bb_instructions)) endpoint /\
  phi_origin_schedule_ready
    (MAPi (\j inst. (inst,live_vars_at lv lbl (j+1),halt))
      (collect_phis bb.bb_instructions)) padding other cells cells_end /\
  incoming.ps_stack = padding ++ MAP (phi_cell_value T) cells ==>
  endpoint.ps_stack = padding ++ MAP (phi_cell_value T) cells_end /\
  endpoint.ps_spilled = incoming.ps_spilled
Proof
  strip_tac >> drule_all ready_native_inst_prefix_phi_schedule >> strip_tac >>
  drule fnPlanLineagePhiTemporalTheory.phi_origin_schedule_state_replay >>
  disch_then (qspecl_then [`incoming`,
    `incoming with ps_stack := other ++ MAP (phi_cell_value F) cells`] mp_tac) >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem native_phi_endpoint_observer_support:
  codegen_ready_fn fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ collect_phis bb.bb_instructions <> [] /\
  fnPlanLineageEntryProduction$native_inst_prefix (liveness_analyze fn) dfg cfg fn lbl halt 0 len
    bb.bb_instructions incoming (LENGTH (collect_phis bb.bb_instructions)) endpoint /\
  phi_origin_schedule_ready
    (MAPi (\j inst. (inst,live_vars_at (liveness_analyze fn) lbl (j+1),halt))
      (collect_phis bb.bb_instructions)) padding other cells cells_end /\
  incoming.ps_stack = padding ++ MAP (phi_cell_value T) cells /\
  MAP (phi_cell_value T) cells = MAP Var
    (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) /\
  phi_origin_tagged (native_phi_class pred (collect_phis bb.bb_instructions)) cells /\
  EVERY (\c. ?op. c = PhiCommon op) cells_end /\
  EVERY (\op. op = dead_stack_marker) padding /\
  (!inst. MEM inst (collect_phis bb.bb_instructions) ==> ~MEM v inst.inst_outputs) ==>
  MEM (Var v) endpoint.ps_stack ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >> drule_all native_phi_schedule_endpoint >> strip_tac >>
  strip_tac >>
  `~MEM (Var v) padding` by
    (fs[EVERY_MEM] >>
     qpat_x_assum `!op. MEM op padding ==> _` (qspec_then `Var v` mp_tac) >>
     simp[dead_stack_marker_def]) >>
  `MEM (Var v) (MAP (phi_cell_value T) cells_end)` by gvs[] >>
  drule_all (REWRITE_RULE [arithmeticTheory.ADD1]
    fnPlanLineagePhiScheduleTheory.analyzed_native_phi_schedule_observer_support) >> simp[]
QED

Theorem native_join_phi_input_extinction:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ lookup_block pred fn.fn_blocks = SOME pb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\ collect_phis bb.bb_instructions <> [] /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,after) /\
  incoming.ps_stack = after.ps_stack /\
  fnPlanLineageEntryProduction$native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn)
    fn lbl halt 0 len bb.bb_instructions incoming (LENGTH (collect_phis bb.bb_instructions)) endpoint /\
  MEM v (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) /\
  (!inst. MEM inst (collect_phis bb.bb_instructions) ==> ~MEM v inst.inst_outputs) /\
  ~MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH (collect_phis bb.bb_instructions))) /\
  LIST_ELEM_COUNT (Var v) incoming.ps_stack +
    (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1 ==>
  ~MEM (Var v) endpoint.ps_stack /\ Var v NOTIN FDOM endpoint.ps_spilled
Proof
  strip_tac >>
  `~NULL (collect_phis bb.bb_instructions)` by simp[NULL_EQ] >>
  drule_all fnPlanLineageJoinEntryTheory.successful_join_edges_native_cells >> strip_tac >>
  `!w i. MEM w (live_vars_at (liveness_analyze fn) lbl 0) /\
    FLOOKUP (FST (build_phi_maps pred (collect_phis bb.bb_instructions))) w = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps pred (collect_phis bb.bb_instructions))) i) /\
    IS_SOME (FLOOKUP (SND (build_phi_maps pred (collect_phis bb.bb_instructions))) i)` by metis_tac[] >>
  drule_all fnPlanLineagePhiScheduleTheory.analyzed_native_slot_schedule_extinction >>
  disch_then (qspecl_then [`prefixQ`, `prefixP`, `halt`] strip_assume_tac) >>
  `incoming.ps_stack = prefixP ++ MAP (phi_cell_value T) cells` by metis_tac[] >>
  drule_all (REWRITE_RULE [GSYM arithmeticTheory.ADD1] native_phi_schedule_endpoint) >>
  strip_tac >>
  `~MEM (Var v) (MAP (phi_cell_value T) cells_end)` by metis_tac[] >>
  `MEM (Var v) (MAP (phi_cell_value T) cells)` by
    (asm_rewrite_tac[] >> simp[MEM_MAP]) >>
  `LIST_ELEM_COUNT (Var v) (MAP (phi_cell_value T) cells) > 0` by
    metis_tac[rich_listTheory.LIST_ELEM_COUNT_MEM] >>
  `LIST_ELEM_COUNT (Var v) prefixP = 0 /\ Var v NOTIN FDOM incoming.ps_spilled` by
    (qpat_x_assum `LIST_ELEM_COUNT _ _ + _ <= 1` mp_tac >>
     qpat_x_assum `LIST_ELEM_COUNT _ _ > 0` mp_tac >>
     asm_rewrite_tac[] >> simp[rich_listTheory.LIST_ELEM_COUNT_THM] >>
     Cases_on `Var v IN FDOM incoming.ps_spilled` >> simp[] >> decide_tac) >>
  `~MEM (Var v) prefixP` by
    (qpat_x_assum `LIST_ELEM_COUNT _ prefixP = 0` mp_tac >>
     simp[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >>
  simp[MEM_APPEND]
QED

Theorem native_incoming_phi_body_stack_support:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  cfg_reachable_of (cfg_analyze fn) pred /\ fn_reachable fn lbl /\ lbl <> entry /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block pred fn.fn_blocks = SOME pb /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,after) /\
  incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled /\
  (MEM (Var v) after.ps_stack ==>
    MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))) /\
  LIST_ELEM_COUNT (Var v) after.ps_stack +
    (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1 /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming
   else ([],incoming)) = (setup_ops,start) /\
  fnPlanLineageEntryProduction$native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn)
    fn lbl (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions start
      (LENGTH (collect_phis bb.bb_instructions)) endpoint /\
  EVERY (\inst. ~MEM v inst.inst_outputs) (collect_phis bb.bb_instructions) ==>
  MEM (Var v) endpoint.ps_stack ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `LIST_ELEM_COUNT (Var v) incoming.ps_stack <= 1` by
    (Cases_on `Var v IN FDOM after.ps_spilled` >> gvs[] >> decide_tac) >>
  `MEM (Var v) incoming.ps_stack ==>
    MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by metis_tac[] >>
  `MEM (Var v) start.ps_stack ==> MEM v
    (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0))` by
    metis_tac[analyzed_edge_setup_stack_support] >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1`
  >- (`NULL (collect_phis bb.bb_instructions)` by
        (gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
         first_x_assum (qspec_then `bb` mp_tac) >> simp[]) >>
      gvs[NULL_EQ, fnPlanLineageEntryProductionTheory.native_inst_prefix_zero,
        livenessDefsTheory.input_vars_from_def]) >>
  gvs[] >>
  Cases_on `collect_phis bb.bb_instructions = []`
  >- gvs[fnPlanLineageEntryProductionTheory.native_inst_prefix_zero,
       livenessDefsTheory.input_vars_from_def] >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  spose_not_then strip_assume_tac >>
  Cases_on `MEM (Var v) incoming.ps_stack`
  >- (`MEM v (input_vars_from pred bb.bb_instructions
         (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by metis_tac[] >>
      `LIST_ELEM_COUNT (Var v) incoming.ps_stack +
        (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1` by simp[] >>
      fs[EVERY_MEM] >> drule_all native_join_phi_input_extinction >> simp[]) >>
  `!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    (EL i bb.bb_instructions).inst_outputs <> [] /\
    ~MEM v (EL i bb.bb_instructions).inst_outputs` by
    suspend "phi_shape" >>
  drule native_phi_interval_stack_absent >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Resume native_incoming_phi_body_stack_support[phi_shape]:
  qspec_then `bb.bb_instructions` (qx_choose_then `tail` assume_tac)
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  rpt gen_tac >> strip_tac >>
  `EL i bb.bb_instructions = EL i (collect_phis bb.bb_instructions)` by
    (qpat_assum `bb.bb_instructions = _ ++ _`
      (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     simp[EL_APPEND1]) >>
  `MEM (EL i (collect_phis bb.bb_instructions)) (collect_phis bb.bb_instructions)` by
    simp[EL_MEM] >>
  `(EL i bb.bb_instructions).inst_opcode = PHI /\
   MEM (EL i bb.bb_instructions) bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `inst_wf (EL i bb.bb_instructions)` by
    metis_tac[fnPlanLineageQuarantineTheory.ready_member_instruction_shape] >>
  fs[EVERY_MEM] >>
  gvs[venomWfTheory.inst_wf_def] >> Cases_on `(EL i bb.bb_instructions).inst_outputs` >> gvs[]
QED

Finalise native_incoming_phi_body_stack_support

Theorem native_phi_fresh_output_demand_support:
  !inst nl halting ps ops qs v.
    v = HD inst.inst_outputs /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    generate_phi_plan inst nl halting ps = (ops,qs) /\ ~halting ==>
    (MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==> MEM v nl
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM v nl` >- simp[] >>
  `~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled` suffices_by simp[] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- gvs[generate_phi_plan_def] >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`nl`,`T`] mp_tac) >>
  namedCases_on `fnPlanLineagePhiTemporal$phi_write_phase inst nl d ps` ["writes ws"] >>
  simp[] >> strip_tac >>
  `LIST_ELEM_COUNT (Var v) ws.ps_stack +
    (if Var v IN FDOM ws.ps_spilled then 1 else 0) <= 1` by
    (qpat_assum `generate_phi_plan _ _ T _ = _`
       (mp_then Any mp_tac generate_phi_plan_resource_bound) >>
     disch_then (qspec_then `v` mp_tac) >>
     gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`nl`,`halting`] mp_tac) >> simp[] >>
  namedCases_on `popmany_plan [Var v] ws` ["pops final"] >>
  strip_tac >>
  `LIST_ELEM_COUNT (Var v) ws.ps_stack <= 1` by
    (Cases_on `Var v IN FDOM ws.ps_spilled` >> gvs[] >> decide_tac) >>
  `~MEM (Var v) final.ps_stack` by
    (irule fnPlanLineageInventoryTheory.popmany_plan_unique_absent >>
     qexistsl [`[Var v]`,`pops`,`ws`] >> simp[]) >>
  `ws.ps_spilled = ps.ps_spilled` by
    (qpat_x_assum `phi_write_phase _ _ _ _ = _` mp_tac >>
     simp[fnPlanLineagePhiTemporalTheory.phi_write_phase_def] >> IF_CASES_TAC
     >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
         drule deepResidualBudgetTheory.do_dup_spilled_eq >> simp[]) >>
     strip_tac >> gvs[]) >>
  mp_tac (Q.SPECL [`[Var v]`,`ws`]
    fnPlanLineageInventoryTheory.popmany_plan_spilled_unchanged) >> gvs[]
QED

(* Deadness at every executed PHI boundary suffices; in the defining case
   use fresh-output support, and otherwise the resource noncreation bound. *)
Theorem native_phi_prefix_dead_absent[local]:
  !lv dfg cfg fn lbl halt n len xs ps k qs.
    fnPlanLineageEntryProduction$native_inst_prefix
      lv dfg cfg fn lbl halt n len xs ps k qs ==>
    !v. k < LENGTH xs /\ ~halt /\ ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
      (!i. i < k ==> (EL i xs).inst_opcode = PHI /\
        ~MEM v (live_vars_at lv lbl (n + SUC i))) ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_ind >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `k < LENGTH xs` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k xs` by metis_tac[HD_DROP, HD] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ mid = SOME (ops,final)` >>
  `~MEM (Var v) mid.ps_stack /\ Var v NOTIN FDOM mid.ps_spilled` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     `i < SUC k` by decide_tac >> metis_tac[]) >>
  qpat_x_assum `!i. i < SUC k ==> _` (qspec_then `k` mp_tac) >>
  simp[] >> strip_tac >>
  `rest <> []` by
    (strip_tac >> gvs[] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def,
      arithmeticTheory.ADD_CLAUSES, GSYM arithmeticTheory.ADD_ASSOC] >>
  Cases_on `v = HD (EL k xs).inst_outputs`
  >- (drule_at (Pat `generate_phi_plan _ _ _ _ = _`)
        native_phi_fresh_output_demand_support >>
      gvs[arithmeticTheory.ADD1]) >>
  drule generate_phi_plan_resource_bound >>
  disch_then (qspec_then `v` mp_tac) >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var v IN FDOM final.ps_spilled` >> simp[] >> decide_tac
QED

Theorem native_defined_phi_body_demand_support:
  codegen_ready_fn fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ ~halt /\
  MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
  ~MEM (Var v) incoming.ps_stack /\ Var v NOTIN FDOM incoming.ps_spilled /\
  fnPlanLineageEntryProduction$native_inst_prefix (liveness_analyze fn) dfg cfg fn lbl halt 0 len
    bb.bb_instructions incoming (LENGTH (collect_phis bb.bb_instructions)) endpoint ==>
  (MEM (Var v) endpoint.ps_stack \/ Var v IN FDOM endpoint.ps_spilled) ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >>
  `collect_phis bb.bb_instructions <> []` by (strip_tac >> gvs[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb <> HD fn.fn_blocks` by
    (strip_tac >>
     `fn.fn_blocks <> []` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
     drule_all fnPlanLineageEntryProductionTheory.ready_entry_static_boundary >>
     gvs[]) >>
  drule_all fnPlanLineagePhiScheduleTheory.ready_phi_block_suffix >> strip_tac >>
  `!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    ~MEM v (inst_uses (EL i bb.bb_instructions))` by
    suspend "no_reads" >>
  Cases_on `MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions)))` >- simp[] >>
  `!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    ~MEM v (live_vars_at (liveness_analyze fn) lbl (0 + SUC i))` by
    suspend "dead_boundaries" >>
  drule native_phi_prefix_dead_absent >>
  disch_then (qspec_then `v` mp_tac) >>
  simp[] >>
  `LENGTH (collect_phis bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _ ++ _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     Cases_on `rest` >> gvs[]) >>
  simp[]
QED

Resume native_defined_phi_body_demand_support[no_reads]:
  rpt gen_tac >> disch_tac >>
  `EL i bb.bb_instructions = EL i (collect_phis bb.bb_instructions)` by
    (qpat_assum `bb.bb_instructions = _ ++ _`
      (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     simp[EL_APPEND1]) >>
  `MEM (EL i (collect_phis bb.bb_instructions)) (collect_phis bb.bb_instructions)` by
    simp[EL_MEM] >>
  conj_tac >- metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `?outphi. MEM outphi (collect_phis bb.bb_instructions) /\ MEM v outphi.inst_outputs` by
    (gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `~MEM (Var v) (EL i (collect_phis bb.bb_instructions)).inst_operands` by
    metis_tac[fnPlanLineagePhiInputExclusionTheory.phi_prefix_output_not_operand] >>
  gvs[venomInstTheory.inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]
QED

Resume native_defined_phi_body_demand_support[dead_boundaries]:
  rpt gen_tac >> disch_tac >> conj_tac >- metis_tac[] >>
  irule fnPlanLineageLivenessTheory.analyzed_dead_before_use_free_interval >>
  conj_tac >- gvs[codegen_ready_fn_def] >> simp[] >>
  qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >>
  simp[] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _ ++ _`
      (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  simp[]
QED

Finalise native_defined_phi_body_demand_support

Theorem native_indexed_step_fresh_output_demand_support:
  !fn bb dfg k before inst rest ops after v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    DROP k (non_param_insts bb) = inst::rest /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\ inst.inst_opcode <> OFFSET /\
    ~bb_is_halting bb /\ MEM v inst.inst_outputs /\
    ~MEM (Var v) before.ps_stack /\ Var v NOTIN FDOM before.ps_spilled /\
    (!w. MEM (Var w) (compute_operands inst) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1))
      (bb_is_halting bb)
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label before = SOME (ops,after) ==>
    (MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) ==>
    MEM v (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_indexed_step_layout >> strip_tac >>
  `~MEM (Var v) (compute_operands inst)` by metis_tac[] >>
  `inst.inst_opcode <> NOP` by
    (strip_tac >> gvs[venomWfTheory.inst_wf_def]) >>
  `?nl term. generate_regular_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn)
    fn inst nl F term bb.bb_label before = (ops,after) /\
    nl = (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
          (k + LENGTH (get_params bb.bb_instructions) + 1))` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    fnPlanLineageSetupTheory.native_regular_fresh_output_demand_support >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem native_suffix_fresh_step[local]:
  !fn bb dfg p k before inst rest ops after v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    DROP (p+k) (non_param_insts bb) = inst::rest /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\ inst.inst_opcode <> OFFSET /\
    ~bb_is_halting bb /\ MEM v inst.inst_outputs /\
    ~MEM (Var v) before.ps_stack /\ Var v NOTIN FDOM before.ps_spilled /\
    (!w. MEM (Var w) (compute_operands inst) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
        (k+(p+(LENGTH (get_params bb.bb_instructions)+1)))) F
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label before = SOME (ops,after) ==>
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (p+(LENGTH (get_params bb.bb_instructions)+SUC k))))
Proof
  rpt gen_tac >> strip_tac >>
  `p+k < LENGTH (non_param_insts bb)` by
    (qpat_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) +
    (p+k) + SUC (LENGTH rest)` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     qpat_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `k+(p+(LENGTH (get_params bb.bb_instructions)+1)) =
    (p+k)+LENGTH (get_params bb.bb_instructions)+1` by decide_tac >>
  pop_assum (fn th => qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [th])) >>
  qpat_assum `~bb_is_halting bb` (fn th =>
    drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
      (SIMP_RULE (srw_ss()) [th]
        (Q.SPECL [`fn`,`bb`] native_indexed_step_fresh_output_resource_bound))) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `~bb_is_halting bb` (fn th =>
    drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
      (SIMP_RULE (srw_ss()) [th]
        (Q.SPECL [`fn`,`bb`] native_indexed_step_fresh_output_demand_support))) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  `k+(p+(LENGTH (get_params bb.bb_instructions)+1)) =
    (p+k)+LENGTH (get_params bb.bb_instructions)+1` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  Cases_on `rest = []` >> simp[] >>
  `LENGTH (get_params bb.bb_instructions)+(p+k)+1 =
    p+(LENGTH (get_params bb.bb_instructions)+SUC k)` by decide_tac >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM, LENGTH]
QED

Theorem native_suffix_ordinary_step[local]:
  !fn bb dfg p k before inst rest ops after v b.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    DROP (p+k) (non_param_insts bb) = inst::rest /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
    ~is_param_opcode inst.inst_opcode /\ ~MEM v inst.inst_outputs /\
    ~bb_is_halting bb /\ b <= 1 /\
    LIST_ELEM_COUNT (Var v) before.ps_stack +
      (if Var v IN FDOM before.ps_spilled then 1 else 0) <= b /\
    ((MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+p+k))) /\
    (!w. MEM (Var w) (compute_operands inst) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH bb.bb_instructions)
       else live_vars_at (liveness_analyze fn) bb.bb_label
        (k+(p+(LENGTH (get_params bb.bb_instructions)+1)))) F
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      bb.bb_label before = SOME (ops,after) ==>
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= b /\
    ((MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (p+(LENGTH (get_params bb.bb_instructions)+SUC k))))
Proof
  rpt gen_tac >> strip_tac >>
  `k+(p+(LENGTH (get_params bb.bb_instructions)+1)) =
    (p+k)+LENGTH (get_params bb.bb_instructions)+1` by decide_tac >>
  pop_assum (fn th => qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [th])) >>
  `LENGTH (get_params bb.bb_instructions)+p+k =
    LENGTH (get_params bb.bb_instructions)+(p+k)` by decide_tac >>
  pop_assum (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_all native_indexed_step_layout >> strip_tac >>
  `LENGTH (compute_operands inst) <= 16 /\
   ((inst.inst_opcode = PHI \/ inst.inst_opcode = OFFSET) ==> inst.inst_outputs <> [])` by
    (conj_tac >- fs[codegen_ready_inst_def] >>
     strip_tac >> gvs[venomWfTheory.inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `LIST_ELEM_COUNT (Var v) after.ps_stack +
    (if Var v IN FDOM after.ps_spilled then 1 else 0) <= b` by
    (Cases_on `b = 0`
     >- (gvs[elem_count_zero_iff, indicator_zero_iff] >>
         drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
           fnPlanLineageNativeOriginsTheory.native_inst_variable_origins >>
         disch_then (qspec_then `v` mp_tac) >> simp[] >> metis_tac[]) >>
     `b = 1` by decide_tac >> gvs[] >>
     drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
       fnPlanLineageSetupTheory.native_inst_observer_upper >>
     disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  qpat_assum `~bb_is_halting bb` (fn th =>
    drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
      (SIMP_RULE (srw_ss()) [th]
        (Q.SPECL [`fn`,`bb`] native_indexed_ordinary_step_demand_support))) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) +
    (p+k) + SUC (LENGTH rest)` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     qpat_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  Cases_on `rest = []` >> simp[] >>
  `LENGTH (get_params bb.bb_instructions)+(p+k)+1 =
    p+(LENGTH (get_params bb.bb_instructions)+SUC k)` by decide_tac >>
  `LIST_ELEM_COUNT (Var v) before.ps_stack +
    (if Var v IN FDOM before.ps_spilled then 1 else 0) <= 1` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `k+(p+LENGTH (get_params bb.bb_instructions)) =
    LENGTH (get_params bb.bb_instructions)+(p+k)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  `k+(p+(LENGTH (get_params bb.bb_instructions)+1)) =
    p+(LENGTH (get_params bb.bb_instructions)+SUC k)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> metis_tac[]
QED

Theorem native_ordinary_suffix_production[local]:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !bb p v.
    lv = liveness_analyze fn /\ cfg = cfg_analyze fn /\ lbl = bb.bb_label /\
    halt = bb_is_halting bb /\ n = LENGTH (get_params bb.bb_instructions) + p /\
    len = LENGTH bb.bb_instructions /\ xs = DROP p (non_param_insts bb) /\
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~bb_is_halting bb /\ ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
    ~MEM (Var v) incoming.ps_stack /\ Var v NOTIN FDOM incoming.ps_spilled /\
    (!j. j < k ==> (EL j xs).inst_opcode <> PHI /\ (EL j xs).inst_opcode <> JMP /\
      ~is_param_opcode (EL j xs).inst_opcode /\
      (MEM v (EL j xs).inst_outputs ==> (EL j xs).inst_opcode <> OFFSET)) /\
    (!j before w. j < k /\
      fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming j before /\
      MEM (Var w) (compute_operands (EL j xs)) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <=
      (if EXISTS (\i. MEM v i.inst_outputs) (TAKE k xs) then 1 else 0) /\
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at lv lbl (n+k)))
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_strongind >>
  conj_tac >- (rpt strip_tac >> gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ before = SOME (ops,after)` >>
  `LIST_ELEM_COUNT (Var v) before.ps_stack +
    (if Var v IN FDOM before.ps_spilled then 1 else 0) <=
    (if EXISTS (\i. MEM v i.inst_outputs) (TAKE k (DROP p (non_param_insts bb))) then 1 else 0) /\
    ((MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+p+k)))` by
    (simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
     first_x_assum irule >> simp[] >> rpt strip_tac >>
     `j < SUC k` by decide_tac >> metis_tac[]) >>
  `DROP (p+k) (non_param_insts bb) = inst::rest` by
    metis_tac [arithmeticTheory.ADD_COMM, DROP_DROP_T] >>
  `k < LENGTH (DROP p (non_param_insts bb)) /\
   inst = EL k (DROP p (non_param_insts bb))` by
    (conj_asm1_tac
     >- (qpat_assum `DROP k _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
         simp[] >> decide_tac) >> metis_tac[HD_DROP, HD]) >>
  `inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
    ~is_param_opcode inst.inst_opcode /\ (MEM v inst.inst_outputs ==> inst.inst_opcode <> OFFSET)` by
    (qpat_x_assum `!j. j < SUC k ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  `!w. MEM (Var w) (compute_operands inst) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by
    (rpt strip_tac >> qpat_x_assum `!j before w. _`
      (qspecl_then [`k`,`before`,`w`] mp_tac) >> simp[] >> metis_tac[]) >>
  `TAKE (SUC k) (DROP p (non_param_insts bb)) =
    TAKE k (DROP p (non_param_insts bb)) ++ [inst]` by simp[TAKE_SUC_BY_TAKE] >>
  qpat_x_assum `!bb' p' v'. _` kall_tac >>
  Cases_on `MEM v inst.inst_outputs`
  >- suspend "defining" >>
  suspend "nondefining"
QED

Resume native_ordinary_suffix_production[defining]:
  `~EXISTS (\i. MEM v i.inst_outputs) (TAKE k (DROP p (non_param_insts bb)))` by
    metis_tac[distinct_flat_map_prefix_exclusion] >>
  `~MEM (Var v) before.ps_stack /\ Var v NOTIN FDOM before.ps_spilled` by
    (gvs[GSYM LIST_ELEM_COUNT_MEM] >>
     Cases_on `Var v IN FDOM before.ps_spilled` >> gvs[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_suffix_fresh_step >>
  disch_then (qspec_then `v` mp_tac) >> simp[EXISTS_APPEND] >>
  `SUC k + (p + LENGTH (get_params bb.bb_instructions)) =
    p + (LENGTH (get_params bb.bb_instructions) + SUC k)` by decide_tac >>
  metis_tac[]
QED

Resume native_ordinary_suffix_production[nondefining]:
  qpat_x_assum `!bb' p' v'. _` kall_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_suffix_ordinary_step >>
  disch_then (qspecl_then [`v`,
    `if EXISTS (\i. MEM v i.inst_outputs) (TAKE k (DROP p (non_param_insts bb))) then 1 else 0`] mp_tac) >>
  simp[EXISTS_APPEND] >>
  (impl_tac
   >- (conj_tac >- (IF_CASES_TAC >> simp[]) >>
       `k+(p+LENGTH (get_params bb.bb_instructions)) =
         LENGTH (get_params bb.bb_instructions)+p+k` by decide_tac >>
       pop_assum (fn th => pure_rewrite_tac[th]) >> metis_tac[])) >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Finalise native_ordinary_suffix_production

Theorem native_ordinary_suffix_computed_available:
  !fn bb dfg p incoming j before w.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    p+j < LENGTH (non_param_insts bb) /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
      (DROP p (non_param_insts bb)) incoming j before /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
       (LENGTH (get_params bb.bb_instructions)+p)) ==>
       MEM (Var v) incoming.ps_stack \/ Var v IN FDOM incoming.ps_spilled) /\
    (!i. i < j ==> (EL i (DROP p (non_param_insts bb))).inst_opcode <> JMP /\
      (EL i (DROP p (non_param_insts bb))).inst_opcode <> PHI) /\
    MEM (Var w) (compute_operands (EL j (DROP p (non_param_insts bb)))) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `EL j (DROP p (non_param_insts bb)) =
    EL (LENGTH (get_params bb.bb_instructions)+p+j) bb.bb_instructions` by
    (drule_all fnPlanLineageCallersTheory.ready_block_suffix_index >>
     gvs[listTheory.EL_DROP, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  `!u. MEM u (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+p+j)) ==>
    MEM (Var u) before.ps_stack \/ Var u IN FDOM before.ps_spilled` by
    (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ j before`)
       fnPlanLineageEntryProductionTheory.native_ordinary_interval_available >>
     disch_then (qspecl_then [`bb`,`p`] mp_tac) >> simp[] >>
     gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  drule fnPlanLineageEntryProductionTheory.analyzed_live_coverage_computed_operands >>
  disch_then (qspecl_then [`bb`,`LENGTH (get_params bb.bb_instructions)+p+j`,`before`] mp_tac) >>
  disch_then (qspec_then `w` mp_tac) >>
  (impl_tac >- (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
    disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
    gvs[] >> decide_tac)) >> gvs[]
QED

Theorem native_defined_ordinary_suffix_demand_support:
  !fn bb dfg p incoming k qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~bb_is_halting bb /\
    ~MEM (Var v) incoming.ps_stack /\ Var v NOTIN FDOM incoming.ps_spilled /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
      (DROP p (non_param_insts bb)) incoming k qs /\
    (!j. j < k ==> (EL j (DROP p (non_param_insts bb))).inst_opcode <> PHI /\
      (EL j (DROP p (non_param_insts bb))).inst_opcode <> JMP /\
      ~is_param_opcode (EL j (DROP p (non_param_insts bb))).inst_opcode /\
      (MEM v (EL j (DROP p (non_param_insts bb))).inst_outputs ==>
        (EL j (DROP p (non_param_insts bb))).inst_opcode <> OFFSET)) /\
    (!j before w. j < k /\
      fnPlanLineageEntryProduction$native_inst_prefix
        (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
        (DROP p (non_param_insts bb)) incoming j before /\
      MEM (Var w) (compute_operands (EL j (DROP p (non_param_insts bb)))) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) ==>
    (MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+p+k))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    (irule fnPlanLineageCallersTheory.ssa_form_block_outputs_distinct >>
     qexists_tac `fn` >> gvs[codegen_ready_fn_def]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (non_param_insts bb)))` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (fn th => qpat_x_assum `ALL_DISTINCT _` (mp_tac o ONCE_REWRITE_RULE [th])) >>
     simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (DROP p (non_param_insts bb))))` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
     qspec_then `p` (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV)
       empty_rewrites [GSYM th]) TAKE_DROP >>
     simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  drule native_ordinary_suffix_production >>
  disch_then (qspecl_then [`bb`,`p`,`v`] mp_tac) >> simp[] >>
  (impl_tac
   >- (rpt strip_tac >>
       qpat_x_assum `!j before w. _` (qspecl_then [`j`,`before`,`w`] mp_tac) >>
       simp[])) >> metis_tac[]
QED

Theorem native_supported_ordinary_suffix_joint[local]:
  !lv dfg cfg fn lbl halt n len xs incoming k qs.
    fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming k qs ==>
    !bb p v.
    lv = liveness_analyze fn /\ cfg = cfg_analyze fn /\ lbl = bb.bb_label /\
    halt = bb_is_halting bb /\ n = LENGTH (get_params bb.bb_instructions)+p /\
    len = LENGTH bb.bb_instructions /\ xs = DROP p (non_param_insts bb) /\
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~bb_is_halting bb /\
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
      (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) incoming.ps_stack \/ Var v IN FDOM incoming.ps_spilled) ==>
      MEM v (live_vars_at lv lbl n)) /\
    (!j. j < k ==> (EL j xs).inst_opcode <> PHI /\ (EL j xs).inst_opcode <> JMP /\
      ~is_param_opcode (EL j xs).inst_opcode /\ ~MEM v (EL j xs).inst_outputs) /\
    (!j before w. j < k /\
      fnPlanLineageEntryProduction$native_inst_prefix lv dfg cfg fn lbl halt n len xs incoming j before /\
      MEM (Var w) (compute_operands (EL j xs)) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at lv lbl (n+k)))
Proof
  ho_match_mp_tac fnPlanLineageEntryProductionTheory.native_inst_prefix_strongind >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ before = SOME (ops,after)` >>
  `LIST_ELEM_COUNT (Var v) before.ps_stack +
    (if Var v IN FDOM before.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+p+k)))` by
    (simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
     first_x_assum irule >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
     reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
     `j < SUC k` by decide_tac >> metis_tac[]) >>
  qpat_x_assum `!bb' p' v'. (bb.bb_label = bb'.bb_label /\ _) ==> _` kall_tac >>
  `DROP (p+k) (non_param_insts bb) = inst::rest` by
    metis_tac[arithmeticTheory.ADD_COMM, DROP_DROP_T] >>
  `k < LENGTH (DROP p (non_param_insts bb)) /\
   inst = EL k (DROP p (non_param_insts bb))` by
    (conj_asm1_tac
     >- (qpat_assum `DROP k _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
         simp[] >> decide_tac) >> metis_tac[HD_DROP, HD]) >>
  `inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
    ~is_param_opcode inst.inst_opcode /\ ~MEM v inst.inst_outputs` by
    (qpat_x_assum `!j. j < SUC k ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  `!w. MEM (Var w) (compute_operands inst) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by
    (rpt strip_tac >> qpat_x_assum `!j before w. _`
      (qspecl_then [`k`,`before`,`w`] mp_tac) >> simp[] >> metis_tac[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_suffix_ordinary_step >>
  disch_then (qspecl_then [`v`,`1`] mp_tac) >> simp[] >>
  `k+(p+LENGTH (get_params bb.bb_instructions)) =
    LENGTH (get_params bb.bb_instructions)+p+k` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  `SUC k+(p+LENGTH (get_params bb.bb_instructions)) =
    p+(LENGTH (get_params bb.bb_instructions)+SUC k)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> metis_tac[]
QED

Theorem native_supported_ordinary_suffix_demand_support:
  !fn bb dfg p incoming k qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~bb_is_halting bb /\
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
      (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) incoming.ps_stack \/ Var v IN FDOM incoming.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+p))) /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
      (DROP p (non_param_insts bb)) incoming k qs /\
    (!j. j < k ==> (EL j (DROP p (non_param_insts bb))).inst_opcode <> PHI /\
      (EL j (DROP p (non_param_insts bb))).inst_opcode <> JMP /\
      ~is_param_opcode (EL j (DROP p (non_param_insts bb))).inst_opcode /\
      ~MEM v (EL j (DROP p (non_param_insts bb))).inst_outputs) /\
    (!j before w. j < k /\
      fnPlanLineageEntryProduction$native_inst_prefix
        (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
        (DROP p (non_param_insts bb)) incoming j before /\
      MEM (Var w) (compute_operands (EL j (DROP p (non_param_insts bb)))) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) ==>
    (MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+p+k))
Proof
  rpt gen_tac >> strip_tac >>
  drule native_supported_ordinary_suffix_joint >>
  disch_then (qspecl_then [`bb`,`p`,`v`] mp_tac) >> simp[] >>
  (impl_tac
   >- (conj_tac
       >- (`p+LENGTH (get_params bb.bb_instructions) =
             LENGTH (get_params bb.bb_instructions)+p` by decide_tac >>
           pop_assum (fn th => pure_rewrite_tac[th]) >> metis_tac[]) >>
       rpt strip_tac >>
       qpat_x_assum `!j before w. _` (qspecl_then [`j`,`before`,`w`] mp_tac) >> simp[])) >>
  metis_tac[]
QED

Theorem native_supported_ordinary_suffix_resource_bound:
  !fn bb dfg p incoming k qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~bb_is_halting bb /\
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
      (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) incoming.ps_stack \/ Var v IN FDOM incoming.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+p))) /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
      (DROP p (non_param_insts bb)) incoming k qs /\
    (!j. j < k ==> (EL j (DROP p (non_param_insts bb))).inst_opcode <> PHI /\
      (EL j (DROP p (non_param_insts bb))).inst_opcode <> JMP /\
      ~is_param_opcode (EL j (DROP p (non_param_insts bb))).inst_opcode /\
      ~MEM v (EL j (DROP p (non_param_insts bb))).inst_outputs) /\
    (!j before w. j < k /\
      fnPlanLineageEntryProduction$native_inst_prefix
        (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
        (DROP p (non_param_insts bb)) incoming j before /\
      MEM (Var w) (compute_operands (EL j (DROP p (non_param_insts bb)))) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  drule native_supported_ordinary_suffix_joint >>
  disch_then (qspecl_then [`bb`,`p`,`v`] mp_tac) >> simp[] >>
  (impl_tac
   >- (conj_tac
       >- (`p+LENGTH (get_params bb.bb_instructions) =
             LENGTH (get_params bb.bb_instructions)+p` by decide_tac >>
           pop_assum (fn th => pure_rewrite_tac[th]) >> metis_tac[]) >>
       rpt strip_tac >>
       qpat_x_assum `!j before w. _` (qspecl_then [`j`,`before`,`w`] mp_tac) >> simp[])) >>
  metis_tac[]
QED

Theorem ready_block_terminal_factor:
  !fn bb lv dfg cfg ps ops after.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (bb = HD fn.fn_blocks ==> LENGTH (cfg_preds_of cfg bb.bb_label) <> 1) /\
    generate_block_plan lv dfg cfg fn bb ps = SOME (ops,after) ==>
    ?setup_ops start before chunk.
      (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps
       else if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
         clean_stack_plan lv cfg fn bb ps else ([],ps)) = (setup_ops,start) /\
      LENGTH (collect_phis bb.bb_instructions) <= PRE (LENGTH (non_param_insts bb)) /\
      PRE (LENGTH (non_param_insts bb)) < LENGTH (non_param_insts bb) /\
      LENGTH (get_params bb.bb_instructions) + PRE (LENGTH (non_param_insts bb)) =
        PRE (LENGTH bb.bb_instructions) /\
      native_inst_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (non_param_insts bb) start (PRE (LENGTH (non_param_insts bb))) before /\
      generate_inst_plan lv dfg cfg fn (LAST bb.bb_instructions)
        (live_vars_at lv bb.bb_label (LENGTH bb.bb_instructions))
        (bb_is_halting bb) F bb.bb_label before = SOME (chunk,after)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (LAST bb.bb_instructions) (non_param_insts bb)` by
    (simp[non_param_insts_def, MEM_FILTER, LAST_MEM] >>
     qpat_x_assum `is_terminator _` mp_tac >>
     Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     simp[venomInstTheory.is_terminator_def, venomInstTheory.is_param_opcode_def]) >>
  `non_param_insts bb <> []` by metis_tac[MEM] >>
  `bb.bb_instructions = get_params bb.bb_instructions ++ non_param_insts bb` by
    metis_tac[fnPlanLineageCallersTheory.ready_block_parameter_suffix] >>
  `LAST bb.bb_instructions = LAST (non_param_insts bb)` by
    (qpat_assum `bb.bb_instructions = _ ++ _`
       (fn th => once_rewrite_tac[th]) >> simp[rich_listTheory.LAST_APPEND_NOT_NIL]) >>
  `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) +
     LENGTH (non_param_insts bb)` by metis_tac[LENGTH_APPEND] >>
  `LENGTH (collect_phis bb.bb_instructions) <= PRE (LENGTH (non_param_insts bb))` by
    suspend "phi_bound" >>
  `?setup_ops start worker_ops.
     (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps
      else if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
        clean_stack_plan lv cfg fn bb ps else ([],ps)) = (setup_ops,start) /\
     generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
       (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
       0 (non_param_insts bb) start = SOME (worker_ops,after)` by
    suspend "setup_worker" >>
  `?before chunk.
     native_inst_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb)
       (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
       (non_param_insts bb) start (PRE (LENGTH (non_param_insts bb))) before /\
     generate_inst_plan lv dfg cfg fn (LAST (non_param_insts bb))
       (live_vars_at lv bb.bb_label (LENGTH bb.bb_instructions))
       (bb_is_halting bb) F bb.bb_label before = SOME (chunk,after)` by
    (irule fnPlanLineageEntryProductionTheory.native_worker_terminal_prefix >>
     goal_assum (drule_at Any) >>
     simp[fnPlanLineageEntryProductionTheory.native_inst_prefix_zero]) >>
  qexistsl_tac [`setup_ops`,`start`,`before`,`chunk`] >> gvs[] >>
  Cases_on `non_param_insts bb` >> gvs[]
QED

Resume ready_block_terminal_factor[phi_bound]:
  mp_tac (Q.SPEC `bb` fnPlanLineageEntryProductionTheory.non_param_insts_phi_prefix) >>
  strip_tac >>
  `tail <> []` by
    (strip_tac >> gvs[] >>
     `MEM (LAST bb.bb_instructions) (collect_phis bb.bb_instructions)` by metis_tac[] >>
     drule livenessProofsTheory.collect_phis_mem >>
     strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  qpat_x_assum `non_param_insts bb = _ ++ _`
    (fn th => once_rewrite_tac[th]) >> simp[] >>
  Cases_on `tail` >> gvs[]
QED

Resume ready_block_terminal_factor[setup_worker]:
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `bb = HD fn.fn_blocks`
  >- (simp[generate_block_plan_def] >> pairarg_tac >> simp[AllCaseEqs()] >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >>
  simp[generate_block_plan_def]
  >- (pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >>
      gvs[] >> metis_tac[]) >>
  simp[AllCaseEqs()] >> strip_tac >> metis_tac[]
QED
Finalise ready_block_terminal_factor

Theorem analyzed_supported_join_phi_output_absent:
  !fn pred pb bb v dfg ps ops after.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps =
      SOME (ops,after) /\
    (MEM (Var v) after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack <= 1 ==>
    ~MEM (Var v) after.ps_stack /\ Var v NOTIN FDOM after.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `after.ps_spilled = FEMPTY` by
    metis_tac[fnPlanLineageEdgeTheory.analyzed_join_edge_spilled_empty] >>
  reverse conj_tac >- simp[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    metis_tac[fnPlanLineageLivenessTheory.analyzed_successor_reachable] >>
  `fn_reachable fn bb.bb_label` by
    metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `fn.fn_blocks <> []` by metis_tac[listTheory.MEM] >>
  drule_all fnPlanLineageEntryProductionTheory.ready_entry_static_boundary >> strip_tac >>
  `bb <> HD fn.fn_blocks` by (strip_tac >> gvs[]) >>
  `fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label` by
    gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def, listTheory.NULL_EQ] >>
  `bb.bb_label <> (HD fn.fn_blocks).bb_label` by
    (strip_tac >> gvs[]) >>
  `?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `LIST_ELEM_COUNT (Var v) (MAP Var (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0))) = 0` by
    metis_tac[fnPlanLineagePhiSuffixResourcesTheory.ready_phi_output_initial_target_count] >>
  `~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    (qpat_x_assum `LIST_ELEM_COUNT _ (MAP _ _) = 0` mp_tac >>
     simp[LIST_ELEM_COUNT_DEF, FILTER_EQ_NIL, EVERY_MEM, MEM_MAP]) >>
  drule_at (Pat `MEM (Var _) _.ps_stack ==> _`) analyzed_edge_setup_stack_support >>
  simp[] >> disch_then (qspecl_then [`bb`, `[]`, `after`] mp_tac) >> simp[]
QED

(* Stack support does not require spill-debt support at the seed.  If the
   observer is dead there, its absent stack occurrence cannot resurrect. *)
Theorem native_stack_supported_ordinary_suffix:
  !fn bb dfg p incoming k qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    ~bb_is_halting bb /\
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
      (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1 /\
    (MEM (Var v) incoming.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+p))) /\
    fnPlanLineageEntryProduction$native_inst_prefix
      (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
      (DROP p (non_param_insts bb)) incoming k qs /\
    (!j. j < k ==> (EL j (DROP p (non_param_insts bb))).inst_opcode <> PHI /\
      (EL j (DROP p (non_param_insts bb))).inst_opcode <> JMP /\
      ~is_param_opcode (EL j (DROP p (non_param_insts bb))).inst_opcode /\
      ~MEM v (EL j (DROP p (non_param_insts bb))).inst_outputs) /\
    (!j before w. j < k /\
      fnPlanLineageEntryProduction$native_inst_prefix
        (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)+p) (LENGTH bb.bb_instructions)
        (DROP p (non_param_insts bb)) incoming j before /\
      MEM (Var w) (compute_operands (EL j (DROP p (non_param_insts bb)))) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) ==>
    MEM (Var v) qs.ps_stack ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+p+k))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (get_params bb.bb_instructions)+p))`
  >- (strip_tac >> irule native_supported_ordinary_suffix_demand_support >>
      simp[] >> qexistsl_tac [`dfg`,`incoming`,`qs`] >>
      gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      metis_tac[]) >>
  `~MEM (Var v) incoming.ps_stack` by metis_tac[] >>
  drule native_ordinary_interval_dead_stack >>
  disch_then (qspecl_then [`bb`,`p`,`v`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> metis_tac[])) >> simp[]
QED

(* A terminal JMP cannot resurrect dead spill debt: targets are live-out and
   the regular release removes all unsupported spill entries. *)
Theorem native_terminal_jmp_demand_support:
  !fn bb dfg ps ops qs v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (LAST bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
      (bb_is_halting bb) F bb.bb_label ps = SOME (ops,qs) /\
    (MEM (Var v) ps.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (PRE (LENGTH bb.bb_instructions)))) ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH bb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions))` >- simp[] >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, EVERY_MEM] >>
     metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ]` by
    gvs[venomWfTheory.inst_wf_def] >>
  `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions /\
    PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[LAST_EL] >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (PRE (LENGTH bb.bb_instructions)))` by
    (strip_tac >> drule_at (Pat `MEM _ (live_vars_at _ _ _)`)
       analyzed_live_loss_compute_operand >>
     simp[compute_operands_def, asmIRTheory.get_non_label_operands_def,
       stackPlanTypesTheory.is_label_operand_def]) >>
  `~MEM (Var v) ps.ps_stack` by metis_tac[] >>
  `~MEM v (LAST bb.bb_instructions).inst_outputs` by
    gvs[venomWfTheory.inst_wf_def] >>
  qspecl_then [`fn`,`bb`,`PRE (LENGTH bb.bb_instructions)`] mp_tac
    native_ordinary_dead_stack_release >>
  simp[venomInstTheory.is_param_opcode_def] >>
  disch_then drule >> simp[] >> metis_tac[]
QED

(* Stack-only support suffices at a regular release, even with spill debt. *)
Theorem native_indexed_regular_stack_support:
  !fn bb i inst dfg ps ops qs v halt term.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> OFFSET /\
    ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> NOP /\ inst.inst_opcode <> JMP /\
    ~MEM v inst.inst_outputs /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 /\
    (!w. MEM (Var w) (compute_operands inst) ==>
      MEM (Var w) ps.ps_stack \/ Var w IN FDOM ps.ps_spilled) /\
    (MEM (Var v) ps.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halt term bb.bb_label ps =
      SOME (ops,qs) ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))`
  >- simp[] >>
  `~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled` suffices_by metis_tac[] >>
  Cases_on `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)`
  >- (`MEM (Var v) (compute_operands inst)` by
        metis_tac[analyzed_live_loss_compute_operand] >>
      `inst_wf inst /\ codegen_ready_inst inst` by
        (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, EVERY_MEM] >>
         metis_tac[EL_MEM]) >>
      drule_all fnPlanLineageSetupTheory.native_inst_last_use_extinction >> simp[]) >>
  `~MEM (Var v) ps.ps_stack` by metis_tac[] >>
  drule_all native_ordinary_dead_stack_release >> simp[]
QED

Theorem ready_edge_source_nonhalting:
  !fn bb succ.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM succ (cfg_succs_of (cfg_analyze fn) bb.bb_label) ==>
    ~bb_is_halting bb
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
  disch_then (fn th => fs[th]) >>
  strip_tac >>
  gvs[cfgTransformTheory.bb_is_halting_def] >>
  `codegen_ready_inst (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  qpat_x_assum `MEM succ (bb_succs bb)` mp_tac >>
  simp[venomInstTheory.bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `(LAST (h::t)).inst_opcode` >>
  gvs[cfgTransformTheory.is_halting_opcode_def, venomInstTheory.get_successors_def,
    codegen_ready_inst_def, venomInstTheory.is_terminator_def, EVERY_MEM] >>
  `FILTER IS_SOME (MAP get_label (LAST (h::t)).inst_operands) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP] >> metis_tac[optionTheory.NOT_IS_SOME_EQ_NONE]) >>
  simp[]
QED
