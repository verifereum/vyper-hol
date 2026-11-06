Theory fnLineageInvActualReplay
Ancestors fnPlanLineageInventory fnPlanLineageReplay fnPlanLineageSetup planWf
  reorderSim
  fnLineageInvCleanupCoherence stackPlanGen
  stackPlanOps stackPlanTypes stackModel list rich_list

(* Silent spill release is independent of the entire physical stack, not
   merely of its live projection.  All allocator effects are retained. *)
Theorem release_dead_spills_stack_update:
  !nl ps stk.
    release_dead_spills nl (ps with ps_stack := stk) =
    (release_dead_spills nl ps) with ps_stack := stk
Proof
  simp[release_dead_spills_def,
       fnPlanLineageSetupTheory.release_fold_stack_update]
QED

Theorem optimistic_swap_plan_bottom_frame:
  !dfg inst nl term ps prefix ops qs.
    EVERY (\op. ~is_var_operand op) prefix /\
    optimistic_swap_plan dfg inst nl term ps = (ops,qs) ==>
    optimistic_swap_plan dfg inst nl term
      (ps with ps_stack := prefix ++ ps.ps_stack) =
    (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (Var (LAST nl)) prefix` by
    (gvs[EVERY_MEM] >> metis_tac[is_var_operand_def]) >>
  simp[optimistic_swap_plan_def, stack_get_depth_bottom_excluded] >>
  Cases_on `term` >- gvs[optimistic_swap_plan_def] >>
  Cases_on `inst.inst_outputs = []` >- gvs[optimistic_swap_plan_def] >>
  Cases_on `nl = []` >- gvs[optimistic_swap_plan_def] >>
  Cases_on `operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST nl))`
  >- gvs[optimistic_swap_plan_def] >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack`
  >- gvs[optimistic_swap_plan_def] >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  gvs[optimistic_swap_plan_def] >>
  drule_all do_swap_bottom_frame >> simp[]
QED

Theorem restore_spilled_plan_bottom_frame:
  !targets ps prefix ops qs.
    restore_spilled_plan targets ps = (ops,qs) ==>
    restore_spilled_plan targets
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct >- (simp[restore_spilled_plan_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `do_restore h ps` >>
  rename1 `do_restore h ps = (step_ops,ps_mid)` >>
  drule do_restore_bottom_frame >>
  disch_then (qspec_then `prefix` assume_tac) >>
  Cases_on `restore_spilled_plan targets ps_mid` >>
  gvs[restore_spilled_plan_def] >>
  first_x_assum drule >> simp[]
QED

Theorem generate_emit_ops_stack_update:
  !inst tc ps stk.
    generate_emit_ops inst tc (ps with ps_stack := stk) =
    (FST (generate_emit_ops inst tc ps),
     (SND (generate_emit_ops inst tc ps)) with ps_stack := stk)
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = INITIAL_FMP` >- simp[generate_emit_ops_def] >>
  Cases_on `inst.inst_opcode = BUMP` >- simp[generate_emit_ops_def] >>
  simp[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  Cases_on `inst.inst_opcode = DJMP` >- simp[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[] >> Cases_on `HD inst.inst_operands` >>
      simp[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = RET` >- simp[] >>
  Cases_on `inst.inst_opcode = ASSERT` >- simp[] >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- simp[fresh_label_def] >>
  Cases_on `inst.inst_opcode = LOG` >- simp[] >>
  Cases_on `inst.inst_opcode = ISTORE` >> simp[]
QED

Theorem popmany_plan_bottom_frame:
  !requests ps prefix ops qs.
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set prefix) (set requests) /\
    popmany_plan requests ps = (ops,qs) ==>
    popmany_plan requests (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`requests`, `ps`, `ps`, `[]`, `prefix`, `ps.ps_stack`,
              `ps.ps_alloc`] mp_tac popmany_plan_prefix_replay >>
  simp[] >> strip_tac >>
  gvs[plan_state_component_equality]
QED

Theorem distinct_available_pending_inventory:
  !targets ps.
    ALL_DISTINCT targets /\
    EVERY (\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) targets ==>
    pending_inventory_wf targets ps
Proof
  rpt gen_tac >> strip_tac >> simp[pending_inventory_wf_def] >>
  gen_tac >>
  drule all_distinct_elem_count_le_one >>
  disch_then (qspec_then `op` assume_tac) >>
  Cases_on `MEM op targets`
  >- (gvs[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
      gvs[] >>
      `LIST_ELEM_COUNT op ps.ps_stack > 0` by
        metis_tac[LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  `LIST_ELEM_COUNT op targets = 0` by
    (spose_not_then assume_tac >>
     `LIST_ELEM_COUNT op targets > 0` by decide_tac >>
     metis_tac[LIST_ELEM_COUNT_MEM]) >>
  simp[]
QED

Theorem generate_jmp_plan_bottom_frame:
  !lv dfg cfg fn inst nl halting term lbl ps ops qs m.
    inst.inst_opcode = JMP /\ compute_operands inst = [] /\
    inst.inst_outputs = [] /\
    (!targets. join_target_ops lv fn lbl inst = SOME targets ==>
      ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
      EVERY (\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) targets) /\
    generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,qs) ==>
    generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl
      (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
      (ops,qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `join_target_ops lv fn lbl inst`
  >- (gvs[generate_regular_inst_plan_def, emit_input_plan_def,
          reorder_plan_def, generate_emit_ops_def, fresh_label_def,
          asmIRTheory.venom_to_evm_name_def,
          venomEffectsTheory.is_commutative_def, stack_pop_def,
          release_dead_spills_stack_update] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[release_dead_spills_stack_update,
          fnPlanPrefixTheory.release_dead_spills_stack,
          TAKE_APPEND, TAKE_LENGTH_TOO_LONG])) >>
  rename1 `join_target_ops lv fn lbl inst = SOME targets` >>
  `ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
   EVERY (\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) targets` by
    metis_tac[] >>
  `pending_inventory_wf targets ps` by
    (irule distinct_available_pending_inventory >> simp[]) >>
  Cases_on `restore_spilled_plan targets ps` >>
  rename1 `restore_spilled_plan targets ps = (restore_ops,rs)` >>
  `LENGTH targets <= LENGTH rs.ps_stack` by
    metis_tac[restore_spilled_plan_length_floor] >>
  `EVERY (\op. ~MEM op (REPLICATE m dead_stack_marker)) targets` by
    (gvs[EVERY_MEM, MEM_REPLICATE, dead_stack_marker_def] >>
     metis_tac[is_var_operand_def]) >>
  drule restore_spilled_plan_bottom_frame >>
  disch_then (qspec_then `REPLICATE m dead_stack_marker` assume_tac) >>
  Cases_on `reorder_plan dfg targets rs` >>
  rename1 `reorder_plan dfg targets rs = (swap_ops,ts)` >>
  drule_all reorder_plan_bottom_frame >> strip_tac >>
  gvs[generate_regular_inst_plan_def, emit_input_plan_def,
      reorder_plan_def, generate_emit_ops_def, fresh_label_def,
      asmIRTheory.venom_to_evm_name_def,
      venomEffectsTheory.is_commutative_def, stack_pop_def,
      release_dead_spills_stack_update] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[release_dead_spills_stack_update,
          fnPlanPrefixTheory.release_dead_spills_stack,
          TAKE_APPEND, TAKE_LENGTH_TOO_LONG])
QED
