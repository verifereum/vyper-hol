Theory algebraicOptProofs
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner unitShapeDefs
  algebraicOptOffsetProofs algebraicOptMainRunProofs algebraicOptCmpRunProofs
  algebraicOptMainShapeProofs o1PassLift

(* Algebraic optimization, with inserted instructions named from the
   supply, preserves the result of a run from the function's entry, up to
   the variables it takes from the supply, unless the original run fails. *)
Theorem ao_transform_function_correct_proof:
  !fuel ctx fn s sup fn' sup'.
    wf_function fn /\
    wf_ssa fn /\
    fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
       lookup_var x s = NONE) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result
      (state_equiv (set sup'.irs_used_vars DIFF set sup.irs_used_vars))
      (execution_equiv UNIV)
      (execution_equiv UNIV)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)
Proof
  map_every qx_gen_tac [`fuel`, `ctx`, `fn`, `s`, `supply`, `fn'`, `last`] >>
  strip_tac >>
  qpat_x_assum `ao_transform_function_supply _ _ = _` mp_tac >>
  simp[ao_transform_function_supply_def] >>
  qmatch_goalsub_abbrev_tac `dfg_build_function fn0` >>
  `fn0.fn_blocks = MAP (\bb. bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` by simp[Abbr `fn0`] >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  Cases_on `ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
    (ao_compute_fn_iszero_targets fn0) supply fn0.fn_blocks` >>
  rename1 `ao_transform_blocks_supply _ _ _ _ _ = (bbs,supply1)` >>
  rewrite_tac [pairTheory.pair_case_thm] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `ao_cmp_flip_function_supply _ supply1 mid` >>
  `mid = fn0 with fn_blocks := bbs` by simp[Abbr `mid`, Abbr `fn0`] >>
  strip_tac >>
  `wf_function fn0` by (irule ao_offset_function_well_formed >> qexists_tac `fn` >> simp[Abbr `fn0`]) >>
  `wf_ssa fn0` by (irule ao_offset_function_ssa >> qexists_tac `fn` >> simp[Abbr `fn0`]) >>
  `fn_inst_wf fn0` by (irule ao_offset_function_inst_wf >> qexists_tac `fn` >> simp[Abbr `fn0`]) >>
  `EVERY label_positions_ok (fn_insts fn0)` by
    (qspecl_then [`fn`, `fn0`] mp_tac ao_offset_function_label_contract >> simp[Abbr `fn0`]) >>
  `ir_supply_covers_fn supply fn0` by
    (irule ao_offset_function_coverage >> qexists_tac `fn` >> simp[Abbr `fn0`]) >>
  `fn_entry_label fn0 = SOME s.vs_current_bb` by simp[Abbr `fn0`, ao_offset_entry_label] >>
  `!i x. MEM i (fn_insts fn0) /\ MEM x i.inst_outputs ==> lookup_var x s = NONE` by
    (rpt strip_tac >> irule ao_offset_function_initial_absence >>
     qexistsl_tac [`fn`, `fn0`] >> simp[Abbr `fn0`] >> metis_tac[]) >>
  `run_blocks fuel ctx fn0 s = run_blocks fuel ctx fn s` by
    simp[Abbr `fn0`, ao_offset_run_blocks] >>
  drule_all ao_main_transform_blocks_supply_run >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  qpat_assum `mid = fn0 with fn_blocks := bbs`
    (fn th => rewrite_tac[GSYM th]) >>
  strip_tac >- metis_tac[] >>
  qpat_assum `Abbrev (fn0 = _)`
    (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts mid)) /\
   ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts mid)))` by
    (drule_all ao_main_function_distinct >> simp[]) >>
  `ir_supply_inst_ok supply1 /\ ir_supply_covers_fn supply1 mid` by
    (drule_all ao_main_function_coverage >> simp[]) >>
  `EVERY (\out.
    (out.inst_opcode = ISZERO ==> LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    (out.inst_opcode = ASSERT ==> LENGTH out.inst_operands = 1)) (fn_insts mid)` by
    (drule_all ao_main_function_unary >> simp[]) >>
  `!i. MEM i (fn_insts mid) /\ (i.inst_opcode = ISZERO \/ i.inst_opcode = ASSERT) ==>
    LENGTH i.inst_operands = 1` by
    (qpat_x_assum `EVERY (\out. _) (fn_insts mid)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `ao_cmp_flip_scan (dfg_build_function mid) (fn_insts mid)` >>
  PairCases_on `r` >>
  drule_all ao_main_comparator_supply_run >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >> strip_tac
  >- (qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
      qpat_x_assum `run_blocks fuel ctx fn0 s = _` (fn th => rewrite_tac[th]) >>
      qpat_x_assum `run_blocks fuel ctx mid s = Error _` mp_tac >>
      rpt (pop_assum kall_tac) >> strip_tac >>
      Cases_on `run_blocks fuel ctx fn s` >>
      simp[stateEquivTheory.lift_result_def]) >>
  qpat_x_assum `lift_result _ _ _ (run_blocks fuel ctx fn0 s) _` mp_tac >>
  qpat_x_assum `run_blocks fuel ctx fn0 s = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `run_blocks fuel ctx fn s` >>
  gvs[o1PassLiftTheory.run_blocks_not_OK] >>
  Cases_on `run_blocks fuel ctx mid s` >>
  simp[stateEquivTheory.lift_result_def] >>
  Cases_on `run_blocks fuel ctx fn' s` >>
  simp[stateEquivTheory.lift_result_def, stateEquivTheory.execution_equiv_def] >>
  metis_tac[]
QED
