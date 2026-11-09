(*
 * CFG normalization (the supply variant the O1 dispatcher runs) against
 * the O1 pass contract.
 *
 * The pass splits each critical edge p -> t with a fresh block that
 * forwards the PHI values t reads along that edge into fresh variables and
 * jumps to t; t's PHIs then name the split block and the forwarded
 * variables.  A run of the output takes one extra block per split edge
 * and otherwise matches the input's run, so the two correspond with
 * different fuel.  A forwarding ASSIGN reads every PHI value for the edge,
 * duplicates included, where the input's PHI reads only the first; wf_ssa
 * makes each of them defined at the predecessor's end.
 *)
Theory o1ContractCfgNorm
Ancestors
  o1PassLift cfgNormDefs cfgNormSupplyProofs venomFnScheduleRunner venomWf
  venomInst irSupply cfgNormSupplySim contextCodegenRel venomExecSemantics
  venomExecProofs venomStepProps ctxLookupAgreeHelpers o1ContractCfgNormStep
  o1PassContract unitMemInv unitShapeDefs venomRetProps o1ComposeSupport

Theorem supply_active_terminator_exec_block:
  st.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL st.vs_inst_idx bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst st = OK sp /\
  ~sp.vs_halted ==>
  exec_block fuel ctx bb st = OK sp
Proof
  rpt strip_tac >>
  simp[Once exec_block_def, get_instruction_def]
QED

Theorem supply_prefix_terminator_entry:
  wf_function f /\ fn_inst_wf f /\ supply_prefix_defined f st /\
  active_inst f inst st /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK sp /\ ~sp.vs_halted ==>
  supply_entry_defined f sp
Proof
  rpt strip_tac >> gvs[active_inst_def] >>
  `exec_block fuel ctx bb st = OK sp` by
    (irule supply_active_terminator_exec_block >> metis_tac[]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  gvs[supply_prefix_defined_def, supply_entry_defined_def] >>
  reverse conj_tac
  >- (irule strict_dom_vars_defined_preserved_from_prefix >> simp[] >>
      qexistsl [`bb`, `ctx`, `fuel`, `st`] >> simp[] >> metis_tac[]) >>
  `MEM sp.vs_current_bb (bb_succs bb)` by
    (irule exec_block_current_bb_in_succs >> conj_tac
     >- (gvs[bb_well_formed_def] >> rpt strip_tac >>
         `i < LENGTH bb.bb_instructions` by decide_tac >>
         `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >> decide_tac) >>
     `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
     simp[] >> qexistsl [`ctx`, `fuel`, `st`] >> simp[]) >>
  irule fn_reachable_step >> qexists `st.vs_current_bb` >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem supply_prefix_enters_block:
  wf_function f /\ supply_entry_defined f st /\ enters_block f st sp ==>
  supply_prefix_defined f sp
Proof
  rpt strip_tac >> gvs[enters_block_def] >>
  drule lookup_block_MEM >> strip_tac >>
  irule supply_prefix_defined_eval_phis >> metis_tac[lookup_block_label]
QED

Theorem supply_frame_reach_prefix:
  !ctx f s0 inst st. frame_reach ctx f s0 inst st ==>
  active_inst f inst st /\
  (wf_function f /\ fn_inst_wf f /\ fn_entry_state f s0 ==>
   supply_prefix_defined f st)
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
      irule supply_prefix_enters_block >>
      metis_tac[supply_entry_defined_entry, fn_entry_state_def])
  >- (rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
      irule supply_prefix_defined_step >> gvs[active_inst_def] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
  irule supply_prefix_enters_block >>
  metis_tac[supply_prefix_terminator_entry]
QED

Theorem supply_frame_reach_terminator_entry:
  wf_function f /\ fn_inst_wf f /\ fn_entry_state f s0 /\
  frame_reach ctx f s0 inst st /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK sp /\ ~sp.vs_halted ==>
  supply_entry_defined f sp
Proof
  metis_tac[supply_frame_reach_prefix, supply_prefix_terminator_entry]
QED

Theorem supply_frame_reach_forward_sources:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ fn_entry_state f s0 /\
  frame_reach ctx f s0 inst st /\ MEM pred f.fn_blocks /\
  MEM target f.fn_blocks /\ pred.bb_label = st.vs_current_bb /\
  active_inst f inst st /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK sp /\
  MEM v (phi_vars_needing_forward pred.bb_label pred target.bb_instructions) ==>
  v IN FDOM sp.vs_vars
Proof
  rpt strip_tac >>
  `supply_prefix_defined f st` by metis_tac[supply_frame_reach_prefix] >>
  `~sp.vs_halted` by
    metis_tac[supply_frame_reach_not_halted, step_inst_ok_halted,
              fn_entry_state_def] >>
  `exec_block fuel ctx pred st = OK sp` by
    (gvs[active_inst_def] >>
     `bb = pred` by metis_tac[same_label_same_block] >> gvs[] >>
     irule supply_active_terminator_exec_block >> metis_tac[]) >>
  irule phi_forward_sources_exec_block_defined >>
  qexistsl [`ctx`, `f`, `fuel`, `pred`, `st`, `target`] >> simp[]
QED

Definition supply_frame_body_def:
  supply_frame_body C fn fn' (s:ir_supply) pred target split repls s0 inst' v <=>
    ?bb inst a.
      MEM bb fn.fn_blocks /\ frame_reach C fn s0 inst a /\
      active_inst fn inst a /\ a.vs_current_bb = bb.bb_label /\
      v.vs_current_bb = bb.bb_label /\ a.vs_inst_idx = v.vs_inst_idx /\
      phi_prefix_length bb.bb_instructions <= a.vs_inst_idx /\
      inst = EL a.vs_inst_idx bb.bb_instructions /\
      inst' = EL v.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions /\
      active_inst fn' inst' v /\ supply_state_agree fn a v
End

Definition supply_frame_split_def:
  supply_frame_split C fn fn' (s:ir_supply) pred target split repls s0 inst' v <=>
    ?inst a u k.
      frame_reach C fn s0 inst a /\ active_inst fn inst a /\
      a.vs_current_bb = pred.bb_label /\ is_terminator inst.inst_opcode /\
      step_inst k C inst a = OK u /\ ~u.vs_halted /\
      supply_entry_defined fn u /\ u.vs_current_bb = target.bb_label /\
      u.vs_prev_bb = SOME pred.bb_label /\
      active_inst fn' inst' v /\ v.vs_current_bb = split.bb_label /\
      v.vs_inst_idx < LENGTH split.bb_instructions /\
      inst' = EL v.vs_inst_idx split.bb_instructions /\ ~v.vs_halted /\
      supply_state_agree fn a v /\
      (!fuel. ?m. exec_block fuel C split v = OK m /\
                   supply_ready fn pred target split repls u m)
End

Definition supply_frame_phase_def:
  supply_frame_phase C fn fn' s pred target split repls s0 inst' v <=>
    supply_frame_body C fn fn' s pred target split repls s0 inst' v \/
    supply_frame_split C fn fn' s pred target split repls s0 inst' v
End

Theorem supply_frame_phase_start:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  fn_entry_state fn s0 /\ enters_block fn' s0 v /\ active_inst fn' inst' v ==>
  supply_frame_phase C fn fn' s pred target split repls s0 inst' v
Proof
  strip_tac >>
  `supply_ready fn pred target split repls s0 s0` by
    (irule supply_ready_entry >> simp[]) >>
  `supply_entry_defined fn s0` by gvs[supply_ready_def] >>
  drule_all supply_entry_defined_lookup >> strip_tac >>
  drule_all supply_ready_image_lookup >> strip_tac >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  rename1 `eval_phis s0 (supply_block_image pred target split repls bb).bb_instructions = OK sp` >>
  `?out. eval_phis s0 bb.bb_instructions = OK out /\ supply_state_agree fn out sp` by
    (qpat_x_assum `supply_ready _ _ _ _ _ _ _` mp_tac >>
     simp[supply_ready_def] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s0.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `out.vs_current_bb = s0.vs_current_bb /\ sp.vs_current_bb = s0.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `phi_prefix_length (supply_block_image pred target split repls bb).bb_instructions =
    phi_prefix_length bb.bb_instructions` by metis_tac[supply_block_image_phi_prefix] >>
  gvs[] >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions /\
   inst' = EL (phi_prefix_length bb.bb_instructions)
     (supply_block_image pred target split repls bb).bb_instructions` by
    (qpat_x_assum `active_inst _ _ _` mp_tac >>
     simp[active_inst_def] >> rpt strip_tac >>
     `bb' = supply_block_image pred target split repls bb` by
       metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def,
                 optionTheory.SOME_11] >> gvs[]) >>
  `active_inst fn (EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
     (out with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[]) >>
  `frame_reach C fn s0 (EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
     (out with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (irule frame_reach_start >> simp[enters_block_def] >> metis_tac[]) >>
  simp[supply_frame_phase_def] >> disj1_tac >>
  simp[supply_frame_body_def] >>
  qexistsl [`bb`, `out with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[supply_state_agree_inst_idx] >> metis_tac[]
QED

Theorem supply_frame_split_next:
  wf_function fn' /\ MEM split fn'.fn_blocks /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_frame_split C fn fn' s pred target split repls s0 inst' v /\
  ~is_terminator inst'.inst_opcode /\ step_inst fuel C inst' v = OK w /\
  active_inst fn' next (w with vs_inst_idx := SUC v.vs_inst_idx) ==>
  supply_frame_split C fn fn' s pred target split repls s0 next
    (w with vs_inst_idx := SUC v.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `supply_frame_split _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[supply_frame_split_def] >> strip_tac >>
  drule_all supply_split_step_agree >> strip_tac >>
  `run_insts fuel C [inst'] v = OK w` by simp[analysisSimDefsTheory.run_insts_def] >>
  `w.vs_current_bb = v.vs_current_bb` by
    (mp_tac (Q.SPEC `[inst']` supply_assigns_run_control) >> simp[] >> metis_tac[]) >>
  `SUC v.vs_inst_idx < LENGTH split.bb_instructions /\
   next = EL (SUC v.vs_inst_idx) split.bb_instructions` by
    (qpat_x_assum `active_inst fn' next _` mp_tac >>
     simp[active_inst_def] >> rpt strip_tac >>
     `bb = split` by metis_tac[same_label_same_block] >> gvs[]) >>
  `!n. ?m. exec_block n C split (w with vs_inst_idx := SUC v.vs_inst_idx) = OK m /\
     supply_ready fn pred target split repls u m` by
    (gen_tac >> first_x_assum (qspec_then `n` strip_assume_tac) >>
     `step_inst n C inst' v = OK w` by metis_tac[supply_assign_fuel_independent] >>
     drule_all supply_exec_block_step_residual >> strip_tac >> metis_tac[]) >>
  simp[supply_frame_split_def] >>
  qexistsl [`inst`, `a`, `u`, `k`] >>
  simp[] >>
  qpat_x_assum `supply_state_agree fn a w` mp_tac >>
  simp[supply_state_agree_def, stateFrameTheory.execution_frame_def,
       venomStateTheory.lookup_var_def]
QED

Theorem supply_frame_body_next:
  wf_function fn /\ wf_function fn' /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  supply_frame_body C fn fn' s pred target split repls s0 inst' v /\
  ~is_terminator inst'.inst_opcode /\ step_inst fuel C inst' v = OK w /\
  active_inst fn' next (w with vs_inst_idx := SUC v.vs_inst_idx) ==>
  supply_frame_body C fn fn' s pred target split repls s0 next
    (w with vs_inst_idx := SUC v.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `supply_frame_body _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[supply_frame_body_def] >> strip_tac >>
  `v.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
  `bb_well_formed bb` by metis_tac[wf_function_def, listTheory.EVERY_MEM] >>
  `(EL v.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI` by
    metis_tac[supply_body_non_phi] >>
  `~is_terminator (EL v.vs_inst_idx bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `~is_terminator _` mp_tac >>
     simp[supply_block_image_body_index, cfgTransformTheory.subst_label_inst_def] >>
     IF_CASES_TAC >> simp[]) >>
  `lift_result
     (\u w. supply_state_agree fn u w /\
            u.vs_current_bb = w.vs_current_bb /\ u.vs_inst_idx = w.vs_inst_idx)
     (supply_state_agree fn) (supply_state_agree fn)
     (step_inst fuel C (EL v.vs_inst_idx bb.bb_instructions) a)
     (step_inst fuel C inst' v)` by
    (qpat_x_assum `inst' = _` (fn th => rewrite_tac[th]) >>
     irule supply_block_image_step_body >> simp[]) >>
  Cases_on `step_inst fuel C (EL v.vs_inst_idx bb.bb_instructions) a` >>
  gvs[stateEquivTheory.lift_result_def] >>
  rename1 `step_inst fuel C (EL v.vs_inst_idx bb.bb_instructions) a = OK u` >>
  `w.vs_current_bb = bb.bb_label` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  `MEM (supply_block_image pred target split repls bb) fn'.fn_blocks` by
    metis_tac[insert_split_supply_image_mem] >>
  `SUC v.vs_inst_idx < LENGTH bb.bb_instructions /\
   next = EL (SUC v.vs_inst_idx)
     (supply_block_image pred target split repls bb).bb_instructions` by
    (qpat_x_assum `active_inst fn' next _` mp_tac >>
     simp[active_inst_def] >> rpt strip_tac >>
     `bb' = supply_block_image pred target split repls bb` by
       metis_tac[same_label_same_block, supply_block_image_label] >> gvs[]) >>
  `active_inst fn (EL (SUC v.vs_inst_idx) bb.bb_instructions)
     (u with vs_inst_idx := SUC v.vs_inst_idx)` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[]) >>
  `frame_reach C fn s0 (EL (SUC v.vs_inst_idx) bb.bb_instructions)
     (u with vs_inst_idx := SUC v.vs_inst_idx)` by
    (qpat_assum `a.vs_inst_idx = v.vs_inst_idx`
       (fn th => rewrite_tac[GSYM th]) >>
     irule frame_reach_next >> metis_tac[]) >>
  qexistsl [`bb`, `u with vs_inst_idx := SUC v.vs_inst_idx`] >>
  simp[supply_state_agree_inst_idx]
QED

Theorem supply_frame_phase_next:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  supply_frame_phase C fn fn' s pred target split repls s0 inst' v /\
  ~is_terminator inst'.inst_opcode /\ step_inst fuel C inst' v = OK w /\
  active_inst fn' next (w with vs_inst_idx := SUC v.vs_inst_idx) ==>
  supply_frame_phase C fn fn' s pred target split repls s0 next
    (w with vs_inst_idx := SUC v.vs_inst_idx)
Proof
  strip_tac >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `MEM split fn'.fn_blocks` by (drule_all supply_split_label_not_old >> strip_tac >>
     metis_tac[insert_split_supply_split_lookup, lookup_block_MEM, fn_labels_def]) >>
  gvs[supply_frame_phase_def]
  >- (disj1_tac >> irule supply_frame_body_next >> metis_tac[]) >>
  disj2_tac >> irule supply_frame_split_next >> metis_tac[]
QED

Theorem supply_frame_body_terminator_step:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  supply_frame_body C fn fn' s pred target split repls s0 inst' v /\
  is_terminator inst'.inst_opcode /\ step_inst fuel C inst' v = OK w ==>
  ?bb inst a u.
    MEM bb fn.fn_blocks /\ frame_reach C fn s0 inst a /\
    active_inst fn inst a /\ a.vs_current_bb = bb.bb_label /\
    supply_state_agree fn a v /\ is_terminator inst.inst_opcode /\
    step_inst fuel C inst a = OK u /\ supply_state_agree fn u w /\
    (~u.vs_halted ==>
      w.vs_current_bb =
        (if bb.bb_label = pred.bb_label /\
            (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
            u.vs_current_bb = target.bb_label
         then split.bb_label else u.vs_current_bb) /\
      w.vs_inst_idx = u.vs_inst_idx /\ w.vs_prev_bb = u.vs_prev_bb)
Proof
  strip_tac >>
  qpat_x_assum `supply_frame_body _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[supply_frame_body_def] >> strip_tac >>
  `v.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
  `inst_wf (EL v.vs_inst_idx bb.bb_instructions) /\
   label_positions_ok (EL v.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `EVERY label_positions_ok _` mp_tac >>
     rewrite_tac[fn_insts_def, ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
     simp[listTheory.EVERY_MEM] >> strip_tac >>
     gvs[fn_inst_wf_def] >> metis_tac[listTheory.EL_MEM]) >>
  `is_terminator (EL v.vs_inst_idx bb.bb_instructions).inst_opcode` by
    metis_tac[supply_block_image_index] >>
  `lift_result
     (\u w. supply_state_agree fn u w /\ (~u.vs_halted ==>
       w.vs_current_bb =
         (if bb.bb_label = pred.bb_label /\
             ((EL v.vs_inst_idx bb.bb_instructions).inst_opcode = JMP \/
              (EL v.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ) /\
             u.vs_current_bb = target.bb_label
          then split.bb_label else u.vs_current_bb) /\
       w.vs_inst_idx = u.vs_inst_idx /\ w.vs_prev_bb = u.vs_prev_bb))
     (supply_state_agree fn) (supply_state_agree fn)
     (step_inst fuel C (EL v.vs_inst_idx bb.bb_instructions) a)
     (step_inst fuel C inst' v)` by
    (qpat_x_assum `inst' = _` (fn th => rewrite_tac[th]) >>
     irule supply_block_image_step_terminator >> simp[]) >>
  Cases_on `step_inst fuel C (EL v.vs_inst_idx bb.bb_instructions) a` >>
  gvs[stateEquivTheory.lift_result_def] >>
  rename1 `step_inst fuel C (EL v.vs_inst_idx bb.bb_instructions) a = OK u` >>
  qexistsl [`bb`, `EL v.vs_inst_idx bb.bb_instructions`, `a`, `u`] >> simp[]
QED

Theorem supply_frame_body_exit_pair:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  fn_entry_state fn s0 /\
  supply_frame_body C fn fn' s pred target split repls s0 inst' v /\
  is_terminator inst'.inst_opcode /\ step_inst fuel C inst' v = OK w /\ ~w.vs_halted ==>
  ?inst a u.
    frame_reach C fn s0 inst a /\ active_inst fn inst a /\
    supply_state_agree fn a v /\ is_terminator inst.inst_opcode /\
    step_inst fuel C inst a = OK u /\ supply_entry_pair fn s pred target split repls u w
Proof
  strip_tac >> drule_all supply_frame_body_terminator_step >> strip_tac >>
  `~u.vs_halted` by metis_tac[supply_state_agree_halted] >>
  `supply_entry_defined fn u` by metis_tac[supply_frame_reach_terminator_entry] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
  `step_inst_base inst a = OK u` by
    (qpat_x_assum `step_inst fuel C inst a = OK u` mp_tac >>
     simp[Once step_inst_def]) >>
  `u.vs_prev_bb = SOME bb.bb_label` by metis_tac[step_inst_base_term_prev_bb] >>
  `bb_well_formed bb` by metis_tac[wf_function_def, listTheory.EVERY_MEM] >>
  `inst = LAST bb.bb_instructions` by
    (gvs[active_inst_def] >>
     `bb' = bb` by metis_tac[same_label_same_block] >>
     gvs[bb_well_formed_def, listTheory.LAST_EL] >> metis_tac[]) >>
  `bb.bb_label = pred.bb_label <=> bb = pred` by metis_tac[same_label_same_block] >>
  `bb = pred ==> (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ)` by
    (strip_tac >> gvs[] >> irule supply_multi_successor_jump >> simp[] >>
     qpat_x_assum `EVERY label_positions_ok _` mp_tac >>
     rewrite_tac[fn_insts_def, ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `split.bb_label <> bb.bb_label` by
    (drule_all supply_split_label_not_old >>
     simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  qexistsl [`inst`, `a`, `u`] >> simp[] >>
  Cases_on `bb = pred /\ u.vs_current_bb = target.bb_label`
  >- (gvs[supply_entry_pair_def] >> disj2_tac >> simp[supply_pending_def] >>
      `EVERY (\x. MEM x s.irs_used_vars) (block_ir_vars target)` by
        (gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
             venomFnScheduleRunnerTheory.list_subset_def,
             listTheory.EVERY_MEM, irSupplyTheory.fn_ir_vars_def] >>
         metis_tac[listTheory.MEM_FLAT, listTheory.MEM_MAP]) >>
      drule cfgNormSupplyProofsTheory.EVERY_phi_vars_needing_forward_covered >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`] assume_tac) >>
      gvs[listTheory.EVERY_MEM] >> rpt strip_tac >> simp[] >>
      `x IN FDOM u.vs_vars` by metis_tac[supply_frame_reach_forward_sources] >>
      simp[venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DEF]) >>
  simp[supply_entry_pair_def] >> disj1_tac >> irule supply_ready_other_entry >>
  Cases_on `bb = pred` >> gvs[] >> metis_tac[]
QED

Theorem supply_frame_ready_block:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  frame_reach C fn s0 inst a /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst a = OK u /\
  supply_ready fn pred target split repls u w /\
  enters_block fn' w z /\ active_inst fn' next z ==>
  supply_frame_body C fn fn' s pred target split repls s0 next z
Proof
  strip_tac >>
  `supply_entry_defined fn u` by gvs[supply_ready_def] >>
  drule_all supply_entry_defined_lookup >> strip_tac >>
  drule_all supply_ready_image_lookup >> strip_tac >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  rename1 `eval_phis w (supply_block_image pred target split repls bb).bb_instructions = OK sp` >>
  `?out. eval_phis u bb.bb_instructions = OK out /\ supply_state_agree fn out sp` by
    (qpat_x_assum `supply_ready _ _ _ _ _ _ _` mp_tac >>
     simp[supply_ready_def] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = u.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `out.vs_current_bb = u.vs_current_bb /\ sp.vs_current_bb = w.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `u.vs_current_bb = w.vs_current_bb /\ ~u.vs_halted` by gvs[supply_ready_def] >>
  `phi_prefix_length (supply_block_image pred target split repls bb).bb_instructions =
    phi_prefix_length bb.bb_instructions` by metis_tac[supply_block_image_phi_prefix] >>
  gvs[] >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions /\
   next = EL (phi_prefix_length bb.bb_instructions)
     (supply_block_image pred target split repls bb).bb_instructions` by
    (qpat_x_assum `active_inst _ _ _` mp_tac >>
     simp[active_inst_def] >> rpt strip_tac >>
     `bb' = supply_block_image pred target split repls bb` by
       metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def,
                 optionTheory.SOME_11] >> gvs[]) >>
  `active_inst fn (EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
     (out with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[]) >>
  `frame_reach C fn s0 (EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
     (out with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (irule frame_reach_block >> simp[enters_block_def] >> metis_tac[]) >>
  simp[supply_frame_body_def] >>
  qexistsl [`bb`, `out with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[supply_state_agree_inst_idx] >> metis_tac[]
QED

Theorem supply_frame_pending_block:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  frame_reach C fn s0 inst a /\ active_inst fn inst a /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst a = OK u /\
  supply_pending fn s pred target split u w /\
  enters_block fn' w z /\ active_inst fn' next z ==>
  supply_frame_split C fn fn' s pred target split repls s0 next z
Proof
  strip_tac >>
  drule_all supply_pending_split_lookup >> strip_tac >>
  drule supply_split_no_phi_entry >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  `z = w with vs_inst_idx := 0` by gvs[enters_block_def] >>
  `supply_state_agree fn a u` by metis_tac[supply_terminator_step_self_agree] >>
  `a.vs_current_bb = pred.bb_label` by
    (`inst.inst_opcode <> INVOKE` by
       (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
     `step_inst_base inst a = OK u` by
       (qpat_x_assum `step_inst fuel C inst a = OK u` mp_tac >>
        simp[Once step_inst_def]) >>
     `u.vs_prev_bb = SOME a.vs_current_bb` by
       metis_tac[step_inst_base_term_prev_bb] >>
     gvs[supply_pending_def]) >>
  `!n. ?m. exec_block n C split z = OK m /\
        supply_ready fn pred target split repls u m` by
    (gen_tac >>
     drule_all supply_pending_contract >>
     disch_then (qspecl_then [`n`, `C`] strip_assume_tac) >>
     qexists_tac `m` >> gvs[run_block_entry_def]) >>
  `supply_state_agree fn a z` by
    (`supply_state_agree fn u w` by gvs[supply_pending_def] >>
     `supply_state_agree fn a w` by metis_tac[supply_state_agree_trans] >>
     gvs[supply_state_agree_def, stateFrameTheory.execution_frame_def,
         venomStateTheory.lookup_var_def]) >>
  simp[supply_frame_split_def] >>
  qexistsl [`inst`, `a`, `u`, `fuel`] >>
  gvs[supply_pending_def] >>
  qpat_x_assum `active_inst fn' next _` mp_tac >>
  simp[active_inst_def] >> rpt strip_tac >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `lookup_block bb.bb_label fn'.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `bb = split` by gvs[] >>
  gvs[]
QED

Theorem supply_frame_body_block:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  fn_entry_state fn s0 /\
  supply_frame_body C fn fn' s pred target split repls s0 inst' v /\
  is_terminator inst'.inst_opcode /\ step_inst fuel C inst' v = OK w /\
  ~w.vs_halted /\ enters_block fn' w z /\ active_inst fn' next z ==>
  supply_frame_phase C fn fn' s pred target split repls s0 next z
Proof
  strip_tac >> drule_all supply_frame_body_exit_pair >> strip_tac >>
  gvs[supply_entry_pair_def] >> simp[supply_frame_phase_def]
  >- (disj1_tac >> irule supply_frame_ready_block >> metis_tac[]) >>
  disj2_tac >> irule supply_frame_pending_block >> metis_tac[]
QED

Theorem supply_frame_split_block:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  supply_frame_split C fn fn' s pred target split repls s0 inst' v /\
  is_terminator inst'.inst_opcode /\ step_inst fuel C inst' v = OK w /\
  ~w.vs_halted /\ enters_block fn' w z /\ active_inst fn' next z ==>
  supply_frame_body C fn fn' s pred target split repls s0 next z
Proof
  strip_tac >> gvs[supply_frame_split_def] >>
  first_x_assum (qspec_then `fuel` strip_assume_tac) >>
  `w = m` by metis_tac[supply_exec_block_step_residual] >>
  irule supply_frame_ready_block >> metis_tac[]
QED

Theorem supply_frame_reach_phase:
  !C fn' s0 inst' v. frame_reach C fn' s0 inst' v ==>
  !fn s pred target split repls s'.
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\ fn_entry_state fn s0 ==>
  supply_frame_phase C fn fn' s pred target split repls s0 inst' v
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule supply_frame_phase_start >> metis_tac[]) 
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule supply_frame_phase_next >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `supply_frame_phase C fn fn' s pred target split repls s0 inst' v` by
    metis_tac[] >>
  qpat_x_assum `supply_frame_phase _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [supply_frame_phase_def])
  >- (irule supply_frame_body_block >> metis_tac[]) >>
  simp[supply_frame_phase_def] >>
  disj1_tac >> irule supply_frame_split_block >> metis_tac[]
QED

Theorem supply_frame_body_witness:
  wf_function fn /\
  supply_frame_body C fn fn' s pred target split repls s0 inst' v ==>
  ?bb inst a.
    MEM bb fn.fn_blocks /\ frame_reach C fn s0 inst a /\
    active_inst fn inst a /\ supply_state_agree fn a v /\
    a.vs_current_bb = bb.bb_label /\ v.vs_current_bb = bb.bb_label /\
    a.vs_inst_idx = v.vs_inst_idx /\
    inst = EL a.vs_inst_idx bb.bb_instructions /\
    inst' = EL v.vs_inst_idx
      (supply_block_image pred target split repls bb).bb_instructions /\
    inst'.inst_opcode = inst.inst_opcode
Proof
  strip_tac >> gvs[supply_frame_body_def] >>
  qexistsl [`bb`, `a`] >> simp[] >>
  irule (cj 1 supply_block_image_index) >> gvs[active_inst_def] >>
  `bb' = bb` by metis_tac[same_label_same_block] >> gvs[]
QED

Theorem supply_frame_split_witness:
  supply_frame_split C fn fn' s pred target split repls s0 inst' v ==>
  ?inst a.
    frame_reach C fn s0 inst a /\ active_inst fn inst a /\
    supply_state_agree fn a v /\ a.vs_current_bb = pred.bb_label /\
    is_terminator inst.inst_opcode /\
    v.vs_current_bb = split.bb_label /\
    v.vs_inst_idx < LENGTH split.bb_instructions /\
    inst' = EL v.vs_inst_idx split.bb_instructions
Proof
  simp[supply_frame_split_def] >> metis_tac[]
QED

Theorem supply_ctx_bisim_step_back:
  ctx_bisim C C' /\ step_inst fuel' C' inst v = OK w ==>
  ?fuel. step_inst fuel C inst v = OK w
Proof
  strip_tac >> drule (cj 2 ctx_bisim_step_inst) >>
  disch_then (qspecl_then [`fuel'`, `inst`, `v`] mp_tac) >>
  simp[passSimulationDefsTheory.terminates_def] >> strip_tac >>
  Cases_on `step_inst fuel C inst v` >>
  gvs[step_result_rel_def, frame_result_rel_def] >> metis_tac[]
QED

Theorem supply_frame_reach_ctx_back:
  !C' fn s0 inst v. frame_reach C' fn s0 inst v ==>
  !C. ctx_bisim C C' ==> frame_reach C fn s0 inst v
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule frame_reach_start >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      drule_all supply_ctx_bisim_step_back >> strip_tac >>
      irule frame_reach_next >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all supply_ctx_bisim_step_back >> strip_tac >>
  irule frame_reach_block >> metis_tac[]
QED

Theorem supply_mem_corr_refl:
  mem_corr inst v inst v
Proof
  simp[mem_corr_def]
QED

Theorem supply_call_corr_refl:
  inst_wf inst ==> call_corr inst v inst v
Proof
  simp[call_corr_def] >> rpt strip_tac >>
  gvs[inst_wf_def, decode_invoke_def]
QED

Theorem supply_call_corr_trans:
  call_corr i a j b /\ call_corr j b k c ==> call_corr i a k c
Proof
  pure_rewrite_tac[call_corr_def] >>
  Cases_on `k.inst_opcode = INVOKE` >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem supply_frame_sim_refl:
  fn_inst_wf fn ==> frame_sim L C C fn fn
Proof
  simp[frame_sim_def] >> rpt strip_tac >>
  `active_inst fn inst' s'` by metis_tac[supply_frame_reach_prefix] >>
  `inst_wf inst'` by
    (gvs[active_inst_def, fn_inst_wf_def] >> metis_tac[listTheory.MEM_EL]) >>
  metis_tac[supply_mem_corr_refl, supply_call_corr_refl]
QED

Theorem supply_frame_sim_trans:
  frame_sim L C1 C2 f g /\ frame_sim L C2 C3 g h /\
  fn_entry_label f = fn_entry_label g ==> frame_sim L C1 C3 f h
Proof
  simp[frame_sim_def] >> rpt strip_tac >>
  `fn_entry_state g s0` by gvs[fn_entry_state_def] >>
  metis_tac[mem_corr_trans, supply_call_corr_trans]
QED

Theorem supply_run_blocks_frame_refl:
  terminates (run_blocks fuel ctx fn s) ==>
  frame_result_rel (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn s)
Proof
  Cases_on `run_blocks fuel ctx fn s` >>
  simp[passSimulationDefsTheory.terminates_def, frame_result_rel_def] >>
  metis_tac[run_blocks_not_OK]
QED

Theorem supply_fn_bisim_refl:
  fn_bisim fn fn
Proof
  simp[fn_bisim_def] >> metis_tac[supply_run_blocks_frame_refl]
QED

Theorem supply_fn_bisim_trans:
  fn_bisim f g /\ fn_bisim g h ==> fn_bisim f h
Proof
  simp[fn_bisim_def] >> rpt strip_tac >>
  `fn_entry_state g s` by gvs[fn_entry_state_def] >>
  metis_tac[frame_result_rel_trans, frame_result_rel_terminates]
QED

Theorem supply_eval_operands_cong:
  !ops a b. (!op. MEM op ops ==> eval_operand op a = eval_operand op b) ==>
  eval_operands ops a = eval_operands ops b
Proof
  Induct >> simp[venomStateTheory.eval_operands_def] >> rpt strip_tac >>
  `eval_operand h a = eval_operand h b` by metis_tac[] >>
  `eval_operands ops a = eval_operands ops b` by metis_tac[] >> simp[]
QED

Theorem supply_inst_mem_ranges_empty:
  MEM inst.inst_opcode [PHI; JMP; JNZ; ASSIGN] ==> inst_mem_ranges inst a = []
Proof
  simp[listTheory.MEM, unitMemInvTheory.inst_mem_ranges_def] >>
  rpt strip_tac >>
  simp[contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem supply_dret_read_cong:
  (!op. MEM op inst.inst_operands ==> eval_operand op a = eval_operand op b) ==>
  contextCodegenRel$dret_memory_read_ranges inst a =
  contextCodegenRel$dret_memory_read_ranges inst b
Proof
  strip_tac >>
  `eval_operands inst.inst_operands a = eval_operands inst.inst_operands b` by
    (irule supply_eval_operands_cong >> simp[]) >>
  simp[contextCodegenRelTheory.dret_memory_read_ranges_def]
QED

Theorem supply_log_read_cong:
  inst.inst_opcode = LOG /\
  (!op. MEM op inst.inst_operands ==> eval_operand op a = eval_operand op b) ==>
  contextCodegenRel$source_memory_read_ranges inst a =
  contextCodegenRel$source_memory_read_ranges inst b
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >>
  simp[contextCodegenRelTheory.source_memory_read_ranges_def] >>
  Cases_on `h` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  `!op. MEM op (REVERSE t) ==> eval_operand op a = eval_operand op b` by
    gvs[] >>
  `!op. MEM op (DROP 2 (REVERSE t)) ==> eval_operand op a = eval_operand op b` by
    metis_tac[rich_listTheory.MEM_DROP_IMP] >>
  `eval_operands (DROP 2 (REVERSE t)) a = eval_operands (DROP 2 (REVERSE t)) b` by
    (irule supply_eval_operands_cong >> simp[]) >>
  `eval_operand (EL 0 (REVERSE t)) a = eval_operand (EL 0 (REVERSE t)) b /\
   eval_operand (EL 1 (REVERSE t)) a = eval_operand (EL 1 (REVERSE t)) b` by
    (conj_tac >>
     qpat_x_assum `!op. MEM op (REVERSE t) ==> _` irule >>
     irule listTheory.EL_MEM >> simp[]) >>
  gvs[contextCodegenRelTheory.memory_range_of_operands_def]
QED

Theorem supply_read_ranges_cong:
  (!op. MEM op inst.inst_operands ==> eval_operand op a = eval_operand op b) ==>
  contextCodegenRel$source_memory_read_ranges inst a =
  contextCodegenRel$source_memory_read_ranges inst b
Proof
  strip_tac >> Cases_on `inst.inst_opcode = LOG`
  >- (irule supply_log_read_cong >> simp[]) >>
  Cases_on `inst.inst_opcode` >>
  simp[contextCodegenRelTheory.source_memory_read_ranges_def]
  >~ [`dret_memory_read_ranges _ _ = _`]
  >- (irule supply_dret_read_cong >> simp[]) >>
  simp[contextCodegenRelTheory.memory_range_of_operands_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os3` ["", "o4 os4"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os4` ["", "o5 os5"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os5` ["", "o6 os6"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os6` ["", "o7 os7"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `os7` >> gvs[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem supply_write_ranges_cong:
  a.vs_call_entry_fmp = b.vs_call_entry_fmp /\
  (!op. MEM op inst.inst_operands ==> eval_operand op a = eval_operand op b) ==>
  source_memory_write_ranges inst a = source_memory_write_ranges inst b
Proof
  strip_tac >>
  `eval_operands inst.inst_operands a = eval_operands inst.inst_operands b` by
    (irule supply_eval_operands_cong >> simp[]) >>
  Cases_on `inst.inst_opcode` >>
  simp[codegenRelTheory.source_memory_write_ranges_def] >>
  simp[codegenRelTheory.fixed_source_write_range_def,
       codegenRelTheory.sized_source_write_range_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os3` ["", "o4 os4"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os4` ["", "o5 os5"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os5` ["", "o6 os6"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os6` ["", "o7 os7"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `os7` >> gvs[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem supply_inst_mem_ranges_cong:
  a.vs_call_entry_fmp = b.vs_call_entry_fmp /\
  (!op. MEM op inst.inst_operands ==> eval_operand op a = eval_operand op b) ==>
  inst_mem_ranges inst a = inst_mem_ranges inst b
Proof
  strip_tac >>
  drule_all supply_read_ranges_cong >>
  drule_all supply_write_ranges_cong >>
  simp[unitMemInvTheory.inst_mem_ranges_def]
QED

Theorem supply_block_image_index_unchanged:
  i < LENGTH bb.bb_instructions /\
  label_positions_ok (EL i bb.bb_instructions) /\
  ~MEM (EL i bb.bb_instructions).inst_opcode [PHI; JMP; JNZ] ==>
  EL i (supply_block_image pred target split repls bb).bb_instructions =
    EL i bb.bb_instructions
Proof
  strip_tac >>
  `!old new. is_terminator (EL i bb.bb_instructions).inst_opcode ==>
    subst_label_inst old new (EL i bb.bb_instructions) = EL i bb.bb_instructions` by
    metis_tac[supply_subst_label_nonjump_terminator, listTheory.MEM] >>
  simp[supply_block_image_def] >> rpt IF_CASES_TAC >>
  simp[supply_update_phis_index, supply_subst_terminator_index,
       cfgTransformTheory.subst_label_terminator_def, listTheory.EL_MAP] >>
  Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >>
  gvs[]
QED

Theorem supply_resolve_block_assigns_cong:
  !xs ys. LIST_REL (\a b.
    a.inst_opcode = b.inst_opcode /\ a.inst_outputs = b.inst_outputs /\
    (b.inst_opcode = ASSIGN ==> a = b)) xs ys ==>
    !op. resolve_block_assigns xs op = resolve_block_assigns ys op
Proof
  Induct_on `xs` >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  Cases_on `op` >> simp[contextCodegenRelTheory.resolve_block_assigns_def] >>
  Cases_on `h'.inst_opcode = ASSIGN` >> gvs[] >>
  simp[contextCodegenRelTheory.resolve_block_assigns_def] >> metis_tac[]
QED

Theorem supply_block_image_resolve_assigns:
  EVERY label_positions_ok bb.bb_instructions ==>
  resolve_block_assigns
    (REVERSE (TAKE k (supply_block_image pred target split repls bb).bb_instructions)) op =
  resolve_block_assigns (REVERSE (TAKE k bb.bb_instructions)) op
Proof
  strip_tac >> irule supply_resolve_block_assigns_cong >>
  simp[listTheory.LIST_REL_EL_EQN, listTheory.EL_REVERSE, listTheory.EL_TAKE,
       listTheory.LENGTH_TAKE_EQ] >>
  rpt strip_tac >>
  `n < LENGTH bb.bb_instructions` by
    (Cases_on `k <= LENGTH bb.bb_instructions` >> gvs[] >> decide_tac) >>
  drule supply_block_image_index >> strip_tac >> simp[] >>
  irule supply_block_image_index_unchanged >>
  gvs[listTheory.EVERY_EL]
QED

Theorem supply_same_after_assigns_cong:
  !xs ys. LIST_REL (\a b.
    a.inst_opcode = b.inst_opcode /\ a.inst_outputs = b.inst_outputs /\
    (b.inst_opcode = ASSIGN ==> a = b)) xs ys ==>
    !op1 op2. same_after_assigns xs op1 op2 = same_after_assigns ys op1 op2
Proof
  Induct_on `xs` >> Cases_on `ys` >>
  simp[contextCodegenRelTheory.same_after_assigns_def] >> rpt strip_tac >>
  `!op. step_back_assign h' op = step_back_assign h op` by
    (Cases_on `op` >> simp[contextCodegenRelTheory.step_back_assign_def] >>
     Cases_on `h.inst_opcode = ASSIGN` >> gvs[]) >>
  first_x_assum drule >> simp[]
QED

(* CFGNorm's block image keeps every ASSIGN, and the opcode and outputs of
   every instruction, at the same index. *)
Theorem supply_block_image_assign_rel:
  EVERY label_positions_ok bb.bb_instructions ==>
  LIST_REL (\a b.
    a.inst_opcode = b.inst_opcode /\ a.inst_outputs = b.inst_outputs /\
    (b.inst_opcode = ASSIGN ==> a = b))
    (supply_block_image pred target split repls bb).bb_instructions
    bb.bb_instructions
Proof
  strip_tac >> simp[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
  drule supply_block_image_index >> strip_tac >> simp[] >>
  irule supply_block_image_index_unchanged >>
  gvs[listTheory.EVERY_EL]
QED

Theorem supply_block_image_get_instruction:
  get_instruction bb k = SOME inst /\ label_positions_ok inst /\
  ~MEM inst.inst_opcode [PHI; JMP; JNZ] ==>
  get_instruction (supply_block_image pred target split repls bb) k = SOME inst
Proof
  simp[get_instruction_def] >> strip_tac >>
  `k < LENGTH bb.bb_instructions` by (spose_not_then assume_tac >> gvs[]) >>
  gvs[] >> irule supply_block_image_index_unchanged >> simp[]
QED

Theorem supply_block_image_revert_forward_pair:
  EVERY label_positions_ok bb.bb_instructions /\ revert_forward_pair bb i j ==>
  revert_forward_pair (supply_block_image pred target split repls bb) i j
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair bb i j` mp_tac >>
  simp[contextCodegenRelTheory.revert_forward_pair_def] >> strip_tac >>
  `label_positions_ok inst1 /\ label_positions_ok inst2` by
    (gvs[get_instruction_def, listTheory.EVERY_EL] >> metis_tac[]) >>
  `get_instruction (supply_block_image pred target split repls bb) i = SOME inst1 /\
   get_instruction (supply_block_image pred target split repls bb) j = SOME inst2` by
    (conj_tac >> irule supply_block_image_get_instruction >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[get_instruction_def] >>
      `k < LENGTH bb.bb_instructions` by decide_tac >>
      qpat_x_assum `k < LENGTH bb.bb_instructions`
        (mp_then Any mp_tac supply_block_image_index) >>
      simp[] >> metis_tac[]) >>
  qexistsl [`inst1`,`inst2`,`p`,`src`,`rds`,`p'`,`rds'`] >>
  drule_then assume_tac supply_block_image_assign_rel >>
  `!n m op.
     resolve_block_assigns
       (REVERSE (TAKE n (DROP m (supply_block_image pred target split repls bb).bb_instructions))) op =
     resolve_block_assigns (REVERSE (TAKE n (DROP m bb.bb_instructions))) op` by
    (rpt gen_tac >> irule supply_resolve_block_assigns_cong >>
     irule listTheory.LIST_REL_REVERSE >> irule rich_listTheory.LIST_REL_TAKE >>
     irule rich_listTheory.LIST_REL_DROP >> first_assum MATCH_ACCEPT_TAC) >>
  `!n op1 op2.
     same_after_assigns
       (REVERSE (TAKE n (supply_block_image pred target split repls bb).bb_instructions)) op1 op2 =
     same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) op1 op2` by
    (rpt gen_tac >> irule supply_same_after_assigns_cong >>
     irule listTheory.LIST_REL_REVERSE >> irule rich_listTheory.LIST_REL_TAKE >>
     first_assum MATCH_ACCEPT_TAC) >>
  simp[]
QED

Theorem supply_block_image_revert_forward_at:
  EVERY label_positions_ok bb.bb_instructions /\ revert_forward_at bb k ==>
  revert_forward_at (supply_block_image pred target split repls bb) k
Proof
  simp[contextCodegenRelTheory.revert_forward_at_def] >>
  metis_tac[supply_block_image_revert_forward_pair]
QED

Theorem supply_unchanged_inst_projection:
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\ inst_wf inst /\
  supply_state_agree fn a v ==>
  mem_corr inst a inst v /\ call_corr inst a inst v
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op a = eval_operand op v` by
    (rpt strip_tac >> irule supply_eval_operand_agree >>
     simp[] >> metis_tac[supply_operand_in_fn]) >>
  `execution_frame a = execution_frame v` by gvs[supply_state_agree_def] >>
  `a.vs_call_entry_fmp = v.vs_call_entry_fmp /\
   a.vs_alloca_next = v.vs_alloca_next /\ a.vs_allocas = v.vs_allocas /\
   a.vs_initial_fmp = v.vs_initial_fmp` by gvs[stateFrameTheory.execution_frame_def] >>
  conj_tac
  >- (drule_all supply_inst_mem_ranges_cong >> simp[mem_corr_def]) >>
  simp[call_corr_def] >> strip_tac >>
  gvs[inst_wf_def, decode_invoke_def] >>
  irule EQ_SYM >> irule supply_eval_operands_cong >> simp[]
QED

Theorem supply_frame_body_projection:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  supply_frame_body C fn fn' s pred target split repls s0 inst' v ==>
  ?inst a. frame_reach C fn s0 inst a /\
    mem_corr inst a inst' v /\ call_corr inst a inst' v
Proof
  strip_tac >> drule_all supply_frame_body_witness >> strip_tac >>
  `MEM inst bb.bb_instructions /\ a.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[active_inst_def] >>
     `bb' = bb` by metis_tac[same_label_same_block] >>
     gvs[] >> metis_tac[listTheory.EL_MEM]) >>
  `inst_wf inst /\ label_positions_ok inst` by
    (drule_all EVERY_fn_block >>
     gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  qexistsl [`inst`, `a`] >> simp[] >>
  Cases_on `MEM inst.inst_opcode [PHI; JMP; JNZ]`
  >- (`inst_mem_ranges inst' v = []` by
        (irule supply_inst_mem_ranges_empty >> gvs[]) >>
      gvs[mem_corr_def, call_corr_def, supply_state_agree_def,
          stateFrameTheory.execution_frame_def]) >>
  `inst' = inst` by
    (gvs[] >> irule supply_block_image_index_unchanged >> simp[]) >>
  gvs[] >> irule supply_unchanged_inst_projection >> metis_tac[]
QED

Theorem supply_frame_body_projection_rf:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  supply_frame_body C fn fn' s pred target split repls s0 inst' v /\
  inst_mem_ranges inst' v <> [] /\ ~in_revert_forward fn' v ==>
  ?inst a. frame_reach C fn s0 inst a /\ ~in_revert_forward fn a /\
    mem_corr inst a inst' v
Proof
  strip_tac >> drule_all supply_frame_body_witness >> strip_tac >>
  `MEM inst bb.bb_instructions /\ a.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[active_inst_def] >>
     `bb' = bb` by metis_tac[same_label_same_block] >>
     gvs[] >> metis_tac[listTheory.EL_MEM]) >>
  `inst_wf inst /\ label_positions_ok inst /\
   EVERY label_positions_ok bb.bb_instructions` by
    (drule_all EVERY_fn_block >>
     gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `~in_revert_forward fn a` by
    (strip_tac >> gvs[contextCodegenRelTheory.in_revert_forward_def] >>
     `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
     gvs[] >>
     `~MEM split.bb_label (fn_labels fn)` by metis_tac[supply_split_label_not_old] >>
     `split.bb_label <> bb.bb_label` by
       (gvs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
     `lookup_block bb.bb_label fn'.fn_blocks =
        SOME (supply_block_image pred target split repls bb)` by
       (irule insert_split_supply_image_lookup >> metis_tac[]) >>
     `revert_forward_at (supply_block_image pred target split repls bb) v.vs_inst_idx` by
       (irule supply_block_image_revert_forward_at >> metis_tac[]) >> metis_tac[]) >>
  qexistsl [`inst`,`a`] >> simp[] >>
  `~MEM inst.inst_opcode [PHI; JMP; JNZ]` by
    (strip_tac >> `inst_mem_ranges inst' v = []` by
       (irule supply_inst_mem_ranges_empty >> gvs[]) >> gvs[]) >>
  `inst' = inst` by
    (gvs[] >> irule supply_block_image_index_unchanged >> simp[]) >>
  gvs[] >> metis_tac[supply_unchanged_inst_projection]
QED

Theorem supply_frame_split_projection:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_frame_split C fn fn' s pred target split repls s0 inst' v ==>
  ?inst a. frame_reach C fn s0 inst a /\
    mem_corr inst a inst' v /\ call_corr inst a inst' v
Proof
  strip_tac >> drule supply_frame_split_witness >> strip_tac >>
  `MEM inst'.inst_opcode [ASSIGN; JMP]` by
    (drule_all supply_split_index_shape >> gvs[] >> metis_tac[]) >>
  `inst_mem_ranges inst' v = []` by
    (irule supply_inst_mem_ranges_empty >> gvs[]) >>
  qexistsl [`inst`, `a`] >>
  gvs[mem_corr_def, call_corr_def, supply_state_agree_def,
      stateFrameTheory.execution_frame_def]
QED

Theorem insert_split_supply_frame_sim:
  ctx_bisim C C' /\ wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  frame_sim L C C' fn fn'
Proof
  strip_tac >> simp[frame_sim_def] >> rpt strip_tac >>
  `frame_reach C fn' s0 inst' s''` by
    metis_tac[supply_frame_reach_ctx_back] >>
  `supply_frame_phase C fn fn' s pred target split repls s0 inst' s''` by
    metis_tac[supply_frame_reach_phase] >>
  gvs[supply_frame_phase_def]
  >- (irule supply_frame_body_projection >> metis_tac[]) >>
  irule supply_frame_split_projection >> metis_tac[]
QED

Theorem insert_split_supply_frame_sim_rf:
  ctx_bisim C C' /\ wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  frame_sim_rf L C C' fn fn'
Proof
  strip_tac >> simp[frame_sim_rf_def] >> rpt strip_tac >>
  `frame_reach C fn' s0 inst' s''` by
    metis_tac[supply_frame_reach_ctx_back] >>
  `supply_frame_phase C fn fn' s pred target split repls s0 inst' s''` by
    metis_tac[supply_frame_reach_phase] >>
  gvs[supply_frame_phase_def]
  >- (irule supply_frame_body_projection_rf >> metis_tac[]) >>
  drule supply_frame_split_witness >> strip_tac >>
  `MEM inst'.inst_opcode [ASSIGN; JMP]` by
    (drule_all supply_split_index_shape >> gvs[] >> metis_tac[]) >>
  `inst_mem_ranges inst' s'' = []` by
    (irule supply_inst_mem_ranges_empty >> gvs[]) >> gvs[]
QED

Theorem insert_split_supply_fn_bisim:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred (block_preds fn target.bb_label) /\ MEM target fn.fn_blocks /\
  1 < num_succs pred /\ insert_split_supply s fn pred target = (fn',s') ==>
  fn_bisim fn fn'
Proof
  strip_tac >>
  `MEM pred fn.fn_blocks` by gvs[cfgTransformTheory.block_preds_def, listTheory.MEM_FILTER] >>
  `fn.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[insert_split_supply_entry] >>
  `fn'.fn_name = fn.fn_name` by metis_tac[insert_split_supply_name] >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,rest)` >>
  `rest = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  simp[fn_bisim_def] >> rpt gen_tac >> strip_tac >>
  rename1 `fn_entry_state fn u` >>
  `supply_entry_pair fn s pred target split repls u u` by
    (simp[supply_entry_pair_def] >> disj1_tac >>
     irule supply_ready_entry >> simp[]) >>
  conj_tac >> gen_tac >> strip_tac
  >- (drule_all supply_run_blocks_forward >> simp[]) >>
  drule_all supply_run_blocks_reverse >> simp[]
QED

Theorem supply_round_semantics:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  supply_norm_inv s' fn' /\ EVERY label_positions_ok (fn_insts fn') /\
  fn_entry_label fn' = fn_entry_label fn /\ fn_bisim fn fn' /\ frame_sim L C C fn fn'
Proof
  strip_tac >>
  `supply_norm_inv s' fn'` by metis_tac[cfg_norm_round_supply_norm_inv] >>
  `wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    gvs[supply_norm_inv_def] >>
  drule cfg_norm_round_supply_cases >> strip_tac
  >- gvs[supply_fn_bisim_refl, supply_frame_sim_refl] >>
  `MEM pred (block_preds fn target.bb_label)` by
    gvs[cfgTransformTheory.block_preds_def, listTheory.MEM_FILTER] >>
  `EVERY label_positions_ok (fn_insts fn')` by
    metis_tac[insert_split_supply_label_positions_ok] >>
  `fn.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label fn' = fn_entry_label fn` by
    metis_tac[insert_split_supply_entry] >>
  `fn_bisim fn fn'` by metis_tac[insert_split_supply_fn_bisim] >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,rest)` >>
  `rest = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `ctx_bisim C C` by
    (simp[ctx_bisim_def] >> metis_tac[supply_run_blocks_frame_refl]) >>
  irule insert_split_supply_frame_sim >> metis_tac[]
QED

Theorem supply_iter_semantics:
  !n s fn fn' s'.
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  fn_bisim fn fn' /\ frame_sim L C C fn fn'
Proof
  Induct_on `n` >> rpt gen_tac
  >- (strip_tac >> gvs[cfg_norm_iter_supply_def] >>
      metis_tac[supply_fn_bisim_refl, supply_frame_sim_refl,
                supply_norm_inv_projections]) >>
  strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (mid,changed,s1)` >>
  `supply_norm_inv s1 mid /\ EVERY label_positions_ok (fn_insts mid) /\
   fn_entry_label mid = fn_entry_label fn /\ fn_bisim fn mid /\ frame_sim L C C fn mid` by
    metis_tac[supply_round_semantics] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def]
  >- metis_tac[supply_fn_bisim_trans, supply_frame_sim_trans] >>
  metis_tac[]
QED

Theorem cfg_norm_function_supply_fn_bisim:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  fn_bisim fn fn'
Proof
  simp[cfg_norm_function_supply_def] >> strip_tac >>
  `supply_norm_inv s fn` by simp[supply_norm_inv_def] >>
  metis_tac[supply_iter_semantics]
QED

(* A split block's ASSIGNs and JMP touch no memory; every other
   instruction keeps its operands up to the renaming of PHI values. *)
Theorem cfg_norm_function_supply_frame_sim:
  ctx_bisim C C' /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  frame_sim L C C' fn fn'
Proof
  simp[cfg_norm_function_supply_def] >> strip_tac >>
  `supply_norm_inv s fn` by simp[supply_norm_inv_def] >>
  `frame_sim L C C fn fn'` by metis_tac[supply_iter_semantics] >>
  simp[frame_sim_def] >> rpt strip_tac >>
  `frame_reach C fn' s0 inst' s''` by
    metis_tac[supply_frame_reach_ctx_back] >>
  gvs[frame_sim_def] >> metis_tac[]
QED

Theorem supply_frame_sim_rf_refl:
  fn_inst_wf fn ==> frame_sim_rf L C C fn fn
Proof
  simp[frame_sim_rf_def] >> rpt strip_tac >>
  `active_inst fn inst' s'` by metis_tac[supply_frame_reach_prefix] >>
  `inst_wf inst'` by
    (gvs[active_inst_def, fn_inst_wf_def] >> metis_tac[listTheory.MEM_EL]) >>
  metis_tac[supply_mem_corr_refl]
QED

Theorem supply_round_frame_sim_rf:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  frame_sim_rf L C C fn fn'
Proof
  strip_tac >>
  `wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    gvs[supply_norm_inv_def] >>
  drule cfg_norm_round_supply_cases >> strip_tac
  >- gvs[supply_frame_sim_rf_refl] >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,rest)` >>
  `rest = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `ctx_bisim C C` by
    (simp[ctx_bisim_def] >> metis_tac[supply_run_blocks_frame_refl]) >>
  irule insert_split_supply_frame_sim_rf >> metis_tac[]
QED

Theorem supply_iter_frame_sim_rf:
  !n s fn fn' s'.
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  frame_sim_rf L C C fn fn'
Proof
  Induct_on `n` >> rpt gen_tac
  >- (strip_tac >> gvs[cfg_norm_iter_supply_def] >>
      metis_tac[supply_frame_sim_rf_refl, supply_norm_inv_projections]) >>
  strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (mid,changed,s1)` >>
  `supply_norm_inv s1 mid /\ EVERY label_positions_ok (fn_insts mid) /\
   fn_entry_label mid = fn_entry_label fn` by metis_tac[supply_round_semantics] >>
  `frame_sim_rf L C C fn mid` by metis_tac[supply_round_frame_sim_rf] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def]
  >- metis_tac[frame_sim_rf_trans] >> metis_tac[]
QED

Theorem cfg_norm_function_supply_frame_sim_rf:
  ctx_bisim C C' /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  frame_sim_rf L C C' fn fn'
Proof
  simp[cfg_norm_function_supply_def] >> strip_tac >>
  `supply_norm_inv s fn` by simp[supply_norm_inv_def] >>
  `frame_sim_rf L C C fn fn'` by metis_tac[supply_iter_frame_sim_rf] >>
  simp[frame_sim_rf_def] >> rpt strip_tac >>
  `frame_reach C fn' s0 inst' s''` by
    metis_tac[supply_frame_reach_ctx_back] >>
  gvs[frame_sim_rf_def] >> metis_tac[]
QED

(* ===== The stage contract (run 8) ===== *)

Theorem supply_round_entry_identity:
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >> drule cfg_norm_round_supply_cases >> strip_tac
  >- gvs[] >>
  `fn.fn_blocks <> []` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  metis_tac[insert_split_supply_entry]
QED

Theorem supply_iter_entry_identity:
  !n s fn fn' s'. cfg_norm_iter_supply n s fn = (fn',s') ==>
    fn_entry_label fn' = fn_entry_label fn
Proof
  Induct >- simp[cfg_norm_iter_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  `fn_entry_label fn1 = fn_entry_label fn` by metis_tac[supply_round_entry_identity] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def] >> metis_tac[]
QED

Theorem cfg_norm_function_supply_identity:
  cfg_norm_function_supply s fn = (fn',s') ==>
  fn'.fn_name = fn.fn_name /\ fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >> drule cfg_norm_function_supply_metadata >> strip_tac >>
  conj_tac >- gvs[fn_identity_metadata_eq_def] >>
  gvs[cfg_norm_function_supply_def] >> metis_tac[supply_iter_entry_identity]
QED

Theorem cfg_norm_pass_step_replay:
  fn_pass_step rpolicy (CFP_Simple VP_CFGNormalization) observed s fn out ==>
  ?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    cfg_norm_function_supply t fn = (out.fpo_function,t')
Proof
  strip_tac >>
  `MEM fn observed.cu_context.ctx_functions` by
    (gvs[fn_pass_step_def] >>
     drule venomFnScheduleRunnerPropsTheory.lookup_unique_function_member >> simp[]) >>
  `ir_supply_covers_fn s fn` by
    (irule fmpStepBridgeTheory.ir_supply_covers_unit_member >>
     qexists `observed` >> gvs[fn_pass_step_def]) >>
  `cfg_norm_function_supply s fn = (out.fpo_function,out.fpo_supply)` by
    (gvs[fn_pass_step_def, AllCaseEqs()] >> simp[]) >>
  qabbrev_tac `t = s with irs_used_inst_ids := irSupply$fn_ir_inst_ids fn` >>
  `ir_supply_covers_fn t fn /\ ir_supply_inst_ok t` by
    (gvs[Abbr `t`, ir_supply_covers_fn_def, irSupplyTheory.ir_supply_inst_ok_def,
         list_subset_def, listTheory.EVERY_MEM]) >>
  `supply_eq_mod_ids s t` by simp[Abbr `t`, supply_eq_mod_ids_fields] >>
  namedCases_on `cfg_norm_function_supply t fn` ["g u"] >>
  drule_all cfg_norm_function_supply_cong >> strip_tac >>
  qexistsl_tac [`t`,`u`] >> gvs[]
QED

Theorem cfg_norm_stage_functions:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' ==>
  C'.ctx_entry = C.ctx_entry /\
  C'.ctx_global_reserved = C.ctx_global_reserved /\
  LIST_REL (\fn fn'. ?t t'.
    ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    cfg_norm_function_supply t fn = (fn',t'))
    C.ctx_functions C'.ctx_functions
Proof
  simp[ctx_pass_stage_def] >> strip_tac >> simp[] >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[] >> drule cfg_norm_pass_step_replay >> simp[]
QED

Theorem o1_fn_shape_label_positions_ok:
  o1_fn_shape ctx fn ==> EVERY label_positions_ok (fn_insts fn)
Proof
  simp[o1_fn_shape_def, fn_shape_ok_def, inst_shape_ok_def,
       listTheory.EVERY_MEM]
QED

(* The input facts both per-function lemmas assume. *)
Theorem cfg_norm_stage_fn_ok:
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\ MEM fn C.ctx_functions ==>
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  EVERY label_positions_ok (fn_insts fn)
Proof
  strip_tac >>
  `o1_fn_shape C fn` by
    (gvs[o1_ctx_shape_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY label_positions_ok (fn_insts fn)` by
    metis_tac[o1_fn_shape_label_positions_ok] >>
  gvs[o1_fn_shape_def, listTheory.EVERY_MEM]
QED

Theorem cfg_norm_stage_bisim:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions ==> ctx_bisim C C'
Proof
  strip_tac >> drule cfg_norm_stage_functions >> strip_tac >>
  irule fn_bisim_ctx_bisim >>
  gvs[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by simp[listTheory.EL_MEM] >>
  drule_all cfg_norm_stage_fn_ok >> strip_tac >>
  irule cfg_norm_function_supply_fn_bisim >> metis_tac[]
QED

Theorem cfg_norm_stage_sim:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==> ctx_sim D C C' vs vs
Proof
  strip_tac >>
  `ctx_bisim C C'` by (irule cfg_norm_stage_bisim >> metis_tac[]) >>
  `C'.ctx_entry = C.ctx_entry` by gvs[ctx_pass_stage_def] >>
  irule ctx_bisim_ctx_sim >> simp[] >>
  rpt gen_tac >> irule run_context_not_int_ret >> rpt strip_tac >>
  `MEM fn C.ctx_functions /\ fn.fn_name = name` by
    metis_tac[venomInstTheory.lookup_function_MEM,
              ctxLookupAgreeHelpersTheory.lookup_function_selected_name] >>
  gvs[o1_ctx_shape_def, o1_fn_shape_def, listTheory.EVERY_MEM,
      entry_fn_no_return_def] >> metis_tac[]
QED

Theorem cfg_norm_stage_max_live_eom:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' ==>
  max_live_eom C' = max_live_eom C
Proof
  strip_tac >> drule ctx_pass_stage_max_live_eom >>
  simp[venomPassDispatcherTheory.fn_pass_static_layout_effect_def,
       venomPassScheduleTheory.fn_pass_tag_def]
QED

Theorem cfg_norm_stage_mem_inv:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv (lowered_mem_fact eom) C vs ==>
  mem_inv (lowered_mem_fact eom) C' vs
Proof
  strip_tac >>
  `ctx_bisim C C'` by (irule cfg_norm_stage_bisim >> metis_tac[]) >>
  drule cfg_norm_stage_functions >> strip_tac >>
  irule frame_sim_rf_mem_inv >> simp[mem_corr_closed_rf_lowered_mem_fact] >>
  qexists_tac `C` >> simp[] >>
  gvs[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule cfg_norm_function_supply_identity >> strip_tac >> simp[] >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by simp[listTheory.EL_MEM] >>
  drule_all cfg_norm_stage_fn_ok >> strip_tac >>
  metis_tac[cfg_norm_function_supply_frame_sim,
            cfg_norm_function_supply_frame_sim_rf]
QED

(* Row 8 (o1_lowered_inv and wf_ssa) to row 9 (o1_lowered_inv). *)
Theorem cfg_norm_stage_walk:
  o1_run_contract rpolicy D 8
Proof
  simp[o1_run_contract_def, venomPassScheduleTheory.o1_fn_passes_def,
       o1_stage_contract_def, o1_inv_def] >> rpt gen_tac >> strip_tac >>
  gvs[o1_ssa_inv_def, o1_lowered_inv_def, o1_run_state_ok_def,
      unitTransformDefsTheory.o1_initial_state_ok_def] >>
  conj_tac >- (irule cfg_norm_stage_sim >> metis_tac[]) >>
  qexists_tac `eom` >>
  conj_tac >- metis_tac[cfg_norm_stage_max_live_eom] >>
  irule cfg_norm_stage_mem_inv >> metis_tac[]
QED

Theorem o1_contract_cfg_normalization:
  o1_step_contract_at 8 rpolicy (CFP_Simple VP_CFGNormalization) /\
  o1_run_contract rpolicy D 8
Proof
  simp[cfg_norm_step_contract, cfg_norm_stage_walk]
QED
