(*
 * Helpers for fnFrameSteps$phi_prefix_frame_sim: a join block's PHI
 * prefix, run from the lineage entry state of its predecessor, against
 * frameRel$fn_frame_inv.
 *)

Theory fnFrameStepsPhi
Ancestors
  fnPlanLineageJoin genFrameSim fnPlanLineage frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst livenessDefs dfgDefs cfgDefs

Theorem phi_delete_spills_domain[local]:
  !xs ps at.
    at IN FDOM (FOLDL (\p (op, off).
      p with <| ps_spilled := p.ps_spilled \\ op;
                ps_alloc := free_spill_slot off p.ps_alloc |>) ps xs).ps_spilled <=>
    at IN FDOM ps.ps_spilled /\ ~MEM at (MAP FST xs)
Proof
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >> metis_tac[]
QED

Theorem phi_release_dead_spills_domain:
  !live ps at.
    at IN FDOM (release_dead_spills live ps).ps_spilled <=>
    at IN FDOM ps.ps_spilled /\ (?v. at = Var v /\ MEM v live)
Proof
  rpt gen_tac >>
  simp[stackPlanOpsTheory.release_dead_spills_def, phi_delete_spills_domain,
       listTheory.MEM_MAP, listTheory.MEM_FILTER, pairTheory.EXISTS_PROD,
       alistTheory.MEM_fmap_to_alist] >>
  Cases_on `at` >> simp[] >> metis_tac[]
QED

Theorem phi_regular_plan_spill_support:
  !liveness dfg cfg fn inst next_live halting next_term lbl ps ops ps' at.
    generate_regular_inst_plan liveness dfg cfg fn inst next_live
      halting next_term lbl ps = (ops, ps') /\
    at IN FDOM ps'.ps_spilled ==>
    ?v. at = Var v /\ MEM v next_live
Proof
  rpt gen_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (IF_CASES_TAC >> gvs[LET_THM]) >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[phi_release_dead_spills_domain]
QED

Theorem phi_regular_plan_spill_fresh:
  generate_regular_inst_plan liveness dfg cfg fn inst next_live
    halting next_term lbl ps = (ops, ps') /\
  ~MEM out next_live ==> ~(Var out IN FDOM ps'.ps_spilled)
Proof
  strip_tac >> strip_tac >>
  drule_all phi_regular_plan_spill_support >> simp[]
QED

Theorem phi_jmp_plan_spill_support:
  generate_inst_plan liveness dfg cfg fn inst next_live halting next_term lbl ps =
    SOME (ops, ps') /\ inst.inst_opcode = JMP /\
  at IN FDOM ps'.ps_spilled ==>
  ?v. at = Var v /\ MEM v next_live
Proof
  strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def,
      venomInstTheory.is_param_opcode_def, AllCaseEqs()] >>
  drule_all phi_regular_plan_spill_support >> simp[]
QED

Theorem phi_terminal_jmp_spill_support:
  !insts i ps ops ps' at.
    insts <> [] /\ (LAST insts).inst_opcode = JMP /\
    generate_block_insts_plan liveness dfg cfg fn lbl halting n_params
      block_len i insts ps = SOME (ops, ps') /\
    at IN FDOM ps'.ps_spilled ==>
    ?v. at = Var v /\ MEM v (live_vars_at liveness lbl block_len)
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> Cases_on `insts = []`
  >- (gvs[generate_block_insts_plan_def, AllCaseEqs()] >>
      metis_tac[phi_jmp_plan_spill_support]) >>
  simp[generate_block_insts_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[listTheory.LAST_DEF] >>
  first_x_assum irule >> goal_assum drule >> simp[]
QED

Theorem phi_non_param_jmp_last[local]:
  !xs. xs <> [] /\ (LAST xs).inst_opcode = JMP ==>
    FILTER (\inst. ~is_param_opcode inst.inst_opcode) xs <> [] /\
    LAST (FILTER (\inst. ~is_param_opcode inst.inst_opcode) xs) = LAST xs
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> Cases_on `xs = []`
  >- gvs[venomInstTheory.is_param_opcode_def] >>
  simp[listTheory.LAST_DEF] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `is_param_opcode h.inst_opcode` >> simp[listTheory.LAST_DEF]
QED

Theorem phi_jmp_block_spill_support:
  generate_block_plan liveness dfg cfg fn pb ps = SOME (ops, ps') /\
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  at IN FDOM ps'.ps_spilled ==>
  ?v. at = Var v /\
    MEM v (live_vars_at liveness pb.bb_label (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `non_param_insts pb <> [] /\
   (LAST (non_param_insts pb)).inst_opcode = JMP` by
    (drule_all phi_non_param_jmp_last >> simp[non_param_insts_def]) >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all phi_terminal_jmp_spill_support >> simp[]
QED

Theorem phi_jmp_block_spill_fresh:
  generate_block_plan liveness dfg cfg fn pb ps = SOME (ops, ps') /\
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  ~MEM out (live_vars_at liveness pb.bb_label (LENGTH pb.bb_instructions)) ==>
  ~(Var out IN FDOM ps'.ps_spilled)
Proof
  strip_tac >> strip_tac >>
  drule_all phi_jmp_block_spill_support >> simp[]
QED

Theorem phi_lineage_entry_spill_support:
  lineage_entry liveness dfg cfg fn ps0 pred succ ps /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  at IN FDOM ps.ps_spilled ==>
  ?v. at = Var v /\
    MEM v (live_vars_at liveness pb.bb_label (LENGTH pb.bb_instructions))
Proof
  simp[lineage_entry_def] >> rpt strip_tac >> gvs[] >>
  drule_all phi_jmp_block_spill_support >> simp[]
QED

Theorem phi_lineage_entry_spill_fresh:
  lineage_entry liveness dfg cfg fn ps0 pred succ ps /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  ~MEM out (live_vars_at liveness pb.bb_label (LENGTH pb.bb_instructions)) ==>
  ~(Var out IN FDOM ps.ps_spilled)
Proof
  strip_tac >> strip_tac >>
  drule_all phi_lineage_entry_spill_support >> simp[]
QED

Theorem phi_codegen_block_ready:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
  phi_block_ready (liveness_analyze fn) bb
Proof
  simp[codegen_ready_fn_def, phi_operands_ready_def] >>
  Cases_on `EVERY (\b. NULL (collect_phis b.bb_instructions)) fn.fn_blocks` >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac
  >- (`collect_phis bb.bb_instructions = []` by
        (qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
         simp[listTheory.EVERY_MEM] >> metis_tac[listTheory.NULL_EQ]) >>
      simp[phi_block_ready_def, phi_uses_disjoint_def]) >>
  metis_tac[]
QED

Theorem phi_codegen_uses_disjoint:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
  phi_uses_disjoint (collect_phis bb.bb_instructions)
Proof
  strip_tac >> drule_all phi_codegen_block_ready >> simp[phi_block_ready_def]
QED

Theorem phi_codegen_input_dead_after_prefix:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v (inst_uses phi) ==>
  ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >> drule_all phi_codegen_block_ready >>
  simp[phi_block_ready_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem phi_restore_spilled_domain:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops, ps') ==>
    FDOM ps'.ps_spilled = FDOM ps.ps_spilled DIFF set targets
Proof
  Induct_on `targets` >- simp[stackPlanOpsTheory.restore_spilled_plan_def] >>
  rpt gen_tac >>
  simp[stackPlanOpsTheory.restore_spilled_plan_def,
       stackPlanOpsTheory.do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled h` >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[finite_mapTheory.FDOM_DOMSUB] >>
  gvs[finite_mapTheory.FLOOKUP_DEF] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem phi_spill_at_preserves_target_absence[local]:
  do_spill_at d ps = (ops, ps') /\
  ~MEM (stack_peek d ps.ps_stack) targets /\
  MEM at targets /\ at NOTIN FDOM ps.ps_spilled ==>
  at NOTIN FDOM ps'.ps_spilled
Proof
  simp[stackPlanOpsTheory.do_spill_at_def,
       stackPlanOpsTheory.do_spill_tos_def, LET_THM] >>
  Cases_on `d = 0` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `ps.ps_stack = []` >>
  simp[stackModelTheory.stack_peek_def, stackModelTheory.stack_swap_def,
       listTheory.EL_LUPDATE] >> rpt strip_tac >>
  gvs[listTheory.LUPDATE_def] >> metis_tac[]
QED

Theorem phi_selected_spill_not_target[local]:
  select_spill_candidate stk targets dist len = SOME cand ==>
  ~MEM (stack_peek cand stk) targets
Proof
  simp[stackPlanOpsTheory.select_spill_candidate_def, LET_THM] >>
  strip_tac >> drule stackPlanGenTheory.FIND_SOME_MEM >> simp[]
QED


Theorem phi_reduce_depth_target_absence[local]:
  !fuel targets op f len ps ops ps' at.
    reduce_depth_plan fuel targets op f len ps = (ops, ps') /\
    MEM at targets /\ at NOTIN FDOM ps.ps_spilled ==>
    at NOTIN FDOM ps'.ps_spilled
Proof
  Induct_on `fuel` >- (simp[stackPlanOpsTheory.reduce_depth_plan_def] >>
    rpt strip_tac >> gvs[]) >>
  rpt gen_tac >>
  simp[Once stackPlanOpsTheory.reduce_depth_plan_def] >>
  IF_CASES_TAC >- (rpt strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op f len ps.ps_stack` >> simp[]
  >- (rpt strip_tac >> gvs[]) >>
  rename1 `dist <= 16` >>
  IF_CASES_TAC >- (rpt strip_tac >> gvs[]) >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist len` >> simp[]
  >- (rpt strip_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  drule phi_selected_spill_not_target >> strip_tac >>
  drule_all phi_spill_at_preserves_target_absence >> strip_tac >>
  qpat_x_assum `!targets op f len ps ops ps' at. _` drule_all >> simp[]
QED

Theorem phi_reorder_restore_absence[local]:
  at NOTIN FDOM ps.ps_spilled ==>
  at NOTIN FDOM (SND
    (case stack_get_unfixed_depth op f len ps.ps_stack of
       SOME _ => ([], ps)
     | NONE => case FLOOKUP ps.ps_spilled op of
         SOME _ => do_restore op ps | NONE => ([], ps))).ps_spilled
Proof
  Cases_on `stack_get_unfixed_depth op f len ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[stackPlanOpsTheory.do_restore_def, finite_mapTheory.FDOM_DOMSUB]
QED

Theorem phi_reorder_one_target_absence[local]:
  reorder_one dfg targets idx op ps = (ops, ps') /\
  MEM at targets /\ at NOTIN FDOM ps.ps_spilled ==>
  at NOTIN FDOM ps'.ps_spilled
Proof
  strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[stackPlanOpsTheory.reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `at NOTIN FDOM ps1.ps_spilled` by
    (drule phi_reorder_restore_absence >>
     disch_then (qspecl_then [`op`, `LENGTH targets`,
       `LENGTH targets - (idx + 1)`] mp_tac) >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op
    (num_ops - (idx + 1)) num_ops ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  pairarg_tac >> simp[] >>
  `at NOTIN FDOM ps2.ps_spilled` by
    (Cases_on `dist > 16` >> gvs[] >>
     drule_all phi_reduce_depth_target_absence >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op
    (num_ops - (idx + 1)) num_ops ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >> simp[]
  >- (IF_CASES_TAC >- (strip_tac >> gvs[]) >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      metis_tac[reorderSimTheory.do_swap_spilled_unchanged, pairTheory.SND]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reorderSimTheory.do_swap_spilled_unchanged, pairTheory.SND]
QED

Theorem phi_reorder_fold_target_absence[local]:
  !xs acc ps ops ps' at.
    FOLDL (\(acc, ps) (idx, op).
      let (step_ops, ps1) = reorder_one dfg targets idx op ps in
      (acc ++ step_ops, ps1)) (acc, ps) xs = (ops, ps') /\
    MEM at targets /\ at NOTIN FDOM ps.ps_spilled ==>
    at NOTIN FDOM ps'.ps_spilled
Proof
  Induct_on `xs` >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule_all phi_reorder_one_target_absence >> strip_tac >>
  gvs[LET_THM] >>
  qpat_x_assum `!acc ps ops ps' at. _` drule_all >> simp[]
QED

Theorem phi_reorder_target_absence:
  reorder_plan dfg targets ps = (ops, ps') /\
  MEM at targets /\ at NOTIN FDOM ps.ps_spilled ==>
  at NOTIN FDOM ps'.ps_spilled
Proof
  rewrite_tac[stackPlanOpsTheory.reorder_plan_def] >>
  MATCH_ACCEPT_TAC phi_reorder_fold_target_absence
QED

Theorem phi_restore_reorder_target_absence:
  restore_spilled_plan targets ps = (restore_ops, ps1) /\
  reorder_plan dfg targets ps1 = (reorder_ops, ps2) /\
  MEM at targets ==>
  at NOTIN FDOM ps2.ps_spilled
Proof
  strip_tac >> drule phi_restore_spilled_domain >> strip_tac >>
  `at NOTIN FDOM ps1.ps_spilled` by simp[] >>
  drule_all phi_reorder_target_absence >> simp[]
QED

Theorem phi_regular_jmp_spills_empty[local]:
  generate_regular_inst_plan liveness dfg cfg fn inst next_live
    halting next_term lbl ps = (ops, ps') /\
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label succ] /\
  inst.inst_outputs = [] /\
  join_target_ops liveness fn lbl inst = SOME targets /\
  (!v. MEM v next_live ==> MEM (Var v) targets) ==>
  ps'.ps_spilled = FEMPTY
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, is_label_operand_def,
       stackPlanOpsTheory.reorder_plan_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def,
       stackModelTheory.stack_pop_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `restore_spilled_plan targets ps = (restore_ops, restored)` >>
  `reorder_plan dfg targets restored = (swap_ops, ps2)` by
    simp[stackPlanOpsTheory.reorder_plan_def] >>
  `!at. MEM at targets ==> at NOTIN FDOM ps2.ps_spilled` by
    metis_tac[phi_restore_reorder_target_absence] >>
  simp[GSYM finite_mapTheory.FDOM_EQ_EMPTY, pred_setTheory.EXTENSION,
       phi_release_dead_spills_domain] >> metis_tac[]
QED

Theorem phi_jmp_plan_spills_empty:
  generate_inst_plan liveness dfg cfg fn inst next_live halting next_term lbl ps =
    SOME (ops, ps') /\ inst.inst_opcode = JMP /\
  inst.inst_operands = [Label succ] /\ inst.inst_outputs = [] /\
  join_target_ops liveness fn lbl inst = SOME targets /\
  (!v. MEM v next_live ==> MEM (Var v) targets) ==>
  ps'.ps_spilled = FEMPTY
Proof
  strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def,
      venomInstTheory.is_param_opcode_def, AllCaseEqs()] >>
  drule_all phi_regular_jmp_spills_empty >> simp[]
QED

Theorem phi_terminal_jmp_spills_empty[local]:
  !insts i ps ops ps'.
    insts <> [] /\ (LAST insts).inst_opcode = JMP /\
    (LAST insts).inst_operands = [Label succ] /\
    (LAST insts).inst_outputs = [] /\
    join_target_ops liveness fn lbl (LAST insts) = SOME targets /\
    (!v. MEM v (live_vars_at liveness lbl block_len) ==> MEM (Var v) targets) /\
    generate_block_insts_plan liveness dfg cfg fn lbl halting n_params
      block_len i insts ps = SOME (ops, ps') ==>
    ps'.ps_spilled = FEMPTY
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> Cases_on `insts = []`
  >- (gvs[generate_block_insts_plan_def, AllCaseEqs()] >>
      metis_tac[phi_jmp_plan_spills_empty]) >>
  simp[generate_block_insts_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[listTheory.LAST_DEF] >>
  first_x_assum irule >> goal_assum drule >> simp[]
QED

Theorem phi_jmp_block_spills_empty:
  generate_block_plan liveness dfg cfg fn pb ps = SOME (ops, ps') /\
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  (LAST pb.bb_instructions).inst_operands = [Label succ] /\
  (LAST pb.bb_instructions).inst_outputs = [] /\
  join_target_ops liveness fn pb.bb_label (LAST pb.bb_instructions) = SOME targets /\
  (!v. MEM v (live_vars_at liveness pb.bb_label (LENGTH pb.bb_instructions)) ==>
       MEM (Var v) targets) ==>
  ps'.ps_spilled = FEMPTY
Proof
  strip_tac >>
  `non_param_insts pb <> [] /\
   LAST (non_param_insts pb) = LAST pb.bb_instructions` by
    (drule_all phi_non_param_jmp_last >> simp[non_param_insts_def]) >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    phi_terminal_jmp_spills_empty >> simp[] >>
  disch_then (qspecl_then [`succ`, `targets`] mp_tac) >> simp[]
QED

Theorem phi_lineage_entry_spills_empty:
  lineage_entry liveness dfg cfg fn ps0 pred succ ps /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  (LAST pb.bb_instructions).inst_operands = [Label target] /\
  (LAST pb.bb_instructions).inst_outputs = [] /\
  join_target_ops liveness fn pb.bb_label (LAST pb.bb_instructions) = SOME targets /\
  (!v. MEM v (live_vars_at liveness pb.bb_label (LENGTH pb.bb_instructions)) ==>
       MEM (Var v) targets) ==>
  ps.ps_spilled = FEMPTY
Proof
  simp[lineage_entry_def] >> rpt strip_tac >> gvs[] >>
  drule_all phi_jmp_block_spills_empty >> simp[]
QED

Theorem phi_cfg_entry_reachable[local]:
  wf_function fn /\ fn_entry_label fn = SOME lbl ==>
  cfg_reachable_of (cfg_analyze fn) lbl
Proof
  simp[fn_entry_label_def, AllCaseEqs()] >> strip_tac >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability >>
  simp[cfg_path_def, relationTheory.RTC_REFL]
QED

Theorem phi_cfg_reachable_successor[local]:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl /\
  MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
  cfg_reachable_of (cfg_analyze fn) succ
Proof
  strip_tac >>
  Cases_on `entry_block fn` >- gvs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def,
        entry_block_def, listTheory.NULL_EQ] >>
  rename1 `entry_block fn = SOME entry` >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability >>
  strip_tac >>
  qpat_assum `!lbl. _` (qspec_then `lbl` assume_tac) >>
  qpat_x_assum `!lbl. _` (qspec_then `succ` mp_tac) >>
  simp[] >> strip_tac >> gvs[cfg_path_def] >>
  irule (cj 2 relationTheory.RTC_RULES_RIGHT1) >>
  qexists_tac `lbl` >> gvs[cfg_path_def]
QED

Theorem phi_lineage_state_reachable:
  !liveness dfg cfg fn ps0 lbl ps.
    lineage_state liveness dfg cfg fn ps0 lbl ps ==>
    wf_function fn /\ cfg = cfg_analyze fn ==>
    cfg_reachable_of (cfg_analyze fn) lbl
Proof
  ntac 5 gen_tac >> ho_match_mp_tac lineage_state_ind >> rpt strip_tac
  >- (drule_all phi_cfg_entry_reachable >> simp[]) >>
  gvs[] >> drule_all phi_cfg_reachable_successor >> simp[]
QED

Theorem phi_join_predecessor_jmp[local]:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1 /\
  MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
  lookup_block pred fn.fn_blocks = SOME pb ==>
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP
Proof
  strip_tac >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    gvs[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label)` >>
     gvs[listTheory.LENGTH_EQ_0] >> decide_tac) >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  gvs[codegen_ready_fn_def, block_entries_ready_def, listTheory.EVERY_MEM] >>
  qpat_x_assum `!b. MEM b fn.fn_blocks ==> _ \/ _`
    (qspec_then `bb` mp_tac) >> simp[] >>
  disch_then (qspec_then `pred` mp_tac) >> simp[listTheory.NULL_EQ]
QED

Theorem phi_ready_jmp_edge_shape[local]:
  codegen_ready_fn fn /\ lookup_block pred fn.fn_blocks = SOME pb /\
  pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) ==>
  (LAST pb.bb_instructions).inst_operands = [Label succ] /\
  (LAST pb.bb_instructions).inst_outputs = [] /\
  cfg_succs_of (cfg_analyze fn) pred = [succ]
Proof
  strip_tac >>
  `MEM pb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `pb.bb_label = pred` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `venomWf$inst_wf (LAST pb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def] >>
     first_x_assum irule >> qexists_tac `pb` >>
     simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  gvs[venomWfTheory.inst_wf_def] >>
  `cfg_succs_of (cfg_analyze fn) pb.bb_label = bb_succs pb` by
    (irule cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
     gvs[codegen_ready_fn_def]) >>
  Cases_on `pb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, is_terminator_def, get_label_def,
      listTheory.nub_def]
QED

Theorem phi_single_successor_live_coverage[local]:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pb.bb_label /\
  lookup_block pb.bb_label fn.fn_blocks = SOME pb /\
  cfg_succs_of (cfg_analyze fn) pb.bb_label = [succ] /\
  lookup_block succ fn.fn_blocks = SOME bb ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) pb.bb_label
                   (LENGTH pb.bb_instructions)) ==>
      MEM v (input_vars_from pb.bb_label bb.bb_instructions
                    (live_vars_at (liveness_analyze fn) succ 0))
Proof
  strip_tac >> drule_all livenessProofsTheory.liveness_convergence >>
  simp[livenessBlockProofsTheory.liveness_instrs_def,
       livenessBlockProofsTheory.liveness_out_def,
       liveness_edge_transfer_def, live_vars_at_def,
       dfHelperDefsTheory.list_union_def, same_vars_def,
       listTheory.EVERY_MEM]
QED

Theorem phi_join_lineage_spills_empty:
  liveness = liveness_analyze fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
  lineage_entry liveness dfg cfg fn ps0 pred bb.bb_label ps ==>
  ps.ps_spilled = FEMPTY
Proof
  strip_tac >> gvs[] >>
  qpat_assum `lineage_entry _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [lineage_entry_def]) >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `pb.bb_label = pred` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `cfg_reachable_of (cfg_analyze fn) pred` by
    (drule phi_lineage_state_reachable >> simp[]) >>
  `pb.bb_instructions <> [] /\ (LAST pb.bb_instructions).inst_opcode = JMP` by
    (drule_all phi_join_predecessor_jmp >> simp[]) >>
  drule_all phi_ready_jmp_edge_shape >> strip_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) pb.bb_label
                (LENGTH pb.bb_instructions)) ==>
       MEM v (input_vars_from pb.bb_label bb.bb_instructions
                (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    (rpt strip_tac >> irule phi_single_successor_live_coverage >> simp[]) >>
  irule phi_lineage_entry_spills_empty >>
  goal_assum (drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
  simp[join_target_ops_def, listTheory.MEM_MAP] >>
  metis_tac[]
QED

Theorem phi_do_dup_spilled[local]:
  !dist ps ops ps'. do_dup dist ps = (ops, ps') ==> ps'.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[stackPlanOpsTheory.do_dup_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem phi_popmany_fold_spilled[local]:
  !xs acc ps.
    (SND (FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
        let (swap_ops, ps') =
          if dist = 0 then ([] : stack_op list, ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack)) (acc, ps) xs)).ps_spilled =
    ps.ps_spilled
Proof
  Induct_on `xs` >- simp[] >> rpt gen_tac >>
  gvs[LET_THM] >> simp[Once listTheory.FOLDL] >>
  Cases_on `stack_get_depth h ps.ps_stack` >- simp[] >> simp[] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  Cases_on `dist = 0` >> simp[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[reorderSimTheory.do_swap_spilled_unchanged, pairTheory.SND]
QED

Theorem phi_do_swap_spilled_result[local]:
  !dist ps ops ps'. do_swap dist ps = (ops, ps') ==> ps'.ps_spilled = ps.ps_spilled
Proof
  rpt strip_tac >>
  qspecl_then [`dist`, `ps`] mp_tac reorderSimTheory.do_swap_spilled_unchanged >>
  simp[]
QED

Theorem phi_popmany_fold_spilled_result[local]:
  !xs acc ps ops ps'.
    FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
        let (swap_ops, ps') =
          if dist = 0 then ([] : stack_op list, ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack)) (acc, ps) xs = (ops, ps') ==>
    ps'.ps_spilled = ps.ps_spilled
Proof
  rpt strip_tac >>
  qspecl_then [`xs`, `acc`, `ps`] mp_tac phi_popmany_fold_spilled >> simp[]
QED

Theorem phi_popmany_spilled:
  !xs ps ops ps'. popmany_plan xs ps = (ops, ps') ==> ps'.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> Cases_on `xs` >> simp[stackPlanOpsTheory.popmany_plan_def,
       stackPlanOpsTheory.popmany_individual_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[SRULE [LET_THM] phi_popmany_fold_spilled_result,
            phi_do_swap_spilled_result]
QED

Theorem phi_plan_spilled_unchanged:
  !inst live halt ps ops ps'.
    generate_phi_plan inst live halt ps = (ops, ps') ==>
    ps'.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[generate_phi_plan_def, LET_THM] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- simp[] >>
  simp[] >> rpt (IF_CASES_TAC >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) live` >> gvs[] >>
  imp_res_tac phi_popmany_spilled >> imp_res_tac phi_do_dup_spilled >> gvs[]
QED
