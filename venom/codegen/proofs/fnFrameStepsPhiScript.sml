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
  allocaRemapSSA fnPlanPrefix removeUnusedSsaProofs

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

Theorem phi_output_normalize_self:
  !fn phi out visited.
    ssa_form fn /\ MEM phi (fn_insts fn) /\ MEM out phi.inst_outputs /\
    phi.inst_opcode = PHI ==>
    normalize_operand (dfg_build_function fn) visited (Var out) = Var out
Proof
  rpt strip_tac >>
  drule_all dfgAnalysisPropsTheory.dfg_build_function_defs_complete >> strip_tac >>
  drule dfgAnalysisPropsTheory.dfg_build_function_correct >> strip_tac >>
  `phi = inst'` by
    (irule allocaRemapSSATheory.ssa_unique_output >> metis_tac[]) >>
  gvs[dfg_get_def_def] >> simp[Once normalize_operand_def]
QED

(* Forward edge selection uses both maps, rather than reversing the exported
   input_vars_from membership theorem. *)
Theorem phi_pair_find_selected[local]:
  !pairs pred v.
    ALL_DISTINCT (MAP FST pairs) /\ MEM (pred,v) pairs ==>
    FIND (\(l,w). l = pred) pairs = SOME (pred,v)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[listTheory.FIND_thm] >> strip_tac >> gvs[] >>
  Cases_on `h0 = pred` >> gvs[] >>
  metis_tac[listTheory.MEM_MAP, pairTheory.FST]
QED

Theorem phi_pair_updates_lookup[local]:
  !pairs m n v.
    FLOOKUP (FOLDL (\m (l,w). m |+ (w,n)) m pairs) v =
    if MEM v (MAP SND pairs) then SOME n else FLOOKUP m v
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[] >> Cases_on `v = h1` >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `MEM v (MAP SND pairs)` >> simp[]
QED

Definition phi_edge_maps_acc_def:
  phi_edge_maps_acc pred n phis acc =
    FOLDL (\(op_map,matching) (j,phi).
      (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,w) => matching |+ (j,w)))
      acc (MAPi (\k phi. (n+k,phi)) phis)
End

Theorem phi_edge_maps_acc_cons[local]:
  phi_edge_maps_acc pred n (phi::phis) (op_map,matching) =
    phi_edge_maps_acc pred (SUC n) phis
      (FOLDL (\m (l,w). m |+ (w,n)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,w) => matching |+ (n,w))
Proof
  simp[phi_edge_maps_acc_def, indexedListsTheory.MAPi_def, combinTheory.o_DEF] >>
  AP_TERM_TAC >> irule indexedListsTheory.MAPi_CONG >> simp[]
QED

Theorem phi_edge_maps_acc_preserves[local]:
  !phis n op_map matching pred v i.
    i < n /\
    EVERY (\phi. ~MEM v (MAP SND (phi_pairs phi.inst_operands))) phis ==>
    FLOOKUP (FST (phi_edge_maps_acc pred n phis (op_map,matching))) v =
      FLOOKUP op_map v /\
    FLOOKUP (SND (phi_edge_maps_acc pred n phis (op_map,matching))) i =
      FLOOKUP matching i
Proof
  Induct >- simp[phi_edge_maps_acc_def] >>
  rpt gen_tac >> simp[phi_edge_maps_acc_cons] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `phi_edge_maps_acc pred (SUC n) phis acc` >>
  `FLOOKUP (FST (phi_edge_maps_acc pred (SUC n) phis acc)) v =
      FLOOKUP (FST acc) v /\
   FLOOKUP (SND (phi_edge_maps_acc pred (SUC n) phis acc)) i =
      FLOOKUP (SND acc) i` by
    (Cases_on `acc` >> simp[] >> first_x_assum irule >> simp[]) >>
  simp[Abbr `acc`, phi_pair_updates_lookup] >>
  Cases_on `FIND (\(l,w). l = pred) (phi_pairs h.inst_operands)`
  >- simp[] >>
  rename1 `_ = SOME pair` >> Cases_on `pair` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >> decide_tac
QED

(* The no-hit branch does not inspect or modify spill ownership. *)
Theorem phi_plan_no_hit:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
    ps.ps_stack = NONE ==>
  generate_phi_plan inst live halting ps = ([], ps)
Proof
  simp[generate_phi_plan_def]
QED

Theorem phi_plan_hit_no_dup:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
    ps.ps_stack = SOME dist /\
  ~MEM (operand_to_string (stack_peek dist ps.ps_stack)) live ==>
  generate_phi_plan inst live halting ps =
    let ret = Var (HD inst.inst_outputs) in
    let p = ps with ps_stack := stack_poke dist ret ps.ps_stack in
    if ~halting /\ ~MEM (HD inst.inst_outputs) live then
      let (pop_ops,p') = popmany_plan [ret] p in
      (SOPoke dist ret :: pop_ops, p')
    else ([SOPoke dist ret], p)
Proof
  simp[generate_phi_plan_def]
QED

(* Value support boundary, including arbitrary resident spill keys. *)
Theorem phi_eval_preserves_lookup:
  !insts s s' v.
    eval_phis s insts = OK s' /\
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts)) ==>
    FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v
Proof
  Induct >- simp[eval_phis_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >- (
    simp[eval_phis_def] >> strip_tac >>
    Cases_on `eval_one_phi s h` >> gvs[] >>
    rename1 `eval_one_phi s h = SOME result` >> PairCases_on `result` >>
    Cases_on `eval_phis s insts` >> gvs[] >>
    `MEM result0 h.inst_outputs` by
      (qpat_x_assum `eval_one_phi _ _ = _` mp_tac >>
       simp[eval_one_phi_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
    `result0 <> v` by metis_tac[] >>
    simp[update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    first_x_assum irule >> simp[]) >>
  simp[eval_phis_def]
QED

(* Persistent residents are protected at both their raw and normalized names. *)
Theorem phi_eval_preserves_frame_operand:
  eval_phis vs insts = OK s_phi /\
  (!v. at = Var v ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts))) ==>
  operand_val (frame_view fn ra s_phi) lo at =
    operand_val (frame_view fn ra vs) lo at
Proof
  strip_tac >> Cases_on `at` >>
  simp[operand_val_def, frame_view_vars_lookup] >>
  AP_TERM_TAC >> irule phi_eval_preserves_lookup >>
  qexists_tac `insts` >> simp[]
QED

Theorem phi_eval_preserves_frame_alias:
  eval_phis vs insts = OK s_phi /\
  (!v. at = Var v \/ normalize_operand dfg [] at = Var v ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts))) /\
  operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at) ==>
  operand_val (frame_view fn ra s_phi) lo at =
    operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)
Proof
  strip_tac >>
  `operand_val (frame_view fn ra s_phi) lo at =
   operand_val (frame_view fn ra vs) lo at` by
    (irule phi_eval_preserves_frame_operand >> qexists_tac `insts` >>
     simp[] >> metis_tac[]) >>
  `operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at) =
   operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)` by
    (irule phi_eval_preserves_frame_operand >> qexists_tac `insts` >>
     simp[] >> metis_tac[]) >> simp[]
QED

Theorem phi_spilled_fresh:
  !base ps insts pred dfg at v.
  generated_plan_state_wf_marked base ps /\
  (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    ~(MEM op ps.ps_stack /\
      ?inst. MEM inst (collect_phis insts) /\
             resolve_phi pred inst.inst_operands = SOME op) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts))) /\
  at IN FDOM ps.ps_spilled /\
  (at = Var v \/ normalize_operand dfg [] at = Var v) ==>
  ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts))
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM at ps.ps_stack` by
    (gvs[generated_plan_state_wf_marked_def, pred_setTheory.IN_DISJOINT] >>
     metis_tac[]) >>
  first_x_assum irule >> qexists_tac `at` >> simp[]
QED

(* ===== The PHI prefix from any entry stack ===== *)

(* phi_prefix_frame_sim without the join-entry facts: it assumes only that
   every variable operand of a PHI on the entry stack is the operand
   resolve_phi selects for the edge taken, so each PHI's stack hit (the
   shallowest of its variable operands, which generate_phi_plan pokes) is
   that operand, also after earlier PHIs' pokes and dead-output pops have
   reordered the stack (a premise on the entry hits alone does not survive
   a pop's swap).  A PHI with no hit (its operand spilled, say) gets no
   code and no slot.  The join case (fnFrameSteps) and the
   single-predecessor case both derive that from their entry stacks.

   Why it should hold: each PHI pokes its hit's slot with its output
   (phi_block_ready: no PHI operand is live past the prefix, so the dup
   branch never runs), and a dead output is popped.  No PHI reads another
   PHI output of the same block (it would then be live past the prefix),
   so the hits stay the same while the prefix runs and the sequential code
   agrees with eval_phis.  The freshness premise keeps every other stack
   or spill entry's value, and its root's, unchanged by eval_phis; only a
   stack entry the prefix consumes (a PHI operand selected from pred) is
   exempt, since its slot is poked.  A spilled pred-edge operand is not
   exempt: it stays in the spill map, and its root may be another PHI's
   output. *)
Theorem phi_prefix_hits_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg fn bb pred base ps vs as s_phi phis
   body ops ps3 r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    vs.vs_prev_bb = SOME pred /\
    (!inst op.
       MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
       MEM op ps.ps_stack ==>
       resolve_phi pred inst.inst_operands = SOME op) /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
       ~(MEM op ps.ps_stack /\
         ?inst. MEM inst (collect_phis bb.bb_instructions) /\
                resolve_phi pred inst.inst_operands = SOME op) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops)
    ==>
    ?phi_ops ps1 body_ops n as'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps =
        SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 =
        SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at))
Proof
  cheat
QED

(* ===== PHI hits at a join's entry stack ===== *)

(* resolve_phi on well-formed PHI operands is the first matching pair. *)
Theorem phi_resolve_find_pairs[local]:
  !ops pred.
    phi_well_formed ops ==>
    resolve_phi pred ops =
      case FIND (\(l,w). l = pred) (phi_pairs ops) of
        NONE => NONE
      | SOME (_,w) => SOME (Var w)
Proof
  ho_match_mp_tac venomInstTheory.phi_pairs_ind >>
  rw[venomInstTheory.phi_pairs_def, venomWfTheory.phi_well_formed_def,
     resolve_phi_def, listTheory.FIND_thm] >> rw[]
QED

Theorem phi_edge_maps_acc_op_none[local]:
  !phis n om m pred v.
    FLOOKUP (FST (phi_edge_maps_acc pred n phis (om,m))) v = NONE ==>
    FLOOKUP om v = NONE /\
    EVERY (\phi. ~MEM v (MAP SND (phi_pairs phi.inst_operands))) phis
Proof
  Induct >- simp[phi_edge_maps_acc_def] >>
  rpt gen_tac >> simp[phi_edge_maps_acc_cons] >> strip_tac >>
  first_x_assum drule >> simp[phi_pair_updates_lookup] >>
  rw[] >> gvs[]
QED

Theorem phi_edge_maps_acc_matching[local]:
  !phis n om m pred i.
    FLOOKUP (SND (phi_edge_maps_acc pred n phis (om,m))) i =
      if n <= i /\ i < n + LENGTH phis then
        (case FIND (\(l,w). l = pred)
                (phi_pairs (EL (i - n) phis).inst_operands) of
           NONE => FLOOKUP m i
         | SOME (_,w) => SOME w)
      else FLOOKUP m i
Proof
  Induct >- simp[phi_edge_maps_acc_def] >>
  rpt gen_tac >> simp[phi_edge_maps_acc_cons] >>
  Cases_on `FIND (\(l,w). l = pred) (phi_pairs h.inst_operands)` >>
  TRY (rename1 `SOME pr` >> PairCases_on `pr`) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `i = n` >> simp[] >>
  Cases_on `n < i` >> simp[] >>
  `i - n = SUC (i - SUC n)` by decide_tac >>
  `LENGTH phis + SUC n = n + SUC (LENGTH phis)` by decide_tac >> simp[]
QED

Theorem phi_build_maps_acc[local]:
  !pred phis.
    build_phi_maps pred phis = phi_edge_maps_acc pred 0 phis (FEMPTY,FEMPTY)
Proof
  simp[build_phi_maps_def, phi_edge_maps_acc_def, LET_THM] >>
  rpt gen_tac >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >> rw[] >>
  BasicProvers.every_case_tac >> simp[]
QED

Theorem phi_input_vars_fold_mem[local]:
  !base acc placed op_map matching y.
    MEM y (FST (FOLDL (\(acc,placed) v.
        case FLOOKUP op_map v of
          SOME phi_idx =>
            if MEM phi_idx placed then (acc,placed)
            else
              (case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v],phi_idx::placed)
               | NONE => (acc,placed))
        | NONE => (acc ++ [v],placed)) (acc,placed) base)) ==>
    MEM y acc \/ (FLOOKUP op_map y = NONE /\ MEM y base) \/
    ?i. FLOOKUP matching i = SOME y
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `FLOOKUP op_map h = SOME j` >>
  Cases_on `MEM j placed` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `FLOOKUP matching j` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]
QED

(* A variable the join entry stack holds is either no PHI's operand, or
   the operand some PHI selects for the edge from pred. *)
Theorem phi_input_vars_from_mem[local]:
  !pred instrs live y.
    MEM y (input_vars_from pred instrs live) /\
    ~NULL (collect_phis instrs) ==>
    EVERY (\phi. ~MEM y (MAP SND (phi_pairs phi.inst_operands)))
      (collect_phis instrs) \/
    ?i. i < LENGTH (collect_phis instrs) /\
        FIND (\(l,w). l = pred)
          (phi_pairs (EL i (collect_phis instrs)).inst_operands) =
          SOME (pred,y)
Proof
  rpt gen_tac >> simp[input_vars_from_def, LET_THM, phi_build_maps_acc] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  qspecl_then [`live`, `[]`, `[]`, `op_map`, `matching`, `y`] mp_tac
    phi_input_vars_fold_mem >>
  gvs[] >> strip_tac
  >- (disj1_tac >>
      qspecl_then [`collect_phis instrs`, `0`, `FEMPTY`, `FEMPTY`, `pred`, `y`]
        mp_tac phi_edge_maps_acc_op_none >> gvs[]) >>
  disj2_tac >> qexists_tac `i` >>
  qspecl_then [`collect_phis instrs`, `0`, `FEMPTY`, `FEMPTY`, `pred`, `i`]
    mp_tac phi_edge_maps_acc_matching >>
  gvs[] >> rw[] >> gvs[AllCaseEqs()] >>
  drule stackPlanGenTheory.FIND_SOME_MEM >> simp[pairTheory.ELIM_UNCURRY] >>
  rename1 `FIND _ _ = SOME pr` >> PairCases_on `pr` >> simp[]
QED

Theorem phi_pairs_mem_var_operand[local]:
  !ops l v. MEM (l,v) (phi_pairs ops) ==> MEM (Var v) ops
Proof
  ho_match_mp_tac venomInstTheory.phi_pairs_ind >>
  rw[venomInstTheory.phi_pairs_def] >> metis_tac[]
QED

Theorem phi_operand_vars_mem[local]:
  !ops v. MEM v (venomInst$operand_vars ops) <=> MEM (Var v) ops
Proof
  Induct >> simp[venomInstTheory.operand_vars_def] >>
  Cases >> simp[venomInstTheory.operand_var_def] >> metis_tac[]
QED

Theorem phi_uses_disjoint_el[local]:
  !l i k v.
    phi_uses_disjoint l /\ i < LENGTH l /\ k < LENGTH l /\ i <> k /\
    MEM (Var v) (EL i l).inst_operands ==>
    ~MEM (Var v) (EL k l).inst_operands
Proof
  Induct >> simp[] >> rpt gen_tac >> simp[phi_uses_disjoint_def] >>
  strip_tac >> Cases_on `i` >> Cases_on `k` >> gvs[]
  >- (gvs[listTheory.EVERY_MEM, inst_uses_def, phi_operand_vars_mem] >>
      metis_tac[listTheory.EL_MEM])
  >- (gvs[listTheory.EVERY_MEM, inst_uses_def, phi_operand_vars_mem] >>
      metis_tac[listTheory.EL_MEM]) >>
  metis_tac[]
QED

(* At a join's entry stack (lineage_entry_join_stack's shape), each PHI's
   hit is the operand resolve_phi selects for the edge from pred. *)
Theorem phi_join_stack_hit:
  !pred instrs live pre inst op.
    phi_uses_disjoint (collect_phis instrs) /\
    EVERY (\phi. phi_well_formed phi.inst_operands) (collect_phis instrs) /\
    MEM inst (collect_phis instrs) /\
    EVERY (\op. op = dead_stack_marker) pre /\
    is_var_operand op /\ MEM op inst.inst_operands /\
    MEM op (pre ++ MAP Var (input_vars_from pred instrs live)) ==>
    resolve_phi pred inst.inst_operands = SOME op
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM op pre` by
    (strip_tac >> gvs[listTheory.EVERY_MEM] >> res_tac >>
     gvs[dead_stack_marker_def, is_var_operand_def]) >>
  Cases_on `op` >> gvs[is_var_operand_def] >> rename1 `Var y` >>
  `MEM y (input_vars_from pred instrs live)` by gvs[listTheory.MEM_MAP] >>
  `~NULL (collect_phis instrs)` by (Cases_on `collect_phis instrs` >> gvs[]) >>
  drule_all phi_input_vars_from_mem >> strip_tac
  >- (gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
      `phi_well_formed inst.inst_operands` by metis_tac[] >>
      drule_all venomWfTheory.phi_well_formed_var_pair >> strip_tac >>
      metis_tac[pairTheory.SND]) >>
  `?k. k < LENGTH (collect_phis instrs) /\ inst = EL k (collect_phis instrs)`
    by metis_tac[listTheory.MEM_EL] >>
  drule stackPlanGenTheory.FIND_SOME_MEM >> strip_tac >>
  drule phi_pairs_mem_var_operand >> strip_tac >>
  Cases_on `i = k`
  >- (gvs[] >>
      `phi_well_formed (EL i (collect_phis instrs)).inst_operands` by
        gvs[listTheory.EVERY_EL] >>
      gvs[phi_resolve_find_pairs]) >>
  metis_tac[phi_uses_disjoint_el]
QED

Theorem phi_prefix_is_collect_phis[local]:
  !phis body.
    LENGTH phis = phi_prefix_length (phis ++ body) ==>
    phis = collect_phis (phis ++ body)
Proof
  Induct
  >- (Cases >> simp[phi_prefix_length_def, collect_phis_def] >> rw[]) >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def, collect_phis_def]
QED

Theorem phi_non_entry_non_param_insts[local]:
  !fn bb.
    canonical_param_prefix fn /\ MEM bb fn.fn_blocks /\
    bb <> HD fn.fn_blocks ==>
    non_param_insts bb = bb.bb_instructions
Proof
  rpt strip_tac >>
  Cases_on `fn.fn_blocks` >>
  gvs[callLayoutDefsTheory.canonical_param_prefix_def,
      listTheory.EVERY_MEM, callLayoutDefsTheory.no_param_insts_def,
      non_param_insts_def] >>
  simp[listTheory.FILTER_EQ_ID, listTheory.EVERY_MEM] >> metis_tac[]
QED

(* The hits premise of phi_prefix_hits_frame_sim at a join's lineage
   entry. *)
Theorem phi_join_entry_hits:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred bb lbl ps_l h
   promised ps phis body.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions ==>
    !inst op.
      MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
      MEM op ps.ps_stack ==>
      resolve_phi pred inst.inst_operands = SOME op
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `non_param_insts bb = bb.bb_instructions` by
    metis_tac[phi_non_entry_non_param_insts, codegen_ready_fn_def] >>
  `phis = collect_phis bb.bb_instructions` by
    metis_tac[phi_prefix_is_collect_phis] >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `fn`, `ch`, `growth`, `spill_base`,
               `lbl_ctr`, `pred`, `bb`, `ps_l`]
    mp_tac fnPlanLineageJoinTheory.lineage_entry_join_stack >>
  impl_tac >- gvs[] >> strip_tac >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    metis_tac[phi_codegen_uses_disjoint] >>
  `EVERY (\phi. phi_well_formed phi.inst_operands)
     (collect_phis bb.bb_instructions)` by (
    simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
    `phi.inst_opcode = PHI /\ MEM phi bb.bb_instructions` by
      (qpat_x_assum `MEM phi _` mp_tac >>
       qspec_tac (`bb.bb_instructions`, `l`) >>
       Induct >> rw[collect_phis_def] >> gvs[]) >>
    `inst_wf phi` by
      metis_tac[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def] >>
    gvs[venomWfTheory.inst_wf_def]) >>
  rpt gen_tac >> strip_tac >>
  irule phi_join_stack_hit >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bb.bb_instructions`, `live_vars_at liveness bb.bb_label 0`,
                `pre`] >>
  gvs[]
QED

(* At a join's lineage entry nothing is spilled: every spill-map key is a
   variable live out of pred (lineage_entry_inventory), pred's live-out
   is input_vars_from pred (single_successor_exit_live), which the JMP's
   plan leaves on the stack (successful_block_jmp_suffix), and
   generated_plan_state_wf_marked keeps stack and spill map disjoint. *)
Theorem phi_join_entry_spill_empty:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps ==>
    ps.ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_assum `lineage_entry _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [lineage_entry_def]) >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  drule_all (SRULE [] fnLineageInvTheory.lineage_entry_inventory) >>
  strip_tac >>
  drule_all fnPlanLineageJoinTheory.join_predecessor_jmp_shape >> strip_tac >>
  drule_all fnPlanLineageJoinTheory.join_predecessor_single_successor >>
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all fnPlanLineageJoinTheory.lineage_state_reachable >> strip_tac >>
  drule_all fnPlanLineageJoinTheory.successful_block_jmp_suffix >> strip_tac >>
  gvs[] >>
  simp[GSYM finite_mapTheory.FDOM_EQ_EMPTY, pred_setTheory.EXTENSION] >>
  rpt strip_tac >>
  `?v. x = Var v /\
       MEM v (live_vars_at (liveness_analyze fn) pb.bb_label
                (LENGTH pb.bb_instructions))` by
    (qpat_x_assum `!op. _ ==> ?v. _` irule >> metis_tac[]) >>
  `MEM v (input_vars_from pb.bb_label bb.bb_instructions
            (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    (irule fnPlanLineageJoinTheory.single_successor_exit_live >>
     asm_rewrite_tac[] >> qexists_tac `pb` >> asm_rewrite_tac[]) >>
  gvs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
      pred_setTheory.IN_DISJOINT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* The PHI prefix's narrowed freshness at a join's lineage entry, from the
   coarse one: with nothing spilled, an exempt entry is a stack operand of
   some PHI, which phi_join_entry_hits makes the pred-selected one. *)
Theorem phi_join_entry_fresh:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred bb lbl ps_l h
   promised ps phis body.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) ==>
    !op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
       ~(MEM op ps.ps_stack /\
         ?inst. MEM inst (collect_phis bb.bb_instructions) /\
                resolve_phi pred inst.inst_operands = SOME op) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`liveness`, `dfg`, `cfg`, `fn`, `ch`, `growth`, `spill_base`,
               `lbl_ctr`, `pred`, `bb`, `lbl`, `ps_l`, `h`, `promised`, `ps`,
               `phis`, `body'`]
    mp_tac phi_join_entry_hits >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `non_param_insts bb = bb.bb_instructions` by
    metis_tac[phi_non_entry_non_param_insts, codegen_ready_fn_def] >>
  `phis = collect_phis bb.bb_instructions` by
    metis_tac[phi_prefix_is_collect_phis] >>
  `ps_l.ps_spilled = FEMPTY` by
    (irule phi_join_entry_spill_empty >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `MEM op ps.ps_stack` by gvs[] >>
  `?s. op = Var s` by (Cases_on `op` >> gvs[normalize_operand_def]) >>
  qpat_x_assum `op = Var _` SUBST_ALL_TAC >>
  `~MEM (Var s) (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions)))` by
    (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> rpt strip_tac >>
     gvs[] >> metis_tac[is_var_operand_def]) >>
  metis_tac[]
QED


(* Boundary probe: a well-formed PHI edge forces reachability, even though
   lookup of an arbitrary block alone does not. *)
Theorem phi_edge_operand_reachable:
  !fn bb inst v.
    phi_edge_uses_wf fn bb inst /\ MEM (Var v) inst.inst_operands ==>
    fn_reachable fn bb.bb_label
Proof
  rpt gen_tac >> simp[venomWfTheory.phi_edge_uses_wf_def] >> strip_tac >>
  drule_all venomWfTheory.phi_well_formed_var_pair >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[venomWfTheory.def_available_at_def, venomWfTheory.fn_dominates_def] >>
  gvs[venomWfTheory.fn_reachable_def] >>
  metis_tac[relationTheory.RTC_RULES_RIGHT1]
QED

Theorem phi_path_first_prefix[local]:
  !path fn target.
    is_fn_path fn path /\ MEM target path ==>
    ?pre. is_fn_path fn (pre ++ [target]) /\
      HD (pre ++ [target]) = HD path /\ ~MEM target pre
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (head::tail)` >> strip_tac >>
  Cases_on `head = target`
  >- (qexists_tac `[]` >> simp[venomWfTheory.is_fn_path_def]) >>
  `is_fn_path fn tail /\ MEM target tail` by
    (Cases_on `tail` >> gvs[venomWfTheory.is_fn_path_def]) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `head::pre` >> simp[] >>
  Cases_on `tail` >- gvs[] >>
  Cases_on `pre` >> gvs[venomWfTheory.is_fn_path_def]
QED

Theorem phi_rtc_path[local]:
  !fn x y. RTC (fn_cfg_edge fn) x y ==>
    ?path. is_fn_path fn path /\ path <> [] /\ HD path = x /\ LAST path = y
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> rpt strip_tac
  >- (qexists_tac `[x]` >> simp[venomWfTheory.is_fn_path_def]) >>
  qexists_tac `x::path` >> Cases_on `path` >>
  gvs[venomWfTheory.is_fn_path_def]
QED

Theorem phi_path_snoc_edge[local]:
  !path fn target.
    path <> [] /\ is_fn_path fn (path ++ [target]) ==>
    is_fn_path fn path /\ fn_cfg_edge fn (LAST path) target
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn ((head::tail) ++ [target])` >>
  Cases_on `tail` >- simp[venomWfTheory.is_fn_path_def] >>
  rename1 `is_fn_path fn ((head::next::rest) ++ [target])` >> strip_tac >>
  `is_fn_path fn ((next::rest) ++ [target])` by
    gvs[venomWfTheory.is_fn_path_def] >>
  first_x_assum (qspecl_then [`fn`, `target`] mp_tac) >> simp[] >>
  strip_tac >> Cases_on `rest` >> gvs[venomWfTheory.is_fn_path_def]
QED

Theorem phi_first_entry_path[local]:
  !fn target.
    fn_reachable fn target /\ fn_entry_label fn <> SOME target ==>
    ?path. is_fn_path fn path /\ path <> [] /\
      fn_entry_label fn = SOME (HD path) /\ ~MEM target path /\
      fn_cfg_edge fn (LAST path) target
Proof
  rpt gen_tac >> simp[venomWfTheory.fn_reachable_def] >> strip_tac >>
  drule phi_rtc_path >> strip_tac >>
  `MEM target path` by metis_tac[rich_listTheory.MEM_LAST_NOT_NIL] >>
  drule_all phi_path_first_prefix >> strip_tac >>
  `pre <> []` by (strip_tac >> gvs[]) >>
  drule_all phi_path_snoc_edge >> strip_tac >>
  qexists_tac `pre` >> Cases_on `pre` >> gvs[]
QED

Theorem phi_first_edge_fresh[local]:
  !fn bb inst path p u.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    phi_edge_uses_wf fn bb inst /\ MEM (p,u) (phi_pairs inst.inst_operands) /\
    is_fn_path fn path /\ path <> [] /\
    fn_entry_label fn = SOME (HD path) /\ LAST path = p /\
    ~MEM bb.bb_label path ==>
    ~MEM u (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `phi_edge_uses_wf _ _ _`
    (strip_assume_tac o REWRITE_RULE [venomWfTheory.phi_edge_uses_wf_def]) >>
  first_x_assum drule >> strip_tac >>
  gvs[venomWfTheory.def_available_at_def] >>
  `def_bb = bb` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[removeUnusedSsaProofsTheory.ssa_unique_output_block]) >>
  gvs[venomWfTheory.fn_dominates_def] >>
  first_x_assum (qspec_then `path` mp_tac) >> simp[]
QED

Theorem phi_reachable_entry_representative[local]:
  !fn bb inst.
    ssa_form fn /\ MEM bb fn.fn_blocks /\ phi_edge_uses_wf fn bb inst /\
    fn_reachable fn bb.bb_label /\ fn_entry_label fn <> SOME bb.bb_label ==>
    ?p u. MEM (p,u) (phi_pairs inst.inst_operands) /\
      ~MEM u (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> drule_all phi_first_entry_path >> strip_tac >>
  `?u. MEM (LAST path,u) (phi_pairs inst.inst_operands)` by
    (fs[venomWfTheory.phi_edge_uses_wf_def] >>
     metis_tac[pairTheory.PAIR]) >>
  `~MEM u (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    (irule phi_first_edge_fresh >> goal_assum drule >>
     qexistsl_tac [`inst`, `LAST path`, `path`] >> simp[]) >>
  metis_tac[]
QED

Theorem phi_codegen_edge_wf[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst (collect_phis bb.bb_instructions) ==>
  phi_edge_uses_wf fn bb inst
Proof
  strip_tac >> drule livenessProofsTheory.collect_phis_mem >> strip_tac >>
  gvs[codegen_ready_fn_def, venomWfTheory.def_dominates_uses_def] >>
  metis_tac[]
QED

Theorem phi_codegen_has_incoming[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst (collect_phis bb.bb_instructions) ==>
  ?p u. MEM (p,u) (phi_pairs inst.inst_operands)
Proof
  strip_tac >>
  `phi_edge_uses_wf fn bb inst` by metis_tac[phi_codegen_edge_wf] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `~(LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <= 1)` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, listTheory.EVERY_MEM] >>
     metis_tac[listTheory.NULL_EQ, listTheory.MEM]) >>
  `?p. MEM p (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> gvs[] >>
     metis_tac[]) >>
  `MEM p (fn_labels fn)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_pred_labels] >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = p` by
    (gvs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM bb.bb_label (bb_succs pb)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond,
              cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs] >>
  `fn_cfg_edge fn p bb.bb_label` by
    (simp[venomWfTheory.fn_cfg_edge_def] >> metis_tac[]) >>
  fs[venomWfTheory.phi_edge_uses_wf_def] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem phi_entry_representative:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  ?p u. MEM (p,u) (phi_pairs phi.inst_operands) /\
    ~MEM u (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  strip_tac >>
  `phi_edge_uses_wf fn bb phi` by metis_tac[phi_codegen_edge_wf] >>
  `?p u. MEM (p,u) (phi_pairs phi.inst_operands)` by
    metis_tac[phi_codegen_has_incoming] >>
  `fn_reachable fn bb.bb_label` by
    (irule phi_edge_operand_reachable >> qexistsl_tac [`phi`, `u`] >>
     metis_tac[phi_pairs_mem_var_operand]) >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def,
         venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
         fn_labels_def] >> strip_tac >>
     `MEM (HD fn.fn_blocks) fn.fn_blocks` by
       (Cases_on `fn.fn_blocks` >> gvs[]) >>
     Cases_on `fn.fn_blocks` >> gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
  irule phi_reachable_entry_representative >>
  qexists_tac `fn` >> simp[] >> gvs[codegen_ready_fn_def]
QED

Theorem phi_unkilled_use_live_entry[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst (collect_phis bb.bb_instructions) /\
  MEM (Var u) inst.inst_operands /\
  ~MEM u (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
  MEM u (live_vars_at (liveness_analyze fn) bb.bb_label 0)
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `phi_edge_uses_wf fn bb inst` by metis_tac[phi_codegen_edge_wf] >>
  `fn_reachable fn bb.bb_label` by metis_tac[phi_edge_operand_reachable] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def, fn_labels_def]) >>
  `MEM inst bb.bb_instructions` by
    metis_tac[livenessProofsTheory.collect_phis_mem] >>
  `?idx. idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst` by
    metis_tac[listTheory.MEM_EL] >>
  `MEM u (inst_uses inst)` by
    metis_tac[removeUnusedSsaProofsTheory.operand_var_in_inst_uses] >>
  `MEM u (live_vars_at (liveness_analyze fn) bb.bb_label idx)` by
    (irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_uses) >>
     goal_assum drule >> simp[]) >>
  irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
  goal_assum drule >> simp[] >> qexists_tac `idx` >> simp[] >>
  rpt strip_tac >>
  `k < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM (EL k bb.bb_instructions) bb.bb_instructions` by
    simp[listTheory.EL_MEM] >>
  qpat_x_assum `~MEM u (FLAT _)` mp_tac >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[venomInstTheory.inst_defs_def]
QED

Theorem phi_live_entry_representative:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) ==>
  ?p u. MEM (p,u) (phi_pairs phi.inst_operands) /\
    MEM u (live_vars_at (liveness_analyze fn) bb.bb_label 0)
Proof
  strip_tac >> drule_all phi_entry_representative >> strip_tac >>
  qexistsl_tac [`p`, `u`] >> simp[] >>
  irule phi_unkilled_use_live_entry >> goal_assum drule >> simp[] >>
  qexists_tac `phi` >> simp[] >> metis_tac[phi_pairs_mem_var_operand]
QED

Theorem phi_input_vars_fold_covers[local]:
  !base acc placed op_map matching u i y.
    FLOOKUP (op_map : (string,num) fmap) u = SOME i /\
    FLOOKUP (matching : (num,string) fmap) i = SOME y /\
    (MEM i placed ==> MEM y acc) /\ (MEM u base \/ MEM y acc) ==>
    MEM y (FST (FOLDL (\(acc,placed) v.
      case FLOOKUP op_map v of
        SOME j => if MEM j placed then (acc,placed)
          else (case FLOOKUP matching j of
                  SOME w => (acc ++ [w],j::placed)
                | NONE => (acc,placed))
      | NONE => (acc ++ [v],placed)) (acc,placed) base))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  (Cases_on `FLOOKUP op_map h` >> simp[]
   >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
   rename1 `FLOOKUP op_map h = SOME j` >>
   Cases_on `MEM j placed` >> simp[]
   >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
   Cases_on `FLOOKUP matching j` >> simp[]
   >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
   first_x_assum irule >> qexistsl_tac [`i`, `u`] >>
   Cases_on `i = j` >> gvs[] >> metis_tac[])
QED

Theorem phi_edge_maps_acc_slot[local]:
  !phis n om m pred i u.
    i < LENGTH phis /\
    MEM u (MAP SND (phi_pairs (EL i phis).inst_operands)) /\
    (!k. k < LENGTH phis /\ k <> i ==>
      ~MEM u (MAP SND (phi_pairs (EL k phis).inst_operands))) ==>
    FLOOKUP (FST (phi_edge_maps_acc pred n phis (om,m))) u = SOME (n+i)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i`
  >- (gvs[] >> simp[phi_edge_maps_acc_cons] >>
      qmatch_goalsub_abbrev_tac `phi_edge_maps_acc pred (SUC n) phis acc` >>
      `EVERY (\phi. ~MEM u (MAP SND (phi_pairs phi.inst_operands))) phis` by
        (simp[listTheory.EVERY_MEM] >> qx_gen_tac `phi` >> strip_tac >>
         `?k. k < LENGTH phis /\ EL k phis = phi` by metis_tac[listTheory.MEM_EL] >>
         first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]) >>
      `FLOOKUP (FST (phi_edge_maps_acc pred (SUC n) phis acc)) u =
       FLOOKUP (FST acc) u` by
        (Cases_on `acc` >> simp[] >>
         irule (cj 1 phi_edge_maps_acc_preserves) >> simp[] >> qexists_tac `n` >> simp[]) >>
      simp[Abbr `acc`, phi_pair_updates_lookup]) >>
  rename1 `SUC j < LENGTH (h::phis)` >>
  simp[phi_edge_maps_acc_cons] >>
  qmatch_goalsub_abbrev_tac `phi_edge_maps_acc pred (SUC n) phis acc` >>
  `SUC n + j = n + SUC j` by decide_tac >>
  pop_assum (SUBST1_TAC o SYM) >>
  Cases_on `acc` >> first_x_assum irule >> gvs[] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]
QED

Theorem phi_input_vars_slot[local]:
  MEM u live /\
  FLOOKUP (FST (build_phi_maps pred (collect_phis instrs))) u = SOME i /\
  FLOOKUP (SND (build_phi_maps pred (collect_phis instrs))) i = SOME y ==>
  MEM y (input_vars_from pred instrs live)
Proof
  strip_tac >> Cases_on `collect_phis instrs = []`
  >- gvs[build_phi_maps_def] >>
  simp[input_vars_from_def, LET_THM, listTheory.NULL_EQ] >> pairarg_tac >> gvs[] >>
  pure_rewrite_tac[pairTheory.UNCURRY] >> simp[] >>
  irule phi_input_vars_fold_covers >> qexistsl_tac [`i`, `u`] >> simp[]
QED

Theorem phi_input_vars_from_covered[local]:
  phi_uses_disjoint (collect_phis instrs) /\
  i < LENGTH (collect_phis instrs) /\
  MEM (p,v) (phi_pairs (EL i (collect_phis instrs)).inst_operands) /\
  ALL_DISTINCT (MAP FST (phi_pairs (EL i (collect_phis instrs)).inst_operands)) /\
  MEM u live /\
  MEM u (MAP SND (phi_pairs (EL i (collect_phis instrs)).inst_operands)) ==>
  MEM v (input_vars_from p instrs live)
Proof
  strip_tac >>
  `FLOOKUP (FST (build_phi_maps p (collect_phis instrs))) u = SOME i` by
    (simp[phi_build_maps_acc] >>
     `0 + i = i` by simp[] >> pop_assum (SUBST1_TAC o SYM) >>
     irule phi_edge_maps_acc_slot >> simp[] >> rpt strip_tac >>
     `MEM (Var u) (EL i (collect_phis instrs)).inst_operands` by
       (gvs[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
        metis_tac[phi_pairs_mem_var_operand]) >>
     `i <> k` by decide_tac >>
     drule_all phi_uses_disjoint_el >>
     gvs[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
     metis_tac[phi_pairs_mem_var_operand]) >>
  `FIND (\(l,w). l = p)
    (phi_pairs (EL i (collect_phis instrs)).inst_operands) = SOME (p,v)` by
    metis_tac[phi_pair_find_selected] >>
  `FLOOKUP (SND (build_phi_maps p (collect_phis instrs))) i = SOME v` by
    simp[phi_build_maps_acc, phi_edge_maps_acc_matching] >>
  irule phi_input_vars_slot >> qexistsl_tac [`i`, `u`] >> simp[]
QED

Theorem phi_selected_input_vars:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\
  MEM (p,v) (phi_pairs phi.inst_operands) ==>
  MEM v (input_vars_from p bb.bb_instructions
    (live_vars_at (liveness_analyze fn) bb.bb_label 0))
Proof
  strip_tac >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    metis_tac[phi_codegen_uses_disjoint] >>
  `phi_edge_uses_wf fn bb phi` by metis_tac[phi_codegen_edge_wf] >>
  `ALL_DISTINCT (MAP FST (phi_pairs phi.inst_operands))` by
    gvs[venomWfTheory.phi_edge_uses_wf_def] >>
  drule_all phi_live_entry_representative >> strip_tac >>
  `?i. i < LENGTH (collect_phis bb.bb_instructions) /\
       EL i (collect_phis bb.bb_instructions) = phi` by
    metis_tac[listTheory.MEM_EL] >>
  irule phi_input_vars_from_covered >> simp[] >> qexistsl_tac [`i`, `u`] >>
  simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem phi_pair_live_out:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\
  MEM (p,v) (phi_pairs phi.inst_operands) /\
  lookup_block p fn.fn_blocks = SOME pb ==>
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `phi_edge_uses_wf fn bb phi` by metis_tac[phi_codegen_edge_wf] >>
  `fn_reachable fn p /\ fn_cfg_edge fn p bb.bb_label` by
    (qpat_x_assum `phi_edge_uses_wf _ _ _`
       (strip_assume_tac o REWRITE_RULE [venomWfTheory.phi_edge_uses_wf_def]) >>
     first_x_assum drule >> strip_tac >>
     gvs[venomWfTheory.def_available_at_def, venomWfTheory.fn_dominates_def] >>
     metis_tac[]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `cfg_reachable_of (cfg_analyze fn) p` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def, fn_labels_def]) >>
  `MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) p)` by
    (gvs[venomWfTheory.fn_cfg_edge_def] >>
     metis_tac[cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs]) >>
  drule_all livenessConvergenceProofsTheory.liveness_recompute_edge_subset >>
  simp[livenessBlockProofsTheory.liveness_instrs_def, liveness_edge_transfer_def,
       pred_setTheory.SUBSET_DEF] >> strip_tac >>
  simp[liveness_analyze_def, live_vars_at_def] >> first_x_assum irule >>
  drule_all phi_selected_input_vars >>
  simp[liveness_analyze_def, live_vars_at_def]
QED

Theorem phi_unkilled_exit_live[local]:
  wf_function fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)) /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions)) /\ i <= LENGTH bb.bb_instructions ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)
Proof
  strip_tac >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
  goal_assum drule >> simp[] >> qexists_tac `LENGTH bb.bb_instructions` >>
  simp[] >> rpt strip_tac >>
  `MEM (EL k bb.bb_instructions) bb.bb_instructions` by simp[listTheory.EL_MEM] >>
  qpat_x_assum `~MEM v (FLAT _)` mp_tac >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[venomInstTheory.inst_defs_def]
QED

Theorem phi_live_out_backward_edge:
  codegen_ready_fn fn /\ fn_reachable fn p /\ fn_cfg_edge fn p q /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block q fn.fn_blocks = SOME qb /\
  ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) qb.bb_instructions)) /\
  MEM v (live_vars_at (liveness_analyze fn) q (LENGTH qb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `qb.bb_label = q /\ pb.bb_label = p` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `MEM qb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `fn_reachable fn q` by
    (gvs[venomWfTheory.fn_reachable_def] >>
     metis_tac[relationTheory.RTC_RULES_RIGHT1]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre /\ MEM q (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `MEM q (cfg_succs_of (cfg_analyze fn) p)` by
    (gvs[venomWfTheory.fn_cfg_edge_def] >>
     metis_tac[cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs]) >>
  `!i. i <= LENGTH qb.bb_instructions ==>
    MEM v (live_vars_at (liveness_analyze fn) q i)` by
    (rpt strip_tac >>
     qpat_assum `qb.bb_label = q` (rewrite_tac o single o SYM) >>
     irule phi_unkilled_exit_live >> simp[]) >>
  `LENGTH (collect_phis qb.bb_instructions) <= LENGTH qb.bb_instructions` by
    (Q.SPEC_TAC (`qb.bb_instructions`, `insts`) >> Induct >>
     simp[collect_phis_def] >> rw[]) >>
  irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_cross_block) >>
  goal_assum drule >> simp[] >> qexistsl_tac [`qb`, `q`] >> simp[] >>
  rpt strip_tac >>
  `MEM v (inst_uses inst)` by
    (gvs[inst_uses_def, phi_operand_vars_mem, listTheory.MEM_MAP,
         pairTheory.EXISTS_PROD] >> metis_tac[phi_pairs_mem_var_operand]) >>
  drule_all phi_codegen_input_dead_after_prefix >> metis_tac[]
QED

Theorem phi_live_out_backward_path:
  !path fn v first_bb last_bb.
    codegen_ready_fn fn /\ is_fn_path fn path /\ path <> [] /\
    fn_reachable fn (HD path) /\
    lookup_block (HD path) fn.fn_blocks = SOME first_bb /\
    lookup_block (LAST path) fn.fn_blocks = SOME last_bb /\
    (!lbl. MEM lbl path ==> ?bb. lookup_block lbl fn.fn_blocks = SOME bb) /\
    (!lbl bb. MEM lbl (TL path) /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
      ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM v (live_vars_at (liveness_analyze fn) (LAST path)
      (LENGTH last_bb.bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze fn) (HD path)
      (LENGTH first_bb.bb_instructions))
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (head::tail)` >> Cases_on `tail`
  >- (strip_tac >> gvs[]) >>
  rename1 `is_fn_path fn (head::next::rest)` >>
  simp[venomWfTheory.is_fn_path_def] >> strip_tac >>
  `?next_bb. lookup_block next fn.fn_blocks = SOME next_bb` by metis_tac[] >>
  `fn_reachable fn next` by
    (gvs[venomWfTheory.fn_reachable_def] >>
     metis_tac[relationTheory.RTC_RULES_RIGHT1]) >>
  `MEM v (live_vars_at (liveness_analyze fn) next
      (LENGTH next_bb.bb_instructions))` by
    (qpat_x_assum `!fn v first_bb last_bb. _`
       (qspecl_then [`fn`, `v`, `next_bb`, `last_bb`] mp_tac) >>
     simp[] >> impl_tac >- (rpt conj_tac >> metis_tac[listTheory.MEM]) >>
     simp[]) >>
  irule phi_live_out_backward_edge >> goal_assum drule >>
  simp[] >> qexistsl_tac [`next`, `next_bb`] >> simp[] >> metis_tac[]
QED

Theorem phi_path_last_suffix[local]:
  !path fn target.
    is_fn_path fn path /\ MEM target path ==>
    ?tail. is_fn_path fn (target::tail) /\
      LAST (target::tail) = LAST path /\ ~MEM target tail /\
      (!lbl. MEM lbl (target::tail) ==> MEM lbl path)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (head::rest)` >> strip_tac >>
  Cases_on `MEM target rest`
  >- (`is_fn_path fn rest` by
        (Cases_on `rest` >> gvs[venomWfTheory.is_fn_path_def]) >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `tail` >> Cases_on `rest` >> gvs[] >> metis_tac[]) >>
  `head = target` by gvs[] >> gvs[] >>
  qexists_tac `rest` >> simp[]
QED

Theorem phi_path_member_reachable[local]:
  !path fn lbl. is_fn_path fn path /\ path <> [] /\
    fn_reachable fn (HD path) /\ MEM lbl path ==> fn_reachable fn lbl
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (head::tail)` >> strip_tac >>
  Cases_on `lbl = head` >- gvs[] >>
  Cases_on `tail` >- gvs[] >>
  rename1 `is_fn_path fn (head::next::rest)` >>
  `fn_cfg_edge fn head next /\ is_fn_path fn (next::rest)` by
    gvs[venomWfTheory.is_fn_path_def] >>
  `fn_reachable fn next` by
    (gvs[venomWfTheory.fn_reachable_def] >>
     metis_tac[relationTheory.RTC_RULES_RIGHT1]) >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED

Theorem phi_reachable_lookup[local]:
  wf_function fn /\ fn_reachable fn lbl ==>
    ?bb. lookup_block lbl fn.fn_blocks = SOME bb
Proof
  strip_tac >> gvs[venomWfTheory.fn_reachable_def] >>
  gvs[Once relationTheory.RTC_CASES2]
  >- (gvs[fn_entry_label_def, entry_block_def] >>
      Cases_on `fn.fn_blocks` >> gvs[] >>
      rename1 `head::tail` >> qexists_tac `head` >>
      irule venomExecPropsTheory.MEM_lookup_block >>
      gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  gvs[venomWfTheory.fn_cfg_edge_def] >>
  `MEM lbl (fn_labels fn)` by
    metis_tac[venomWfTheory.wf_function_def, venomWfTheory.fn_succs_closed_def] >>
  gvs[fn_labels_def, listTheory.MEM_MAP] >>
  metis_tac[venomExecPropsTheory.MEM_lookup_block, venomWfTheory.wf_function_def,
            fn_labels_def]
QED

Theorem phi_defined_live_out_back[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs /\
  fn_dominates fn bb.bb_label p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions))
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `fn_reachable fn p` by gvs[venomWfTheory.fn_dominates_def] >>
  qpat_assum `fn_reachable fn p`
    (strip_assume_tac o REWRITE_RULE [venomWfTheory.fn_reachable_def]) >>
  drule phi_rtc_path >> strip_tac >>
  `MEM bb.bb_label path` by
    (gvs[venomWfTheory.fn_dominates_def] >> metis_tac[]) >>
  `fn_reachable fn (HD path)` by
    (simp[venomWfTheory.fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  `!lbl. MEM lbl path ==> fn_reachable fn lbl` by
    metis_tac[phi_path_member_reachable] >>
  drule_all phi_path_last_suffix >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  irule (SRULE [] (Q.SPEC `bb.bb_label::tail` phi_live_out_backward_path)) >>
  simp[] >> qexists_tac `pb` >> simp[] >>
  qexists_tac `tail` >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> metis_tac[phi_reachable_lookup, listTheory.MEM]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME other_bb` >>
  `MEM other_bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `other_bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  strip_tac >> gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  `other_bb = bb` by metis_tac[removeUnusedSsaProofsTheory.ssa_unique_output_block] >>
  metis_tac[]
QED

Theorem phi_prefix_outputs_disjoint_suffix[local]:
  !insts v.
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis insts))) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs)
      (DROP (LENGTH (collect_phis insts)) insts)))
Proof
  Induct >- simp[collect_phis_def] >> rpt gen_tac >>
  rename1 `collect_phis (head::tail)` >>
  Cases_on `head.inst_opcode = PHI` >>
  simp[collect_phis_def, listTheory.ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  `MEM inst tail` by
    (gvs[listTheory.MEM_DROP] >> metis_tac[listTheory.EL_MEM]) >>
  metis_tac[]
QED

Theorem phi_block_outputs_distinct[local]:
  ssa_form fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  strip_tac >> gvs[venomWfTheory.ssa_form_def, fn_insts_def] >>
  qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  Q.SPEC_TAC (`fn.fn_blocks`, `blocks`) >>
  Induct >> simp[fn_insts_blocks_def, listTheory.MAP_APPEND,
    listTheory.FLAT_APPEND, listTheory.ALL_DISTINCT_APPEND] >>
  metis_tac[]
QED

Theorem phi_output_exit_live_prefix[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM outphi (collect_phis bb.bb_instructions) /\ MEM v outphi.inst_outputs /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    metis_tac[phi_block_outputs_distinct] >>
  `~MEM v (FLAT (MAP (\inst. inst.inst_outputs)
    (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)))` by
    (irule phi_prefix_outputs_disjoint_suffix >> simp[] >>
     simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (Q.SPEC_TAC (`bb.bb_instructions`, `insts`) >> Induct >>
     simp[collect_phis_def] >> rw[]) >>
  irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
  goal_assum drule >> simp[] >> qexists_tac `LENGTH bb.bb_instructions` >>
  simp[] >> rpt strip_tac >>
  `MEM (EL k bb.bb_instructions)
    (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)` by
    (simp[listTheory.MEM_DROP] >>
     qexists_tac `k - LENGTH (collect_phis bb.bb_instructions)` >> simp[]) >>
  qpat_x_assum `~MEM v (FLAT _)` mp_tac >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[inst_defs_def]
QED

Theorem phi_prefix_output_not_operand:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\
  MEM outphi (collect_phis bb.bb_instructions) /\ MEM v outphi.inst_outputs ==>
  ~MEM (Var v) phi.inst_operands
Proof
  strip_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `MEM outphi bb.bb_instructions` by
    metis_tac[livenessProofsTheory.collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by metis_tac[phi_codegen_edge_wf] >>
  `fn_reachable fn bb.bb_label` by metis_tac[phi_edge_operand_reachable] >>
  `?p. MEM (p,v) (phi_pairs phi.inst_operands)` by
    (gvs[venomWfTheory.phi_edge_uses_wf_def] >>
     metis_tac[venomWfTheory.phi_well_formed_var_pair]) >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = p /\
    def_available_at fn pb NONE v` by
    (gvs[venomWfTheory.phi_edge_uses_wf_def] >> metis_tac[]) >>
  `lookup_block p fn.fn_blocks = SOME pb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  `fn_dominates fn bb.bb_label p` by
    (qpat_x_assum `def_available_at _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [venomWfTheory.def_available_at_def]) >>
     `def_bb = bb` by
       metis_tac[removeUnusedSsaProofsTheory.ssa_unique_output_block] >>
     gvs[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions))` by
    (irule phi_pair_live_out >> goal_assum drule >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions))` by
    (irule phi_defined_live_out_back >> goal_assum drule >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))` by
    (irule phi_output_exit_live_prefix >> goal_assum drule >> metis_tac[]) >>
  `MEM v (inst_uses phi)` by
    metis_tac[removeUnusedSsaProofsTheory.operand_var_in_inst_uses] >>
  metis_tac[phi_codegen_input_dead_after_prefix]
QED
