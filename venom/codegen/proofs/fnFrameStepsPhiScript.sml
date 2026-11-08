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
  allocaRemapSSA fnPlanPrefix removeUnusedSsaProofs dftCommutation fnFrameDeepInvoke cfgCorrectnessProof livenessProofs

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
    (irule cfgCorrectnessProofTheory.cfg_analyze_preserves_bb_succs >>
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
  imp_res_tac phi_popmany_spilled >> imp_res_tac deepResidualBudgetTheory.do_dup_spilled_eq >> gvs[]
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
  simp[Abbr `acc`, fnLineageStaticTheory.phi_pair_updates_lookup] >>
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
  first_x_assum drule >> simp[fnLineageStaticTheory.phi_pair_updates_lookup] >>
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

Theorem phi_uses_disjoint_el[local]:
  !l i k v.
    phi_uses_disjoint l /\ i < LENGTH l /\ k < LENGTH l /\ i <> k /\
    MEM (Var v) (EL i l).inst_operands ==>
    ~MEM (Var v) (EL k l).inst_operands
Proof
  Induct >> simp[] >> rpt gen_tac >> simp[phi_uses_disjoint_def] >>
  strip_tac >> Cases_on `i` >> Cases_on `k` >> gvs[]
  >- (gvs[listTheory.EVERY_MEM, inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
      metis_tac[listTheory.EL_MEM])
  >- (gvs[listTheory.EVERY_MEM, inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
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
  drule cfgNormBaseTheory.phi_pairs_mem_var >> strip_tac >>
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
  drule venomExecProofsTheory.rtc_to_fn_path >> strip_tac >>
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
    metis_tac[cfgCorrectnessProofTheory.cfg_analyze_pred_labels] >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = p` by
    (gvs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM bb.bb_label (bb_succs pb)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond,
              cfgCorrectnessProofTheory.cfg_analyze_preserves_bb_succs] >>
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
     metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
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
  qexists_tac `phi` >> simp[] >> metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]
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
      simp[Abbr `acc`, fnLineageStaticTheory.phi_pair_updates_lookup]) >>
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
        metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
     `i <> k` by decide_tac >>
     drule_all phi_uses_disjoint_el >>
     gvs[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
     metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
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
     metis_tac[cfgCorrectnessProofTheory.cfg_analyze_preserves_bb_succs]) >>
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
     metis_tac[cfgCorrectnessProofTheory.cfg_analyze_preserves_bb_succs]) >>
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
    (gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var, listTheory.MEM_MAP,
         pairTheory.EXISTS_PROD] >> metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
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
  drule venomExecProofsTheory.rtc_to_fn_path >> strip_tac >>
  `MEM bb.bb_label path` by
    (gvs[venomWfTheory.fn_dominates_def] >> metis_tac[]) >>
  `fn_reachable fn (HD path)` by
    (simp[venomWfTheory.fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  `!lbl. MEM lbl path ==> fn_reachable fn lbl` by
    metis_tac[removeUnusedSsaProofsTheory.is_fn_path_all_reachable] >>
  drule_all phi_path_last_suffix >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  irule (SRULE [] (Q.SPEC `bb.bb_label::tail` phi_live_out_backward_path)) >>
  simp[] >> qexists_tac `pb` >> simp[] >>
  qexists_tac `tail` >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> metis_tac[removeUnusedSsaProofsTheory.fn_reachable_has_block, listTheory.MEM]) >>
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
    metis_tac[phiBlockTheory.ssa_form_block_outputs_distinct] >>
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

Theorem phi_eval_take_ok:
  !insts s final k. eval_phis s insts = OK final ==>
    ?prefix_state. eval_phis s (TAKE k insts) = OK prefix_state
Proof
  Induct >- simp[eval_phis_def] >> rpt gen_tac >>
  rename1 `eval_phis s (head::tail)` >>
  Cases_on `k` >- simp[eval_phis_def] >>
  qmatch_goalsub_rename_tac `TAKE (SUC take_count) (head::tail)` >>
  Cases_on `head.inst_opcode = PHI`
  >- (simp[eval_phis_def] >> strip_tac >>
      Cases_on `eval_one_phi s head` >> gvs[] >>
      rename1 `eval_one_phi s head = SOME pair` >> PairCases_on `pair` >>
      Cases_on `eval_phis s tail` >> gvs[] >>
      first_x_assum drule >>
      disch_then (qspec_then `take_count` strip_assume_tac) >> simp[]) >>
  simp[eval_phis_def]
QED

Theorem phi_eval_member_value:
  !insts s final inst out value.
    eval_phis s insts = OK final /\ EVERY (\i. i.inst_opcode = PHI) insts /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
    MEM inst insts /\ eval_one_phi s inst = SOME (out,value) ==>
    FLOOKUP final.vs_vars out = SOME value
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `eval_phis s (head::tail)` >>
  simp[eval_phis_def] >> strip_tac >>
  Cases_on `eval_one_phi s head` >> gvs[] >>
  rename1 `eval_one_phi s head = SOME result` >> PairCases_on `result` >>
  Cases_on `eval_phis s tail` >> gvs[] >>
  simp[update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `out = result0` >> gvs[]
  >- (`MEM out head.inst_outputs /\ MEM out inst.inst_outputs` by
        metis_tac[venomExecProofsTheory.eval_one_phi_output_mem] >>
      gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT,
          listTheory.MEM_MAP] >> metis_tac[]) >>
  first_x_assum irule >> gvs[listTheory.ALL_DISTINCT_APPEND] >>
  qexistsl_tac [`inst`, `s`] >> simp[]
QED

Theorem phi_eval_member_result:
  !insts s final inst.
    eval_phis s insts = OK final /\ EVERY (\i. i.inst_opcode = PHI) insts /\
    MEM inst insts ==> ?out value. eval_one_phi s inst = SOME (out,value)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `eval_phis s (head::tail)` >>
  simp[eval_phis_def] >> strip_tac >>
  Cases_on `eval_one_phi s head` >> gvs[] >>
  rename1 `eval_one_phi s head = SOME result` >> PairCases_on `result` >>
  Cases_on `eval_phis s tail` >> gvs[] >> metis_tac[]
QED

Theorem phi_eval_member_output_agree:
  eval_phis s insts = OK final /\ eval_phis s prefix = OK partial /\
  EVERY (\i. i.inst_opcode = PHI) insts /\
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) prefix)) /\
  MEM inst insts /\ MEM inst prefix /\ MEM out inst.inst_outputs ==>
  FLOOKUP partial.vs_vars out = FLOOKUP final.vs_vars out
Proof
  strip_tac >>
  `?name value. eval_one_phi s inst = SOME (name,value)` by
    metis_tac[phi_eval_member_result] >>
  `inst.inst_outputs = [name]` by
    metis_tac[venomExecProofsTheory.eval_one_phi_imp_inst_outputs] >>
  gvs[] >> metis_tac[phi_eval_member_value]
QED

Theorem phi_collect_prefix_index:
  !insts. LENGTH (collect_phis insts) <= LENGTH insts /\
    (!k. k < LENGTH (collect_phis insts) ==>
      EL k (collect_phis insts) = EL k insts)
Proof
  Induct >- simp[collect_phis_def] >>
  gen_tac >> simp[collect_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  rpt strip_tac >> Cases_on `k` >> gvs[]
QED

Theorem phi_input_dead_at_successor:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  MEM (Var v) (EL i (collect_phis bb.bb_instructions)).inst_operands ==>
  ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
Proof
  strip_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM (EL i (collect_phis bb.bb_instructions))
    (collect_phis bb.bb_instructions)` by simp[listTheory.EL_MEM] >>
  `MEM v (inst_uses (EL i (collect_phis bb.bb_instructions)))` by
    metis_tac[removeUnusedSsaProofsTheory.operand_var_in_inst_uses] >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))` by
    metis_tac[phi_codegen_input_dead_after_prefix] >>
  `phi_edge_uses_wf fn bb (EL i (collect_phis bb.bb_instructions))` by
    metis_tac[phi_codegen_edge_wf] >>
  `fn_reachable fn bb.bb_label` by metis_tac[phi_edge_operand_reachable] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    metis_tac[phi_codegen_uses_disjoint] >>
  `!k. SUC i <= k /\ k < LENGTH (collect_phis bb.bb_instructions) ==>
     ~MEM v (inst_defs (EL k bb.bb_instructions)) /\
     ~MEM v (inst_uses (EL k bb.bb_instructions))` by
    (gen_tac >> strip_tac >>
     `EL k bb.bb_instructions = EL k (collect_phis bb.bb_instructions)` by
       metis_tac[phi_collect_prefix_index] >>
     `MEM (EL k (collect_phis bb.bb_instructions))
       (collect_phis bb.bb_instructions)` by simp[listTheory.EL_MEM] >>
     conj_tac
     >- (simp[inst_defs_def] >> strip_tac >>
         metis_tac[phi_prefix_output_not_operand]) >>
     `i <> k` by decide_tac >>
     drule_all phi_uses_disjoint_el >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  mp_tac (SRULE [LET_THM] livenessProofsTheory.live_vars_at_forward_or_used) >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then
    [`bb`, `SUC i`, `LENGTH (collect_phis bb.bb_instructions)`, `v`] mp_tac) >>
  simp[phi_collect_prefix_index] >> gen_tac >>
  Cases_on `k <= i` >> simp[] >>
  Cases_on `k < LENGTH (collect_phis bb.bb_instructions)` >> simp[] >>
  `SUC i <= k` by decide_tac >> metis_tac[]
QED

Theorem phi_prefix_operand_lookup:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM (Var v) phi.inst_operands /\
  (!inst. MEM inst done ==> MEM inst (collect_phis bb.bb_instructions)) /\
  eval_phis vs done = OK partial ==>
  FLOOKUP partial.vs_vars v = FLOOKUP vs.vs_vars v
Proof
  strip_tac >> irule phi_eval_preserves_lookup >> qexists_tac `done` >>
  simp[] >> simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[phi_prefix_output_not_operand]
QED

Theorem phi_output_retpc:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM out inst.inst_outputs /\ MEM (Var src) inst.inst_operands ==>
  (retpc_var fn out <=> retpc_var fn src)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >>
      qpat_x_assum `retpc_shape_ok fn` mp_tac >>
      simp[retpc_shape_ok_def] >> strip_tac >>
      qpat_x_assum `!inst x. MEM inst _ /\ MEM x _ /\ retpc_var _ _ ==> _`
        (qspecl_then [`inst`, `out`] mp_tac) >>
      simp[]) >>
  simp[retpc_var_def] >> strip_tac >>
  irule copy_phi_var_phi >> metis_tac[]
QED

Theorem phi_selected_frame_value:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM inst phis /\ EVERY (\i. i.inst_opcode = PHI) phis /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis)) /\
  eval_phis vs phis = OK final /\ vs.vs_prev_bb = SOME pred /\
  resolve_phi pred inst.inst_operands = SOME (Var src) ==>
  operand_val (frame_view fn ra final) lo (Var (HD inst.inst_outputs)) =
    operand_val (frame_view fn ra vs) lo (Var src)
Proof
  strip_tac >>
  `?out value. eval_one_phi vs inst = SOME (out,value)` by
    metis_tac[phi_eval_member_result] >>
  `inst.inst_outputs = [out] /\ FLOOKUP vs.vs_vars src = SOME value` by
    (qpat_x_assum `eval_one_phi _ _ = _` mp_tac >>
     simp[eval_one_phi_def, eval_operand_def, lookup_var_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `FLOOKUP final.vs_vars out = SOME value` by
    metis_tac[phi_eval_member_value] >>
  `MEM (Var src) inst.inst_operands` by
    metis_tac[dftCommutationTheory.resolve_phi_MEM] >>
  `retpc_var fn out = retpc_var fn src` by
    (irule phi_output_retpc >> simp[] >> qexists_tac `inst` >> simp[]) >>
  simp[operand_val_def, frame_view_vars_lookup]
QED

Theorem phi_popmany_singleton_stack:
  (SND (popmany_plan [v] ps)).ps_stack =
    case stack_get_depth v ps.ps_stack of
      NONE => ps.ps_stack
    | SOME d => stack_pop 1 (stack_swap d ps.ps_stack)
Proof
  Cases_on `stack_get_depth v ps.ps_stack` >>
  simp[stackPlanOpsTheory.popmany_plan_def,
       stackPlanOpsTheory.popmany_individual_def,
       stackPlanOpsTheory.is_contiguous_top_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF] >>
  rename1 `stack_get_depth v ps.ps_stack = SOME d` >>
  `d < LENGTH ps.ps_stack` by metis_tac[planWfTheory.stack_get_depth_bound] >>
  Cases_on `d = 1` >> simp[]
  >- (pairarg_tac >> gvs[] >> rename1 `do_swap 1 ps = (swap_ops, swapped)` >>
      `swapped.ps_stack = stack_swap 1 ps.ps_stack` by
        metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >>
      simp[]) >>
  Cases_on `d = 0` >> simp[]
  >- simp[stackModelTheory.stack_swap_def, listTheory.LUPDATE_SAME] >>
  pairarg_tac >> gvs[] >> rename1 `do_swap d ps = (swap_ops, swapped)` >>
  `swapped.ps_stack = stack_swap d ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >> simp[]
QED

Theorem phi_popmany_singleton_count:
  !v ps x. MEM v ps.ps_stack ==>
    LIST_ELEM_COUNT x (SND (popmany_plan [v] ps)).ps_stack +
      (if x = v then 1 else 0) = LIST_ELEM_COUNT x ps.ps_stack
Proof
  rpt strip_tac >>
  `?d. stack_get_depth v ps.ps_stack = SOME d` by
    (Cases_on `stack_get_depth v ps.ps_stack` >> simp[] >>
     `?k. k < LENGTH ps.ps_stack /\ EL k ps.ps_stack = v` by
       metis_tac[listTheory.MEM_EL] >>
     `LENGTH ps.ps_stack - 1 - k < LENGTH ps.ps_stack /\
      LENGTH ps.ps_stack - 1 - (LENGTH ps.ps_stack - 1 - k) = k` by decide_tac >>
     gvs[stackModelTheory.stack_get_depth_NONE] >>
     first_x_assum (qspec_then `LENGTH ps.ps_stack - 1 - k` mp_tac) >>
     simp[stackModelTheory.stack_peek_def]) >>
  `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = v` by
    metis_tac[stackModelTheory.stack_get_depth_props, planWfTheory.stack_get_depth_bound] >>
  `LIST_ELEM_COUNT x (stack_swap d ps.ps_stack) = LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity, doSwapSimTheory.do_swap_stack_result] >>
  `LENGTH (stack_swap d ps.ps_stack) = LENGTH ps.ps_stack` by
    simp[stackModelTheory.stack_swap_def] >>
  `stack_peek 0 (stack_swap d ps.ps_stack) = v` by
    (simp[stackModelTheory.stack_peek_def, stackModelTheory.stack_swap_def,
          listTheory.EL_LUPDATE] >> gvs[stackModelTheory.stack_peek_def]) >>
  qspecl_then [`x`, `stack_swap d ps.ps_stack`] mp_tac reorderSimTheory.stack_pop_one_elem_count >>
  simp[phi_popmany_singleton_stack] >>
  `stack_swap d ps.ps_stack <> []` by
    (strip_tac >>
     `LENGTH (stack_swap d ps.ps_stack) = 0` by simp[] >>
     gvs[stackModelTheory.stack_swap_def]) >>
  Cases_on `v = x` >> simp[rich_listTheory.LIST_ELEM_COUNT_DEF]
QED

Theorem phi_popmany_singleton_mem:
  !v ps x. LIST_ELEM_COUNT v ps.ps_stack <= 1 ==>
    (MEM x (SND (popmany_plan [v] ps)).ps_stack <=>
     MEM x ps.ps_stack /\ x <> v)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `MEM v ps.ps_stack`
  >- (drule phi_popmany_singleton_count >>
      disch_then (qspec_then `x` mp_tac) >>
      Cases_on `x = v` >>
      gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  `stack_get_depth v ps.ps_stack = NONE` by
    (simp[stackModelTheory.stack_get_depth_NONE] >> rpt strip_tac >>
     `MEM (stack_peek d ps.ps_stack) ps.ps_stack` by
       (simp[NoAsms, stackModelTheory.stack_peek_def] >>
        irule listTheory.EL_MEM >> decide_tac) >> metis_tac[]) >>
  simp[phi_popmany_singleton_stack] >> metis_tac[]
QED

Definition phi_stack_provenance_def:
  phi_stack_provenance base pred entry done todo ps <=>
    generated_plan_state_wf_marked base ps /\
    ps.ps_spilled = entry.ps_spilled /\
    (!at. MEM at ps.ps_stack ==>
      (MEM at entry.ps_stack /\
       ~(?inst. MEM inst done /\
                resolve_phi pred inst.inst_operands = SOME at)) \/
      (?inst v. MEM inst done /\ MEM v inst.inst_outputs /\ at = Var v)) /\
    (!inst op. MEM inst todo /\ is_var_operand op /\ MEM op inst.inst_operands ==>
      (MEM op ps.ps_stack <=> MEM op entry.ps_stack))
End

Theorem phi_stack_provenance_init:
  !base entry pred phis. generated_plan_state_wf_marked base entry ==>
  phi_stack_provenance base pred entry [] phis entry
Proof
  simp[phi_stack_provenance_def]
QED

Theorem phi_stack_provenance_no_change:
  !base pred entry done inst todo ps.
  phi_stack_provenance base pred entry done (inst::todo) ps /\
  (!at. MEM at ps.ps_stack ==>
        resolve_phi pred inst.inst_operands <> SOME at) ==>
  phi_stack_provenance base pred entry (done ++ [inst]) todo ps
Proof
  rpt gen_tac >> simp[phi_stack_provenance_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!at. MEM at _ ==> _ \/ _` drule >>
      simp[] >> metis_tac[]) >> metis_tac[]
QED

Theorem phi_lupdate_count:
  !xs n x y. n < LENGTH xs ==>
    LIST_ELEM_COUNT x (LUPDATE y n xs) + (if x = EL n xs then 1 else 0) =
    LIST_ELEM_COUNT x xs + (if x = y then 1 else 0)
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `n`
  >- (Cases_on `x = h` >> Cases_on `x = y` >>
      gvs[listTheory.LUPDATE_def, rich_listTheory.LIST_ELEM_COUNT_THM,
           EQ_SYM_EQ]) >>
  simp[listTheory.LUPDATE_def] >> strip_tac >> rename1 `index < LENGTH xs` >>
  first_x_assum drule >> disch_then (qspecl_then [`x`, `y`] mp_tac) >>
  Cases_on `x = h` >> Cases_on `x = y` >> Cases_on `x = EL index xs` >>
  gvs[rich_listTheory.LIST_ELEM_COUNT_THM, EQ_SYM_EQ] >> decide_tac
QED

Theorem phi_stack_poke_mem:
  !xs d src dst x.
    d < LENGTH xs /\ stack_peek d xs = src /\
    LIST_ELEM_COUNT src xs <= 1 ==>
    (MEM x (stack_poke d dst xs) <=> (MEM x xs /\ x <> src) \/ x = dst)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH xs - 1 - d < LENGTH xs` by decide_tac >>
  `MEM src xs` by
    (qpat_x_assum `stack_peek d xs = src` (SUBST1_TAC o SYM) >>
     simp[stackModelTheory.stack_peek_def, listTheory.EL_MEM]) >>
  drule phi_lupdate_count >>
  disch_then (qspecl_then [`x`, `dst`] mp_tac) >>
  Cases_on `x = src` >> Cases_on `x = dst` >>
  gvs[GSYM stackModelTheory.stack_poke_def, stackModelTheory.stack_peek_def,
      GSYM rich_listTheory.LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem phi_stack_poke_fresh_count:
  !xs d dst. d < LENGTH xs /\ ~MEM dst xs ==>
    LIST_ELEM_COUNT dst (stack_poke d dst xs) = 1
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH xs - 1 - d < LENGTH xs` by decide_tac >>
  `~(dst = EL (LENGTH xs - 1 - d) xs)` by
    metis_tac[listTheory.EL_MEM] >>
  `LIST_ELEM_COUNT dst xs = 0` by
    gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM] >>
  drule phi_lupdate_count >>
  disch_then (qspecl_then [`dst`, `dst`] mp_tac) >>
  simp[GSYM stackModelTheory.stack_poke_def]
QED

Theorem phi_stack_poke_pop_mem:
  !ps d src dst ops final x.
    d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = src /\
    LIST_ELEM_COUNT src ps.ps_stack <= 1 /\ ~MEM dst ps.ps_stack /\
    popmany_plan [dst] (ps with ps_stack := stack_poke d dst ps.ps_stack) =
      (ops, final) ==>
    (MEM x final.ps_stack <=> MEM x ps.ps_stack /\ x <> src)
Proof
  rpt gen_tac >> strip_tac >>
  `LIST_ELEM_COUNT dst (stack_poke d dst ps.ps_stack) <= 1` by
    simp[phi_stack_poke_fresh_count] >>
  qspecl_then [`dst`, `ps with ps_stack := stack_poke d dst ps.ps_stack`, `x`]
    mp_tac phi_popmany_singleton_mem >>
  simp[] >>
  `MEM x (stack_poke d dst ps.ps_stack) <=>
   (MEM x ps.ps_stack /\ x <> src) \/ x = dst` by
    metis_tac[phi_stack_poke_mem] >>
  simp[] >> metis_tac[]
QED

Theorem phi_entry_output_absent:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    ~(MEM op ps.ps_stack /\
      ?inst. MEM inst (collect_phis bb.bb_instructions) /\
             resolve_phi pred inst.inst_operands = SOME op) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM out phi.inst_outputs ==>
  ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled
Proof
  strip_tac >>
  `~(?inst. MEM inst (collect_phis bb.bb_instructions) /\
            resolve_phi pred inst.inst_operands = SOME (Var out))` by
    (strip_tac >>
     `MEM (Var out) inst.inst_operands` by
       metis_tac[dftCommutationTheory.resolve_phi_MEM] >>
     metis_tac[phi_prefix_output_not_operand]) >>
  `MEM out (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[livenessProofsTheory.collect_phis_mem]) >>
  qpat_x_assum `!op v. _` (qspecl_then [`Var out`, `out`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem phi_provenance_output_absent:
  !base pred entry done todo ps out.
    phi_stack_provenance base pred entry done todo ps /\
    ~MEM (Var out) entry.ps_stack /\ Var out NOTIN FDOM entry.ps_spilled /\
    (!inst. MEM inst done ==> ~MEM out inst.inst_outputs) ==>
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled
Proof
  simp[phi_stack_provenance_def] >> rpt strip_tac >> metis_tac[operand_11]
QED

Theorem phi_stack_hit_operand:
  !ops stk d.
    stack_get_phi_depth (FILTER is_var_operand ops) stk = SOME d ==>
    is_var_operand (stack_peek d stk) /\ MEM (stack_peek d stk) ops /\
    MEM (stack_peek d stk) stk
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH stk` by
    metis_tac[genBlockSimTheory.stack_get_phi_depth_var_not_marker] >>
  `MEM (EL d (REVERSE stk)) (FILTER is_var_operand ops)` by
    (qpat_x_assum `stack_get_phi_depth _ _ = _` mp_tac >>
     simp[stackModelTheory.stack_get_phi_depth_def] >> strip_tac >>
     drule genBlockSimTheory.stack_find_el >> simp[]) >>
  `stack_peek d stk = EL d (REVERSE stk)` by
    (simp[stackModelTheory.stack_peek_def, listTheory.EL_REVERSE] >>
     `PRE (LENGTH stk - d) = LENGTH stk - 1 - d` by decide_tac >> simp[]) >>
  gvs[listTheory.MEM_FILTER] >>
  metis_tac[listTheory.EL_MEM, listTheory.MEM_REVERSE, listTheory.LENGTH_REVERSE]
QED

Theorem phi_provenance_hit_selected:
  !base pred entry done inst todo ps d.
    phi_stack_provenance base pred entry done (inst::todo) ps /\
    (!phi op. MEM phi (inst::todo) /\ is_var_operand op /\
      MEM op phi.inst_operands /\ MEM op entry.ps_stack ==>
      resolve_phi pred phi.inst_operands = SOME op) /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
    resolve_phi pred inst.inst_operands = SOME (stack_peek d ps.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  drule phi_stack_hit_operand >> strip_tac >>
  gvs[phi_stack_provenance_def] >>
  qpat_x_assum `!phi op. _` irule >> simp[] >> metis_tac[]
QED

Theorem phi_provenance_rename:
  !base pred entry done inst todo ps next src out keep.
    phi_stack_provenance base pred entry done (inst::todo) ps /\
    resolve_phi pred inst.inst_operands = SOME src /\ MEM out inst.inst_outputs /\
    generated_plan_state_wf_marked base next /\ next.ps_spilled = ps.ps_spilled /\
    (!at. MEM at next.ps_stack <=>
      (MEM at ps.ps_stack /\ at <> src) \/ (keep /\ at = Var out)) /\
    (!phi op. MEM phi todo /\ is_var_operand op /\ MEM op phi.inst_operands ==>
      op <> src /\ op <> Var out) ==>
    phi_stack_provenance base pred entry (done ++ [inst]) todo next
Proof
  rpt gen_tac >> simp[phi_stack_provenance_def] >> strip_tac >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!at. MEM at _ <=> _` (qspec_then `at` mp_tac) >>
      qpat_x_assum `!at. MEM at _ ==> _ \/ _` (qspec_then `at` mp_tac) >>
      simp[] >> metis_tac[optionTheory.SOME_11]) >>
  rpt strip_tac >>
  qpat_x_assum `!at. MEM at _ <=> _` (qspec_then `op` mp_tac) >>
  metis_tac[]
QED

Theorem do_swap_wf_marked:
  !base ps dist ops ps'.
    generated_plan_state_wf_marked base ps /\
    dist < LENGTH ps.ps_stack /\
    do_swap dist ps = (ops, ps') ==>
    generated_plan_state_wf_marked base ps'
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generated_plan_state_wf_marked bound ps` >>
  `plan_slots_bounded bound ps'` by
    metis_tac[planSpillBoundsTheory.do_swap_plan_slots_bounded,
              generated_plan_state_wf_marked_def] >>
  `sorting$PERM ps'.ps_stack ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_perm, pairTheory.SND] >>
  `ps'.ps_spilled = ps.ps_spilled /\
   doSwapSim$spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled` by
    metis_tac[doSwapSimTheory.do_swap_layout_wf,
              generated_plan_state_wf_marked_def, pairTheory.SND] >>
  gvs[generated_plan_state_wf_marked_def] >> conj_tac
  >- metis_tac[sortingTheory.PERM_FILTER, sortingTheory.ALL_DISTINCT_PERM] >>
  fs[pred_setTheory.IN_DISJOINT] >> metis_tac[sortingTheory.PERM_MEM_EQ]
QED

Theorem wf_marked_stack_sublist:
  !base ps stk.
    generated_plan_state_wf_marked base ps /\
    (!op. MEM op stk ==> MEM op ps.ps_stack) /\
    ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) stk) ==>
    generated_plan_state_wf_marked base (ps with ps_stack := stk)
Proof
  simp[generated_plan_state_wf_marked_def, pred_setTheory.IN_DISJOINT] >>
  metis_tac[]
QED

Theorem wf_marked_pop:
  !base ps n.
    generated_plan_state_wf_marked base ps ==>
    generated_plan_state_wf_marked base
      (ps with ps_stack := stack_pop n ps.ps_stack)
Proof
  rpt strip_tac >> irule wf_marked_stack_sublist >>
  simp[stackModelTheory.stack_pop_def] >>
  conj_tac >- metis_tac[rich_listTheory.MEM_TAKE] >>
  qpat_x_assum `generated_plan_state_wf_marked _ _` mp_tac >>
  simp[generated_plan_state_wf_marked_def] >> strip_tac >>
  `ps.ps_stack = TAKE (LENGTH ps.ps_stack - n) ps.ps_stack ++
                 DROP (LENGTH ps.ps_stack - n) ps.ps_stack` by
    simp[] >>
  metis_tac[listTheory.FILTER_APPEND_DISTRIB, listTheory.ALL_DISTINCT_APPEND]
QED

Theorem popmany_individual_wf_marked:
  !xs base ps ops ps'.
    generated_plan_state_wf_marked base ps /\
    popmany_individual xs ps = (ops, ps') ==>
    generated_plan_state_wf_marked base ps'
Proof
  simp[stackPlanOpsTheory.popmany_individual_def] >> rpt gen_tac >>
  rename1 `generated_plan_state_wf_marked bound _` >>
  qmatch_goalsub_abbrev_tac `FOLDL popf acc0 sorted` >>
  `!items acc.
     generated_plan_state_wf_marked bound (SND acc) ==>
     generated_plan_state_wf_marked bound (SND (FOLDL popf acc items))` by
    (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     first_x_assum irule >> PairCases_on `acc` >> gvs[] >>
     simp[Abbr `popf`] >>
     Cases_on `stack_get_depth h acc1.ps_stack` >> simp[] >>
     rename1 `stack_get_depth h acc1.ps_stack = SOME dist` >>
     drule stackModelTheory.stack_get_depth_props >> strip_tac >>
     Cases_on `dist = 0` >> simp[]
     >- metis_tac[wf_marked_pop, pairTheory.SND] >>
     pairarg_tac >> simp[] >>
     metis_tac[wf_marked_pop, do_swap_wf_marked, pairTheory.SND]) >>
  rpt strip_tac >> first_x_assum (qspec_then `sorted` mp_tac) >>
  disch_then (qspec_then `acc0` mp_tac) >>
  gvs[Abbr `acc0`]
QED

Theorem popmany_plan_wf_marked:
  !xs base ps ops ps'.
    generated_plan_state_wf_marked base ps /\
    popmany_plan xs ps = (ops, ps') ==>
    generated_plan_state_wf_marked base ps'
Proof
  Cases >- simp[stackPlanOpsTheory.popmany_plan_def] >>
  simp[stackPlanOpsTheory.popmany_plan_def] >> rpt gen_tac >>
  reverse IF_CASES_TAC
  >- metis_tac[popmany_individual_wf_marked] >>
  reverse IF_CASES_TAC
  >- metis_tac[popmany_individual_wf_marked] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `is_contiguous_top depths` >>
  `!v. IS_SOME (stack_get_depth v ps.ps_stack) ==>
       THE (stack_get_depth v ps.ps_stack) < LENGTH ps.ps_stack` by
    (gen_tac >> Cases_on `stack_get_depth v ps.ps_stack` >> simp[] >>
     metis_tac[stackModelTheory.stack_get_depth_props]) >>
  `!d. MEM d depths ==> d < LENGTH ps.ps_stack` by
    (simp[Abbr `depths`, listTheory.MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     gvs[listTheory.EVERY_MEM, listTheory.MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `MEM (SUC (LENGTH t)) depths` by
    (`LENGTH depths = SUC (LENGTH t)` by simp[Abbr `depths`] >>
     `MEM (SUC (LENGTH t)) (QSORT (\a b. a <= b) depths)` by
       gvs[stackPlanOpsTheory.is_contiguous_top_def, listTheory.MEM_GENLIST] >>
     metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]) >>
  `SUC (LENGTH t) < LENGTH ps.ps_stack` by metis_tac[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[do_swap_wf_marked, wf_marked_pop]
QED

Theorem phi_filter_lupdate_distinct:
  !xs n dst marker.
    ALL_DISTINCT (FILTER (\x. x <> marker) xs) /\ ~MEM dst xs ==>
    ALL_DISTINCT (FILTER (\x. x <> marker) (LUPDATE dst n xs))
Proof
  Induct >- simp[listTheory.LUPDATE_def] >> rpt gen_tac >> Cases_on `n` >>
  simp[listTheory.LUPDATE_def] >> rpt strip_tac >>
  Cases_on `h = marker` >> Cases_on `dst = marker` >>
  gvs[listTheory.MEM_FILTER] >>
  metis_tac[listTheory.MEM_LUPDATE_E]
QED

Theorem phi_wf_marked_poke:
  !base ps d out.
    generated_plan_state_wf_marked base ps /\
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled ==>
    generated_plan_state_wf_marked base
      (ps with ps_stack := stack_poke d (Var out) ps.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[generated_plan_state_wf_marked_def, stackModelTheory.stack_poke_def] >>
  conj_tac >- metis_tac[phi_filter_lupdate_distinct] >>
  fs[pred_setTheory.IN_DISJOINT] >> metis_tac[listTheory.MEM_LUPDATE_E]
QED

Theorem phi_marked_count:
  !xs marker src.
    ALL_DISTINCT (FILTER (\x. x <> marker) xs) /\ src <> marker ==>
    LIST_ELEM_COUNT src xs <= 1
Proof
  Induct >- simp[rich_listTheory.LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> Cases_on `h = marker` >> Cases_on `h = src` >>
  gvs[rich_listTheory.LIST_ELEM_COUNT_THM, listTheory.MEM_FILTER,
      GSYM rich_listTheory.LIST_ELEM_COUNT_MEM] >>
  strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem phi_plan_hit_residents:
  !base ps inst live halt d ops next.
    generated_plan_state_wf_marked base ps /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    ~MEM (operand_to_string (stack_peek d ps.ps_stack)) live /\
    ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
    Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled /\
    generate_phi_plan inst live halt ps = (ops,next) ==>
    generated_plan_state_wf_marked base next /\
    next.ps_spilled = ps.ps_spilled /\
    (!at. MEM at next.ps_stack <=>
      (MEM at ps.ps_stack /\ at <> stack_peek d ps.ps_stack) \/
      ((halt \/ MEM (HD inst.inst_outputs) live) /\ at = Var (HD inst.inst_outputs)))
Proof
  rpt gen_tac >> strip_tac >> rename1 `generated_plan_state_wf_marked bound ps` >>
  `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack <> dead_stack_marker` by
    metis_tac[genBlockSimTheory.stack_get_phi_depth_var_not_marker] >>
  `LIST_ELEM_COUNT (stack_peek d ps.ps_stack) ps.ps_stack <= 1` by
    (irule phi_marked_count >> qexists_tac `dead_stack_marker` >>
     gvs[generated_plan_state_wf_marked_def]) >>
  `generated_plan_state_wf_marked bound
    (ps with ps_stack := stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack)` by
    metis_tac[phi_wf_marked_poke] >>
  drule_all phi_plan_hit_no_dup >>
  Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) live` >> simp[]
  >- (pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
      conj_tac >- metis_tac[popmany_plan_wf_marked, pairTheory.SND] >>
      conj_tac >- (drule phi_popmany_spilled >> simp[]) >>
      gen_tac >> irule phi_stack_poke_pop_mem >> metis_tac[]) >>
  strip_tac >> gvs[] >> gen_tac >>
  simp[phi_stack_poke_mem] >> metis_tac[]
QED

Theorem phi_no_hit_selected_absent:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = NONE /\
  (!op. resolve_phi pred inst.inst_operands = SOME op ==> is_var_operand op) ==>
  !at. MEM at ps.ps_stack ==> resolve_phi pred inst.inst_operands <> SOME at
Proof
  simp[stackModelTheory.stack_get_phi_depth_def] >> strip_tac >>
  fs[stackModelTheory.stack_find_NONE_EVERY, listTheory.EVERY_MEM,
     listTheory.MEM_REVERSE] >>
  metis_tac[dftCommutationTheory.resolve_phi_MEM, listTheory.MEM_FILTER]
QED

Theorem phi_provenance_plan_no_hit:
  !base pred entry done inst todo ps live halt.
    phi_stack_provenance base pred entry done (inst::todo) ps /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = NONE /\
    (!op. resolve_phi pred inst.inst_operands = SOME op ==> is_var_operand op) ==>
    phi_stack_provenance base pred entry (done ++ [inst]) todo
      (SND (generate_phi_plan inst live halt ps))
Proof
  rpt gen_tac >> strip_tac >>
  drule phi_plan_no_hit >> simp[] >> strip_tac >>
  irule phi_stack_provenance_no_change >> simp[] >>
  metis_tac[phi_no_hit_selected_absent]
QED

Theorem phi_provenance_plan_hit:
  !base pred entry done inst todo ps live halt d ops next.
    phi_stack_provenance base pred entry done (inst::todo) ps /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    resolve_phi pred inst.inst_operands = SOME (stack_peek d ps.ps_stack) /\
    inst.inst_outputs <> [] /\
    ~MEM (operand_to_string (stack_peek d ps.ps_stack)) live /\
    ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
    Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled /\
    (!phi op. MEM phi todo /\ is_var_operand op /\ MEM op phi.inst_operands ==>
      op <> stack_peek d ps.ps_stack /\ op <> Var (HD inst.inst_outputs)) /\
    generate_phi_plan inst live halt ps = (ops,next) ==>
    phi_stack_provenance base pred entry (done ++ [inst]) todo next
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `phi_stack_provenance bound pred entry done (inst::todo) ps` >>
  `generated_plan_state_wf_marked bound ps` by
    gvs[phi_stack_provenance_def] >>
  drule_all phi_plan_hit_residents >> strip_tac >>
  irule phi_provenance_rename >> simp[] >>
  qexistsl_tac [`halt \/ MEM (HD inst.inst_outputs) live`, `HD inst.inst_outputs`,
                `ps`] >>
  simp[] >> Cases_on `inst.inst_outputs` >> gvs[] >> metis_tac[]
QED

Theorem phi_pending_source_excluded:
  !done inst todo v.
    phi_uses_disjoint (done ++ inst::todo) /\ MEM (Var v) inst.inst_operands ==>
    !phi. MEM phi todo ==> ~MEM (Var v) phi.inst_operands
Proof
  Induct >> simp[phi_uses_disjoint_def] >> rpt strip_tac
  >- (gvs[listTheory.EVERY_MEM, inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem phi_processed_output_excluded:
  !done inst todo out.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (done ++ inst::todo))) /\
    MEM out inst.inst_outputs ==>
    !phi. MEM phi done ==> ~MEM out phi.inst_outputs
Proof
  simp[listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
       listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

Theorem phi_provenance_fresh_output:
  !base pred entry done inst todo ps out.
    phi_stack_provenance base pred entry done (inst::todo) ps /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (done ++ inst::todo))) /\
    MEM out inst.inst_outputs /\
    ~MEM (Var out) entry.ps_stack /\ Var out NOTIN FDOM entry.ps_spilled ==>
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  irule phi_provenance_output_absent >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[phi_processed_output_excluded]
QED

Theorem phi_collect_outputs_distinct:
  !insts.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (collect_phis insts)))
Proof
  Induct >> simp[collect_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[livenessProofsTheory.collect_phis_mem]
QED

Theorem phi_codegen_inst_shape:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst (collect_phis bb.bb_instructions) ==>
  inst.inst_opcode = PHI /\ LENGTH inst.inst_outputs = 1 /\
  phi_well_formed inst.inst_operands
Proof
  strip_tac >>
  `inst.inst_opcode = PHI /\ MEM inst bb.bb_instructions` by
    (qpat_x_assum `MEM inst (collect_phis _)` mp_tac >>
     Q.SPEC_TAC (`bb.bb_instructions`, `insts`) >>
     Induct >> rw[collect_phis_def] >> gvs[]) >>
  `inst_wf inst` by
    metis_tac[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def] >>
  gvs[venomWfTheory.inst_wf_def]
QED

Theorem phi_codegen_pending_excluded:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  is_var_operand src /\ MEM src inst.inst_operands /\ MEM out inst.inst_outputs ==>
  !phi op. MEM phi todo /\ is_var_operand op /\ MEM op phi.inst_operands ==>
    op <> src /\ op <> Var out
Proof
  strip_tac >>
  `phi_uses_disjoint (done ++ inst::todo)` by
    metis_tac[phi_codegen_uses_disjoint] >>
  Cases_on `src` >> gvs[is_var_operand_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[phi_pending_source_excluded] >>
  `MEM inst (collect_phis bb.bb_instructions) /\
   MEM phi (collect_phis bb.bb_instructions)` by simp[] >>
  metis_tac[phi_prefix_output_not_operand]
QED

Theorem phi_codegen_provenance_fresh:
  !base pred entry done inst todo ps fn bb out.
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  phi_stack_provenance base pred entry done (inst::todo) ps /\
  MEM out inst.inst_outputs /\
  ~MEM (Var out) entry.ps_stack /\ Var out NOTIN FDOM entry.ps_spilled ==>
  ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (collect_phis bb.bb_instructions)))` by
    (irule phi_collect_outputs_distinct >>
     irule phiBlockTheory.ssa_form_block_outputs_distinct >>
     qexists_tac `fn` >> gvs[codegen_ready_fn_def]) >>
  metis_tac[phi_provenance_fresh_output]
QED

Theorem phi_provenance_advance:
  !base pred entry done inst todo ps fn bb halt ops next.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
    collect_phis bb.bb_instructions = done ++ inst::todo /\
    phi_stack_provenance base pred entry done (inst::todo) ps /\
    (!phi op. MEM phi (collect_phis bb.bb_instructions) /\ is_var_operand op /\
      MEM op phi.inst_operands /\ MEM op entry.ps_stack ==>
      resolve_phi pred phi.inst_operands = SOME op) /\
    (!phi out. MEM phi (collect_phis bb.bb_instructions) /\ MEM out phi.inst_outputs ==>
      ~MEM (Var out) entry.ps_stack /\ Var out NOTIN FDOM entry.ps_spilled) /\
    generate_phi_plan inst
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))) halt ps =
      (ops,next) ==>
    phi_stack_provenance base pred entry (done ++ [inst]) todo next
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `phi_stack_provenance bound pred entry done (inst::todo) ps` >>
  `MEM inst (collect_phis bb.bb_instructions)` by simp[] >>
  `inst.inst_opcode = PHI /\ LENGTH inst.inst_outputs = 1 /\
   phi_well_formed inst.inst_operands` by metis_tac[phi_codegen_inst_shape] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- (`SND (generate_phi_plan inst
         (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))) halt ps) = next`
        by simp[] >>
      pop_assum (SUBST1_TAC o SYM) >>
      irule phi_provenance_plan_no_hit >> simp[] >>
      metis_tac[phiWellFormedTheory.resolve_phi_well_formed, is_var_operand_def]) >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  `is_var_operand (stack_peek d ps.ps_stack) /\
   MEM (stack_peek d ps.ps_stack) inst.inst_operands` by
    metis_tac[phi_stack_hit_operand] >>
  `resolve_phi pred inst.inst_operands = SOME (stack_peek d ps.ps_stack)` by
    (irule phi_provenance_hit_selected >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  `MEM (HD inst.inst_outputs) inst.inst_outputs` by
    (Cases_on `inst.inst_outputs` >> gvs[]) >>
  `~MEM (Var (HD inst.inst_outputs)) entry.ps_stack /\
   Var (HD inst.inst_outputs) NOTIN FDOM entry.ps_spilled` by metis_tac[] >>
  `~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
   Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled` by
    (drule_all phi_codegen_provenance_fresh >> simp[]) >>
  `~MEM (operand_to_string (stack_peek d ps.ps_stack))
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done)))` by
    (Cases_on `stack_peek d ps.ps_stack` >> gvs[is_var_operand_def, operand_to_string_def] >>
     irule phi_input_dead_at_successor >> simp[] >>
     simp[listTheory.EL_APPEND_EQN]) >>
  `inst.inst_outputs <> []` by (Cases_on `inst.inst_outputs` >> gvs[]) >>
  irule phi_provenance_plan_hit >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`halt`, `ops`] >> simp[] >>
  rpt gen_tac >> strip_tac >> drule_all phi_codegen_pending_excluded >> simp[]
QED

Theorem phi_provenance_final_resident:
  !base pred entry phis ps at.
    generated_plan_state_wf_marked base entry /\
    phi_stack_provenance base pred entry phis [] ps /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) ==>
    ((MEM at entry.ps_stack \/ at IN FDOM entry.ps_spilled) /\
     ~(MEM at entry.ps_stack /\
       ?inst. MEM inst phis /\ resolve_phi pred inst.inst_operands = SOME at)) \/
    (?inst v. MEM inst phis /\ MEM v inst.inst_outputs /\ at = Var v)
Proof
  simp[phi_stack_provenance_def, generated_plan_state_wf_marked_def,
       pred_setTheory.IN_DISJOINT] >> metis_tac[]
QED

Theorem phi_venom_rel_vars_transfer:
  !lo ps u vars st.
    venom_asm_rel lo ps u st /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (u with vs_vars := vars) lo at = operand_val u lo at) ==>
    venom_asm_rel lo ps (u with vs_vars := vars) st
Proof
  rpt gen_tac >> simp[codegenRelTheory.venom_asm_rel_def] >> strip_tac >>
  conj_tac
  >- (gvs[codegenRelTheory.plan_stack_rel_def] >> rpt strip_tac >>
      `MEM (EL i (REVERSE ps.ps_stack)) ps.ps_stack` by
        metis_tac[listTheory.EL_MEM, listTheory.MEM_REVERSE, listTheory.LENGTH_REVERSE] >>
      metis_tac[]) >>
  gvs[codegenRelTheory.plan_spill_rel_def] >> rpt strip_tac >>
  `op IN FDOM ps.ps_spilled` by
    (qpat_x_assum `FLOOKUP _ op = SOME off` mp_tac >>
     simp[finite_mapTheory.FLOOKUP_DEF] >> IF_CASES_TAC >> simp[]) >>
  metis_tac[]
QED

Theorem phi_numeric_relabel:
  !lo ps u vars st d out.
    venom_asm_rel lo ps u st /\ d < LENGTH ps.ps_stack /\
    stack_peek d ps.ps_stack <> dead_stack_marker /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (u with vs_vars := vars) lo at = operand_val u lo at) /\
    operand_val (u with vs_vars := vars) lo (Var out) =
      operand_val u lo (stack_peek d ps.ps_stack) ==>
    venom_asm_rel lo
      (ps with ps_stack := stack_poke d (Var out) ps.ps_stack)
      (u with vs_vars := vars) st
Proof
  rpt gen_tac >> strip_tac >>
  `venom_asm_rel lo ps (u with vs_vars := vars) st` by
    metis_tac[phi_venom_rel_vars_transfer] >>
  irule instSimHelpersTheory.venom_asm_rel_poke >> simp[] >>
  qpat_x_assum `venom_asm_rel lo ps u st` mp_tac >>
  simp[codegenRelTheory.venom_asm_rel_def, codegenRelTheory.plan_stack_rel_def] >>
  strip_tac >>
  qpat_x_assum `!i. i < LENGTH ps.ps_stack ==> _` (qspec_then `d` mp_tac) >>
  `stack_peek d ps.ps_stack = EL d (REVERSE ps.ps_stack)` by
    (simp[stackModelTheory.stack_peek_def, listTheory.EL_REVERSE] >>
     AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  gvs[]
QED

Theorem phi_execute_poke:
  execute_plan initial_fmp (SOPoke d op :: ops) = execute_plan initial_fmp ops
Proof
  simp[execute_plan_def, exec_stack_op_def]
QED

Theorem phi_numeric_hit_sim:
  !inst live halting ps dist ops ps' lo o2pc prog u vars st initial_fmp.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
      ps.ps_stack = SOME dist /\
    ~MEM (operand_to_string (stack_peek dist ps.ps_stack)) live /\
    generate_phi_plan inst live halting ps = (ops, ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    venom_asm_rel lo ps u st /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (u with vs_vars := vars) lo at = operand_val u lo at) /\
    operand_val (u with vs_vars := vars) lo (Var (HD inst.inst_outputs)) =
      operand_val u lo (stack_peek dist ps.ps_stack) /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' (u with vs_vars := vars) st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all genBlockSimTheory.stack_get_phi_depth_var_not_marker >> strip_tac >>
  drule_all phi_plan_hit_no_dup >>
  strip_tac >>
  `venom_asm_rel lo
      (ps with ps_stack := stack_poke dist (Var (HD inst.inst_outputs)) ps.ps_stack)
      (u with vs_vars := vars) st` by
    (irule phi_numeric_relabel >> simp[] >> metis_tac[]) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) live`
  >- (gvs[] >>
      Cases_on `popmany_plan [Var (HD inst.inst_outputs)]
        (ps with ps_stack := stack_poke dist (Var (HD inst.inst_outputs)) ps.ps_stack)` >>
      gvs[phi_execute_poke] >>
      `spill_alloc_layout_wf
        (ps with ps_stack := stack_poke dist (Var (HD inst.inst_outputs)) ps.ps_stack).ps_alloc
        (ps with ps_stack := stack_poke dist (Var (HD inst.inst_outputs)) ps.ps_stack).ps_spilled`
        by simp[] >>
      drule_all fnFrameDeepInvokeTheory.popmany_plan_sim_numeric >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[execute_plan_def, exec_stack_op_def] >> qexists `st` >> simp[asm_steps_def]
QED

Theorem phi_numeric_no_hit_sim:
  !inst live halting ps ops ps' lo o2pc prog u vars st initial_fmp.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
      ps.ps_stack = NONE /\
    generate_phi_plan inst live halting ps = (ops, ps') /\
    venom_asm_rel lo ps u st /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (u with vs_vars := vars) lo at = operand_val u lo at) ==>
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st /\
    venom_asm_rel lo ps' (u with vs_vars := vars) st /\
    st.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> drule phi_plan_no_hit >> strip_tac >>
  gvs[execute_plan_def, asm_steps_def] >>
  irule phi_venom_rel_vars_transfer >> simp[] >> metis_tac[]
QED

Theorem phi_prefix_cons_plan:
  inst.inst_opcode = PHI /\ block_len = SUC i + LENGTH rest ==>
  generate_block_insts_prefix liveness dfg cfg fn label halt 0 block_len i
    (SUC j) (inst::rest) ps =
  let (step_ops, next) = generate_phi_plan inst
        (live_vars_at liveness label (SUC i)) halt ps in
  case generate_block_insts_prefix liveness dfg cfg fn label halt 0 block_len
      (SUC i) j rest next of
    NONE => NONE
  | SOME (tail_ops, last) => SOME (step_ops ++ tail_ops, last)
Proof
  strip_tac >>
  simp[generate_block_insts_prefix_def, generate_inst_plan_def,
       is_pre_codegen_opcode_def, is_unlowered_fmp_opcode_def,
       is_unlowered_internal_call_opcode_def, is_raw_fmp_opcode_def,
       GSYM arithmeticTheory.ADD1] >>
  Cases_on `rest` >> simp[] >>
  Cases_on `generate_phi_plan inst (live_vars_at liveness label (SUC i)) halt ps` >>
  simp[]
QED

Theorem phi_eval_snoc_update:
  !done s partial inst out value.
    EVERY (\i. i.inst_opcode = PHI) done /\
    eval_phis s done = OK partial /\ inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (out,value) /\
    ~MEM out (FLAT (MAP (\i. i.inst_outputs) done)) ==>
    eval_phis s (done ++ [inst]) = OK (update_var out value partial)
Proof
  Induct >- simp[eval_phis_def] >> rpt gen_tac >>
  simp[eval_phis_def] >> strip_tac >>
  Cases_on `eval_one_phi s h` >> gvs[] >>
  rename1 `eval_one_phi s h = SOME result` >> Cases_on `result` >>
  rename1 `eval_one_phi s h = SOME (name, val)` >>
  Cases_on `eval_phis s done` >> gvs[] >>
  `name <> out` by
    metis_tac[venomExecProofsTheory.eval_one_phi_output_mem] >>
  first_x_assum drule >>
  disch_then (qspecl_then [`inst`, `out`, `value`] mp_tac) >>
  simp[] >> strip_tac >> simp[dftCommutationTheory.update_var_commutes]
QED

Theorem phi_parallel_frame_residents:
  !done inst s partial next ps fn ra lo.
    EVERY (\i. i.inst_opcode = PHI) done /\ inst.inst_opcode = PHI /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (done ++ [inst]))) /\
    eval_phis s done = OK partial /\
    eval_phis s (done ++ [inst]) = OK next /\
    ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
    Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled ==>
    frame_view fn ra next =
      (frame_view fn ra partial with vs_vars := (frame_view fn ra next).vs_vars) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra next) lo at =
      operand_val (frame_view fn ra partial) lo at)
Proof
  rpt gen_tac >> strip_tac >>
  `?out value. eval_one_phi s inst = SOME (out,value)` by
    (irule phi_eval_member_result >>
     qexistsl_tac [`next`, `done ++ [inst]`] >> simp[]) >>
  `inst.inst_outputs = [out]` by
    metis_tac[venomExecProofsTheory.eval_one_phi_imp_inst_outputs] >>
  `~MEM out (FLAT (MAP (\i. i.inst_outputs) done))` by
    gvs[listTheory.ALL_DISTINCT_APPEND] >>
  `next = update_var out value partial` by
    (drule_all phi_eval_snoc_update >> simp[]) >>
  gvs[frameViewFactsTheory.frame_view_update_var] >> conj_tac
  >- simp[update_var_def] >>
  rpt strip_tac >> irule instSimHelpersTheory.operand_val_update_var >>
  Cases_on `at` >> gvs[] >> metis_tac[]
QED

Theorem phi_parallel_selected_value:
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  eval_phis vs done = OK partial /\
  eval_phis vs (done ++ [inst]) = OK next /\
  vs.vs_prev_bb = SOME pred /\
  resolve_phi pred inst.inst_operands = SOME (Var src) ==>
  operand_val (frame_view fn ra next) lo (Var (HD inst.inst_outputs)) =
    operand_val (frame_view fn ra partial) lo (Var src)
Proof
  strip_tac >>
  `MEM inst (collect_phis bb.bb_instructions)` by simp[] >>
  `inst.inst_opcode = PHI /\ LENGTH inst.inst_outputs = 1 /\
   phi_well_formed inst.inst_operands` by metis_tac[phi_codegen_inst_shape] >>
  `MEM (Var src) inst.inst_operands` by
    metis_tac[dftCommutationTheory.resolve_phi_MEM] >>
  `FLOOKUP partial.vs_vars src = FLOOKUP vs.vs_vars src` by
    (irule phi_prefix_operand_lookup >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[listTheory.MEM_APPEND]) >>
  `MEM inst (fn_insts fn)` by
    metis_tac[allocaRemapSSATheory.mem_fn_insts_intro,
              livenessProofsTheory.collect_phis_mem] >>
  `EVERY (\i. i.inst_opcode = PHI) (done ++ [inst])` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     `MEM i (collect_phis bb.bb_instructions)` by gvs[] >>
     metis_tac[phi_codegen_inst_shape]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (done ++ [inst])))` by
    (`ssa_form fn` by gvs[codegen_ready_fn_def] >>
     drule_all phiBlockTheory.ssa_form_block_outputs_distinct >> strip_tac >>
     drule phi_collect_outputs_distinct >> simp[] >>
     simp[listTheory.ALL_DISTINCT_APPEND]) >>
  `MEM inst (done ++ [inst])` by simp[] >>
  drule_all phi_selected_frame_value >>
  simp[operand_val_def, frame_view_vars_lookup]
QED

Definition phi_run_context_def:
  phi_run_context fn bb pred entry source final <=>
    codegen_ready_fn fn /\ retpc_shape_ok fn /\
    MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
    source.vs_prev_bb = SOME pred /\
    eval_phis source (collect_phis bb.bb_instructions) = OK final /\
    (!inst op. MEM inst (collect_phis bb.bb_instructions) /\
      is_var_operand op /\ MEM op inst.inst_operands /\ MEM op entry.ps_stack ==>
      resolve_phi pred inst.inst_operands = SOME op) /\
    (!inst out. MEM inst (collect_phis bb.bb_instructions) /\ MEM out inst.inst_outputs ==>
      ~MEM (Var out) entry.ps_stack /\ Var out NOTIN FDOM entry.ps_spilled)
End

Definition phi_run_config_def:
  phi_run_config fn ra lo base pred entry source m done todo ps st <=>
    phi_stack_provenance base pred entry done todo ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (?partial. eval_phis source done = OK partial /\
      venom_asm_rel lo ps ((frame_view fn ra partial) with vs_memory := m) st)
End

Theorem phi_run_init:
  !base entry fn ra lo source m st phis pred.
  generated_plan_state_wf_marked base entry /\
  spill_alloc_layout_wf entry.ps_alloc entry.ps_spilled /\
  venom_asm_rel lo entry ((frame_view fn ra source) with vs_memory := m) st ==>
  phi_run_config fn ra lo base pred entry source m [] phis entry st
Proof
  simp[phi_run_config_def, phi_stack_provenance_init, eval_phis_def]
QED

Theorem phi_run_step:
  !base fn bb pred entry source final done inst todo ra lo m ps st halt ops next
    prog initial_fmp o2pc.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ inst::todo /\
  phi_run_config fn ra lo base pred entry source m done (inst::todo) ps st /\
  generate_phi_plan inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))) halt ps =
    (ops,next) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    phi_run_config fn ra lo base pred entry source m (done ++ [inst]) todo next st'
Proof
  rpt gen_tac >> rewrite_tac[phi_run_context_def, phi_run_config_def] >> strip_tac >>
  rename1 `phi_stack_provenance bound pred entry done (inst::todo) ps` >>
  `MEM inst (collect_phis bb.bb_instructions)` by simp[] >>
  `inst.inst_opcode = PHI /\ LENGTH inst.inst_outputs = 1 /\
   phi_well_formed inst.inst_operands` by metis_tac[phi_codegen_inst_shape] >>
  `?after. eval_phis source (done ++ [inst]) = OK after` by
    (qpat_assum `eval_phis source (collect_phis _) = OK final`
       (mp_then Any mp_tac phi_eval_take_ok) >>
     disch_then (qspec_then `SUC (LENGTH done)` mp_tac) >>
     qpat_x_assum `collect_phis _ = _` SUBST1_TAC >>
     pure_once_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
     simp[listTheory.TAKE_APPEND2, listTheory.TAKE_def,
          arithmeticTheory.ADD1]) >>
  `EVERY (\i. i.inst_opcode = PHI) done` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     metis_tac[livenessProofsTheory.collect_phis_mem, listTheory.MEM_APPEND,
       phi_codegen_inst_shape]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (done ++ [inst])))` by
    (`ssa_form fn` by gvs[codegen_ready_fn_def] >>
     drule_all phiBlockTheory.ssa_form_block_outputs_distinct >> strip_tac >>
     drule phi_collect_outputs_distinct >> simp[] >>
     simp[listTheory.ALL_DISTINCT_APPEND]) >>
  `MEM (HD inst.inst_outputs) inst.inst_outputs` by
    (Cases_on `inst.inst_outputs` >> gvs[]) >>
  `~MEM (Var (HD inst.inst_outputs)) entry.ps_stack /\
   Var (HD inst.inst_outputs) NOTIN FDOM entry.ps_spilled` by metis_tac[] >>
  `~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
   Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled` by
    (drule_all phi_codegen_provenance_fresh >> simp[]) >>
  drule_all phi_parallel_frame_residents >>
  disch_then (qspecl_then [`fn`, `ra`, `lo`] strip_assume_tac) >>
  `phi_stack_provenance bound pred entry (done ++ [inst]) todo next` by
    (drule_all phi_provenance_advance >> simp[]) >>
  `((frame_view fn ra partial with vs_memory := m) with
       vs_vars := (frame_view fn ra after).vs_vars) =
     (frame_view fn ra after with vs_memory := m)` by
    (qpat_x_assum `frame_view fn ra after = _` SUBST1_TAC >> simp[]) >>
  `!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val ((frame_view fn ra partial with vs_memory := m) with
      vs_vars := (frame_view fn ra after).vs_vars) lo at =
    operand_val (frame_view fn ra partial with vs_memory := m) lo at` by
    (simp[genFrameSimTheory.operand_val_memory_update] >> metis_tac[]) >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- suspend "no_hit" >>
  rename1 `stack_get_phi_depth _ _ = SOME dist` >> suspend "hit"
QED

Resume phi_run_step[no_hit]:
  drule_all phi_numeric_no_hit_sim >>
  disch_then (qspecl_then [`o2pc`, `prog`, `initial_fmp`] strip_assume_tac) >>
  drule phi_plan_no_hit >>
  disch_then (qspecl_then [`live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))`,
    `halt`] assume_tac) >> gvs[] >>
  qexists `st` >> simp[] >> qexists `after` >> simp[]
QED

Resume phi_run_step[hit]:
  `is_var_operand (stack_peek dist ps.ps_stack) /\
   MEM (stack_peek dist ps.ps_stack) inst.inst_operands` by
    metis_tac[phi_stack_hit_operand] >>
  `resolve_phi pred inst.inst_operands = SOME (stack_peek dist ps.ps_stack)` by
    (irule phi_provenance_hit_selected >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  `~MEM (operand_to_string (stack_peek dist ps.ps_stack))
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done)))` by
    (Cases_on `stack_peek dist ps.ps_stack` >> gvs[is_var_operand_def, operand_to_string_def] >>
     irule phi_input_dead_at_successor >> simp[] >>
     simp[listTheory.EL_APPEND_EQN]) >>
  `operand_val (frame_view fn ra after) lo (Var (HD inst.inst_outputs)) =
   operand_val (frame_view fn ra partial) lo (stack_peek dist ps.ps_stack)` by
    (Cases_on `stack_peek dist ps.ps_stack` >> gvs[is_var_operand_def] >>
     irule phi_parallel_selected_value >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `operand_val ((frame_view fn ra partial with vs_memory := m) with
      vs_vars := (frame_view fn ra after).vs_vars) lo (Var (HD inst.inst_outputs)) =
   operand_val (frame_view fn ra partial with vs_memory := m) lo
     (stack_peek dist ps.ps_stack)` by
    simp[genFrameSimTheory.operand_val_memory_update] >>
  drule_all phi_numeric_hit_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  goal_assum (drule_at Any) >> gvs[]
QED

Finalise phi_run_step

Theorem phi_run_prefix:
  !todo done base fn bb pred entry source final ra lo m ps st body block_len
    dfg cfg halt ops last prog initial_fmp o2pc.
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ todo /\
  phi_run_config fn ra lo base pred entry source m done todo ps st /\
  block_len = LENGTH done + LENGTH (todo ++ body) /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    halt 0 block_len (LENGTH done) (LENGTH todo) (todo ++ body) ps = SOME (ops,last) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    phi_run_config fn ra lo base pred entry source m (done ++ todo) [] last st'
Proof
  Induct >- (rpt gen_tac >>
    simp[generate_block_insts_prefix_def] >> strip_tac >> gvs[] >>
    qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  rpt gen_tac >> strip_tac >> rename1 `collect_phis _ = done ++ inst::todo` >>
  `inst.inst_opcode = PHI` by
    (irule (cj 1 phi_codegen_inst_shape) >>
     qexistsl_tac [`bb`, `fn`] >>
     gvs[phi_run_context_def] >> simp[]) >>
  rename1 `block_len = LENGTH done + LENGTH (inst::todo ++ suffix)` >>
  `block_len = SUC (LENGTH done) + LENGTH (todo ++ suffix)` by simp[] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[phi_prefix_cons_plan] >>
  Cases_on `generate_phi_plan inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (LENGTH done))) halt ps` >>
  rename1 `generate_phi_plan _ _ _ _ = (step_ops, next)` >>
  simp[AllCaseEqs()] >> strip_tac >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
      listTheory.EVERY_APPEND] >>
  `collect_phis bb.bb_instructions = done ++ inst::todo` by simp[] >>
  drule_all phi_run_step >> disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `asm_steps lo o2pc prog _ st = AsmOK middle` >>
  `collect_phis bb.bb_instructions = (done ++ [inst]) ++ todo` by simp[] >>
  first_x_assum (qspec_then `done ++ [inst]` assume_tac) >>
  `asm_block_at prog middle.as_pc (execute_plan initial_fmp tail_ops)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  first_x_assum drule >> simp[] >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `suffix` mp_tac) >>
  rule_assum_tac (SIMP_RULE bool_ss
    [arithmeticTheory.ADD1, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  simp_tac bool_ss [arithmeticTheory.ADD1,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> disch_then drule_all >> disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `asm_steps lo o2pc prog _ middle = AsmOK result_st` >>
  qexists `result_st` >> simp[] >> conj_tac
  >- (qpat_assum `asm_steps _ _ _ _ st = AsmOK middle`
        (mp_then Any mp_tac stackOpSimTheory.asm_steps_add_ok) >>
      disch_then (qspec_then `LENGTH (execute_plan initial_fmp tail_ops)` mp_tac) >> simp[]) >>
  metis_tac[listTheory.APPEND_ASSOC, listTheory.APPEND]
QED

Theorem phi_run_final:
  !base fn bb pred entry source final ra lo m last st.
  phi_run_context fn bb pred entry source final /\
  phi_run_config fn ra lo base pred entry source m
    (collect_phis bb.bb_instructions) [] last st ==>
  phi_stack_provenance base pred entry (collect_phis bb.bb_instructions) [] last /\
  spill_alloc_layout_wf last.ps_alloc last.ps_spilled /\
  venom_asm_rel lo last ((frame_view fn ra final) with vs_memory := m) st
Proof
  simp[phi_run_context_def, phi_run_config_def] >> rpt strip_tac >> gvs[]
QED

Theorem phi_run_final_memory:
  !base fn bb pred entry source final ra lo m last st.
  phi_run_context fn bb pred entry source final /\
  phi_run_config fn ra lo base pred entry source m
    (collect_phis bb.bb_instructions) [] last st ==>
  memory_rel last.ps_alloc m st.as_memory
Proof
  rpt gen_tac >> strip_tac >> drule_all phi_run_final >> strip_tac >>
  drule fnFrameBoundaryEntryParamsTheory.entry_local_memory_footprint >> simp[]
QED

Theorem phi_run_final_support:
  !base fn bb pred entry source final ra lo m last st at.
  phi_run_context fn bb pred entry source final /\
  phi_run_config fn ra lo base pred entry source m
    (collect_phis bb.bb_instructions) [] last st /\
  generated_plan_state_wf_marked base entry /\
  (MEM at last.ps_stack \/ at IN FDOM last.ps_spilled) ==>
  ((MEM at entry.ps_stack \/ at IN FDOM entry.ps_spilled) /\
   ~(MEM at entry.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
      resolve_phi pred inst.inst_operands = SOME at)) \/
  (?inst v. MEM inst (collect_phis bb.bb_instructions) /\ MEM v inst.inst_outputs /\ at = Var v)
Proof
  rpt gen_tac >> strip_tac >> drule_all phi_run_final >> strip_tac >>
  metis_tac[phi_provenance_final_resident]
QED

Theorem phi_run_final_alias:
  !base fn bb pred entry source final ra lo m last st dfg.
  phi_run_context fn bb pred entry source final /\
  phi_run_config fn ra lo base pred entry source m
    (collect_phis bb.bb_instructions) [] last st /\
  generated_plan_state_wf_marked base entry /\
  dfg = dfg_build_function fn /\
  (!op v. (MEM op entry.ps_stack \/ op IN FDOM entry.ps_spilled) /\
    ~(MEM op entry.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
      resolve_phi pred inst.inst_operands = SOME op) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
  (!at. MEM at entry.ps_stack \/ at IN FDOM entry.ps_spilled ==>
    operand_val (frame_view fn ra source) lo at =
    operand_val (frame_view fn ra source) lo (normalize_operand dfg [] at)) ==>
  !at. MEM at last.ps_stack \/ at IN FDOM last.ps_spilled ==>
    operand_val (frame_view fn ra final) lo at =
    operand_val (frame_view fn ra final) lo (normalize_operand dfg [] at)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  drule_all phi_run_final_support >> disch_then DISJ_CASES_TAC
  >- (irule phi_eval_preserves_frame_alias >>
      qexistsl_tac [`collect_phis bb.bb_instructions`, `source`] >>
      gvs[phi_run_context_def] >>
      rpt strip_tac >>
      `~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
        (qpat_x_assum `!op v. _` irule >> qexists_tac `at` >> simp[]) >>
      gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      metis_tac[livenessProofsTheory.collect_phis_mem]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  `ssa_form fn` by gvs[phi_run_context_def, codegen_ready_fn_def] >>
  `MEM inst (fn_insts fn)` by
    (gvs[phi_run_context_def] >>
     metis_tac[allocaRemapSSATheory.mem_fn_insts_intro,
       livenessProofsTheory.collect_phis_mem]) >>
  `inst.inst_opcode = PHI` by
    metis_tac[phi_codegen_inst_shape, phi_run_context_def] >>
  metis_tac[phi_output_normalize_self]
QED

Theorem phi_local_frame_transport:
  !ctx cp lo fn ra rest mem0 ps vs st last final endpoint insts k r.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  eval_phis vs insts = OK final /\
  venom_asm_rel lo last
    (frame_view fn ra final with vs_memory := st.as_memory) endpoint /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= last.ps_alloc.sa_spill_base /\
  last.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  fn_frame_inv ctx cp lo fn ra rest mem0 last (final with vs_inst_idx := k)
    (endpoint with as_stack := endpoint.as_stack ++ rest)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >> strip_tac >>
  `final.vs_memory = vs.vs_memory /\ final.vs_halted = vs.vs_halted /\
   final.vs_initial_fmp = vs.vs_initial_fmp` by
    (qpat_x_assum `final = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `context_memory_rel cplan (frame_view fn ra final).vs_memory st.as_memory` by
    gvs[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  `context_venom_asm_rel cplan lo last (frame_view fn ra final) endpoint` by
    (irule fnFrameBoundaryEntryParamsTheory.entry_local_to_context_memory >>
     conj_tac >- (qexists_tac `r` >> simp[]) >>
     qexists_tac `st.as_memory` >> simp[]) >>
  `memory_rel last.ps_alloc st.as_memory endpoint.as_memory` by
    gvs[venom_asm_rel_def] >>
  `!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    read_byte b endpoint.as_memory = read_byte b st.as_memory` by
    (rpt strip_tac >>
     irule fnFrameBoundaryEntryParamsTheory.entry_local_footprint_outside_closure >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!s op. operand_val (s with vs_inst_idx := k) lo op = operand_val s lo op` by
    (gen_tac >> Cases >> simp[operand_val_def]) >>
  simp[fn_frame_inv_def] >> conj_tac >- gvs[fn_frame_inv_def] >>
  conj_tac >- gvs[fn_frame_inv_def] >> conj_tac
  >- (pure_rewrite_tac[context_venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def] >>
      `!op. operand_val (frame_view fn ra (final with vs_inst_idx := k)) lo op =
        operand_val (frame_view fn ra final) lo op` by
        (Cases >> simp[frame_view_def, operand_val_def]) >>
      simp[] >> gvs[context_venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def,
        frame_view_def]) >>
  conj_tac >- (gvs[fn_frame_inv_def] >> metis_tac[]) >>
  qexists_tac `r` >> simp[]
QED

Theorem phi_entry_outputs_absent:
  !fn bb pred entry dfg.
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  (!op v. (MEM op entry.ps_stack \/ op IN FDOM entry.ps_spilled) /\
    ~(MEM op entry.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
      resolve_phi pred inst.inst_operands = SOME op) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) ==>
  !inst out. MEM inst (collect_phis bb.bb_instructions) /\ MEM out inst.inst_outputs ==>
    ~MEM (Var out) entry.ps_stack /\ Var out NOTIN FDOM entry.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `~(?phi. MEM phi (collect_phis bb.bb_instructions) /\
    resolve_phi pred phi.inst_operands = SOME (Var out))` by
    (strip_tac >>
     `MEM (Var out) phi.inst_operands` by metis_tac[dftCommutationTheory.resolve_phi_MEM] >>
     metis_tac[phi_prefix_output_not_operand]) >>
  `MEM out (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     qexists_tac `inst.inst_outputs` >> simp[] >>
     qexists_tac `inst` >> simp[] >>
     metis_tac[livenessProofsTheory.collect_phis_mem]) >>
  metis_tac[]
QED

Theorem phi_eval_collect:
  !insts s. eval_phis s (collect_phis insts) = eval_phis s insts
Proof
  Induct >- simp[collect_phis_def, eval_phis_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[collect_phis_def, eval_phis_def]
QED

(* The entry-stack-agnostic PHI prefix simulation.  Entry residents are
   tracked by provenance, not fixed depths: dead-output pops may permute
   the remaining hits.  Parallel evaluation preserves pending raw source
   values; freshness is needed only for the final residents and their
   normalized roots, not for intermediate alias relations.  The join and
   single-predecessor wrappers discharge the entry-hit premises. *)
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
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  rename1 `generated_plan_state_wf_marked bound ps` >>
  rename1 `non_param_insts bb = phis ++ suffix` >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `non_param_insts bb = bb.bb_instructions` by
    (irule phi_non_entry_non_param_insts >> qexists_tac `fn` >>
     gvs[codegen_ready_fn_def]) >>
  `phis = collect_phis bb.bb_instructions` by
    (qspecl_then [`phis`, `suffix`] mp_tac phi_prefix_is_collect_phis >>
     metis_tac[]) >>
  suspend "prepare"
QED

Resume phi_prefix_hits_frame_sim[prepare]:
  `get_params bb.bb_instructions = []` by
    (Cases_on `fn.fn_blocks` >>
     gvs[codegen_ready_fn_def, callLayoutDefsTheory.canonical_param_prefix_def,
       callLayoutDefsTheory.no_param_insts_def, listTheory.EVERY_MEM] >>
     Cases_on `bb.bb_instructions` >- simp[get_params_def] >>
     rename1 `bb.bb_instructions = inst::tail` >>
     `~is_param_opcode inst.inst_opcode` by
       (qpat_x_assum `!bb'. MEM bb' _ ==> _` (qspec_then `bb` mp_tac) >> simp[]) >>
     simp[get_params_def]) >>
  `eval_phis vs (collect_phis bb.bb_instructions) = OK s_phi` by
    simp[phi_eval_collect] >>
  `phi_run_context fn bb pred ps vs s_phi` by
    (rewrite_tac[phi_run_context_def] >> simp[] >>
     rpt gen_tac >> strip_tac >> irule phi_entry_outputs_absent >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  `LENGTH phis <= LENGTH (phis ++ suffix)` by simp[] >>
  qspecl_then [`LENGTH phis`, `phis ++ suffix`] mp_tac
    (INST_TYPE [``:'a`` |-> ``:cfg_analysis``] generate_block_insts_plan_split) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => CONV_TAC (LAND_CONV (REWR_CONV (SPEC_ALL th)))) >>
  simp_tac (srw_ss()) [listTheory.DROP_APPEND] >> strip_tac >>
  suspend "run"
QED

Resume phi_prefix_hits_frame_sim[run]:
  rename1 `ops = phi_ops ++ body_ops` >>
  rename1 `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ ps = SOME (phi_ops,ps1)` >>
  `r.sr_spill_base <= ps1.ps_alloc.sa_spill_base /\
   ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (drule allocMonoTheory.generate_block_insts_plan_spill_base >> strip_tac >>
     drule allocMonoTheory.generate_block_insts_plan_next_offset >> strip_tac >> simp[]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) phi_ops` by
    (simp[listTheory.EVERY_MEM] >> Cases >> simp[] >> metis_tac[listTheory.MEM_APPEND]) >>
  `asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp phi_ops)` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  drule fnFrameTerminalPrepTheory.fn_frame_inv_local_state >> strip_tac >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    gvs[generated_plan_state_wf_marked_def] >>
  `phi_run_config fn ra lo bound pred ps vs st.as_memory [] phis ps
    (st with as_stack := top)` by (irule phi_run_init >> simp[]) >>
  `collect_phis bb.bb_instructions = [] ++ phis` by simp[] >>
  `LENGTH bb.bb_instructions = LENGTH [] + LENGTH (phis ++ suffix)` by
    (qpat_x_assum `non_param_insts bb = phis ++ suffix` mp_tac >>
     qpat_x_assum `non_param_insts bb = bb.bb_instructions` mp_tac >>
     simp_tac (srw_ss()) [] >> rpt strip_tac >> gvs[]) >>
  `generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) (LENGTH []) (LENGTH phis)
    (phis ++ suffix) ps = SOME (phi_ops, ps1)` by
    (qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ ps = _` mp_tac >>
     qpat_x_assum `liveness = liveness_analyze fn` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `get_params bb.bb_instructions = []` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) []) >>
  `asm_block_at prog (st with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp phi_ops)` by simp[] >>
  `?endpoint.
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp phi_ops))
      (st with as_stack := top) = AsmOK endpoint /\
    endpoint.as_pc = (st with as_stack := top).as_pc +
      LENGTH (execute_plan cplan.cp_initial_fmp phi_ops) /\
    phi_run_config fn ra lo bound pred ps vs st.as_memory ([] ++ phis) [] ps1 endpoint` by
    (irule (INST_TYPE [``:'a`` |-> ``:cfg_analysis``] phi_run_prefix) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`LENGTH bb.bb_instructions`, `suffix`, `cfg`, `dfg`, `s_phi`, `bb_is_halting bb`] >>
     rule_assum_tac (SIMP_RULE bool_ss [listTheory.LENGTH]) >>
     simp_tac bool_ss [listTheory.LENGTH] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "lift"
QED

Resume phi_prefix_hits_frame_sim[lift]:
  rename1 `asm_steps lo o2pc prog _ (st with as_stack := top) = AsmOK endpoint` >>
  `phi_run_config fn ra lo bound pred ps vs st.as_memory
    (collect_phis bb.bb_instructions) [] ps1 endpoint` by
    (qpat_x_assum `phi_run_config _ _ _ _ _ _ _ _ _ [] ps1 endpoint` mp_tac >>
     pure_rewrite_tac[listTheory.APPEND] >>
     qpat_x_assum `phis = collect_phis bb.bb_instructions` (fn th => rewrite_tac[th]) >>
     simp_tac bool_ss []) >>
  drule_all phi_run_final >> strip_tac >>
  `fn_frame_inv ctx cplan lo fn ra rest mem0 ps1
    (s_phi with vs_inst_idx := LENGTH phis)
    (endpoint with as_stack := endpoint.as_stack ++ rest)` by
    (irule phi_local_frame_transport >> conj_tac
     >- (qexists_tac `r` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`bb.bb_instructions`, `ps`, `st`, `vs`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule asmFrameTheory.asm_steps_frame >>
  disch_then (qspec_then `rest` mp_tac) >>
  `st with as_stack := top ++ rest = st` by
    (qpat_x_assum `st.as_stack = top ++ rest` (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  qpat_x_assum `st with as_stack := top ++ rest = st` (fn th => rewrite_tac[th]) >> strip_tac >>
  qexistsl_tac [`phi_ops`, `ps1`, `body_ops`,
    `LENGTH (execute_plan cplan.cp_initial_fmp phi_ops)`,
    `endpoint with as_stack := endpoint.as_stack ++ rest`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `endpoint.as_pc = _` mp_tac >> simp_tac (srw_ss()) []) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >> irule phi_run_final_alias >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qpat_assum `phi_run_config _ _ _ _ _ _ _ _ (collect_phis _) [] ps1 endpoint`
    (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise phi_prefix_hits_frame_sim
