(*
 * The planner state partway through a block's instructions.
 *
 * generate_block_insts_plan takes each instruction's lookahead (the
 * liveness after it, whether the next one is a terminator) from the list
 * it is given, so planning a prefix of the instructions on its own plans
 * the prefix's last instruction as if it ended the block.  The prefix
 * planner below stops after j instructions but takes the lookahead from
 * the whole list, so its state is the one the block's plan reaches.
 *
 * Also generated_plan_state_wf_marked, the planner-state well-formedness
 * the block induction can keep: a cleanup elision (clean_stack_plan's
 * mark_dead_stack) leaves dead_stack_marker in several stack slots, so
 * generated_plan_state_wf's ALL_DISTINCT ps_stack fails after it.
 *
 * TOP-LEVEL:
 *   generate_block_insts_prefix      - the first j instructions' plan
 *   generate_block_insts_plan_split  - a block's plan is its prefix's plan
 *                                      followed by the rest's
 *   generated_plan_state_wf_marked   - generated_plan_state_wf, with
 *                                      repeated dead_stack_marker slots
 *   generated_plan_state_wf_marked_wf - generated_plan_state_wf implies it
 *)

Theory fnPlanPrefix
Ancestors
  callLayoutDefs fnLiveDefDom removeUnusedSsaProofs dominatorProofs dominatorAnalysisProps
  livenessDefs livenessProofs codegenReadyCompute venomExecProofs
  stackPlanOps alist fnPlanLineageReorder genBlockSim stackPlanGen stackPlanTypes venomInst rich_list list arithmetic cfgAnalysisProps venomWf simplifyCfgDefs

Definition generate_block_insts_prefix_def:
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (0:num) insts ps =
    SOME ([] : stack_op list, ps) /\
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (SUC j) [] ps = NONE /\
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (SUC j) (inst :: rest) ps =
    let next_live =
      if rest = [] then live_vars_at liveness bb_label block_len
      else live_vars_at liveness bb_label (i + n_params + 1) in
    let next_is_term =
      case rest of
        [] => F
      | next_i :: _ => is_terminator next_i.inst_opcode in
    case generate_inst_plan liveness dfg cfg fn inst
           next_live is_halting next_is_term bb_label ps of
      NONE => NONE
    | SOME (step_ops, ps') =>
        case generate_block_insts_prefix liveness dfg cfg fn bb_label
               is_halting n_params block_len (i + 1) j rest ps' of
          NONE => NONE
        | SOME (rest_ops, ps'') => SOME (step_ops ++ rest_ops, ps'')
End

Theorem generate_block_insts_plan_split:
  !j insts liveness dfg cfg fn bb_label is_halting n_params block_len i ps
   ops ps_end.
    j <= LENGTH insts ==>
    (generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
       n_params block_len i insts ps = SOME (ops, ps_end) <=>
     ?pre ps_mid post.
       generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
         n_params block_len i j insts ps = SOME (pre, ps_mid) /\
       generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
         n_params block_len (i + j) (DROP j insts) ps_mid =
         SOME (post, ps_end) /\
       ops = pre ++ post)
Proof
  Induct_on `j`
  >- simp[generate_block_insts_prefix_def] >>
  gen_tac >> Cases_on `insts` >- simp[] >>
  first_x_assum (qspec_then `t` mp_tac) >>
  disch_tac >> rpt gen_tac >> disch_tac >> gvs[] >>
  simp[Once generate_block_insts_plan_def, generate_block_insts_prefix_def,
       LET_THM, AllCaseEqs(), PULL_EXISTS] >>
  `i + SUC j = i + 1 + j` by simp[] >> pop_assum SUBST1_TAC >>
  eq_tac >> strip_tac >> gvs[] >>
  rpt (first_assum $ irule_at Any) >> simp[]
QED

Definition generated_plan_state_wf_marked_def:
  generated_plan_state_wf_marked base (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack) /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)
End

Theorem wf_marked_cleanup_fields:
  !base ps h promised.
    generated_plan_state_wf_marked base
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) <=>
    generated_plan_state_wf_marked base ps
Proof
  simp[generated_plan_state_wf_marked_def, planSpillBoundsTheory.plan_slots_bounded_def]
QED

Theorem codegen_ready_fn_no_marker:
  !fn. codegen_ready_fn fn ==>
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks
Proof
  simp[codegen_ready_fn_def, EVERY_MEM] >> rpt strip_tac >>
  `codegen_ready_inst inst` by metis_tac[] >>
  gvs[codegen_ready_inst_def]
QED

(* generated_plan_state_wf doesn't keep the marker out of the spill map,
   hence the second premise. *)
Theorem generated_plan_state_wf_marked_wf:
  !base ps.
    generated_plan_state_wf base ps /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled ==>
    generated_plan_state_wf_marked base ps
Proof
  rw[generated_plan_state_wf_def, generated_plan_state_wf_marked_def] >>
  irule FILTER_ALL_DISTINCT >> simp[]
QED

Theorem initial_cleanup_wf_marked:
  generated_plan_state_wf_marked spill_base
    (init_cleanup_plan_state ch growth spill_base lbl_ctr)
Proof
  simp[generated_plan_state_wf_marked_def,
       planSpillBoundsTheory.plan_slots_bounded_def,
       planSpillBoundsTheory.alloc_slots_bounded_def,
       doSwapSimTheory.spill_alloc_layout_wf_def,
       init_cleanup_plan_state_def, init_plan_state_def, init_spill_alloc_def]
QED

Theorem non_param_insts_last_jmp:
  bb.bb_instructions <> [] /\
  (LAST bb.bb_instructions).inst_opcode = JMP ==>
  non_param_insts bb <> [] /\
  LAST (non_param_insts bb) = LAST bb.bb_instructions
Proof
  strip_tac >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++
                           [LAST bb.bb_instructions]` by
    metis_tac[APPEND_FRONT_LAST] >>
  `non_param_insts bb =
    FILTER (\inst. ~is_param_opcode inst.inst_opcode)
      (FRONT bb.bb_instructions) ++ [LAST bb.bb_instructions]` by
    (simp[non_param_insts_def] >>
     qpat_x_assum `bb.bb_instructions = _` (fn th =>
       CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[FILTER_APPEND_DISTRIB, is_param_opcode_def]) >>
  simp[LAST_APPEND_NOT_NIL]
QED

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

Theorem phi_restore_reorder_target_absence:
  restore_spilled_plan targets ps = (restore_ops, ps1) /\
  reorder_plan dfg targets ps1 = (reorder_ops, ps2) /\
  MEM at targets ==>
  at NOTIN FDOM ps2.ps_spilled
Proof
  strip_tac >> drule phi_restore_spilled_domain >> strip_tac >>
  `at NOTIN FDOM ps1.ps_spilled` by simp[] >>
  drule_all reorder_plan_pending_not_spilled >>
  disch_then (qspec_then `dfg` mp_tac) >> simp[]
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
    (drule_all non_param_insts_last_jmp >> simp[]) >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    phi_terminal_jmp_spills_empty >> simp[] >>
  disch_then (qspecl_then [`succ`, `targets`] mp_tac) >> simp[]
QED

Theorem join_predecessor_jmp_shape:
  !fn pred pb bb.
    codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1 ==>
    pb.bb_label = pred /\ pb.bb_instructions <> [] /\
    (LAST pb.bb_instructions).inst_opcode = JMP
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac lookup_block_member_label >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfg_edge_symmetry_uncond] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (`cfg_preds_of (cfg_analyze fn) bb.bb_label <> []` by
       (strip_tac >> gvs[]) >>
     `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 0` by
       metis_tac[LENGTH_NIL] >> decide_tac) >>
  gvs[codegen_ready_fn_def, block_entries_ready_def, EVERY_MEM] >>
  qpat_x_assum `!blk. MEM blk fn.fn_blocks ==> (_ \/ _)` (qspec_then `bb` mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspec_then `pb.bb_label` mp_tac) >>
  simp[NULL_EQ]
QED

Theorem join_predecessor_single_successor:
  !fn pred pb bb.
    codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1 ==>
    (LAST pb.bb_instructions).inst_operands = [Label bb.bb_label] /\
    cfg_succs_of (cfg_analyze fn) pred = [bb.bb_label]
Proof
  rpt gen_tac >> strip_tac >>
  drule_all join_predecessor_jmp_shape >> strip_tac >>
  imp_res_tac lookup_block_member_label >>
  `wf_function fn /\ fn_inst_wf fn` by
    gvs[codegen_ready_fn_def] >>
  `inst_wf (LAST pb.bb_instructions)` by
    (gvs[fn_inst_wf_def] >> first_x_assum irule >>
     qexists_tac `pb` >> simp[] >>
     Cases_on `pb.bb_instructions` >> gvs[MEM_LAST]) >>
  `cfg_succs_of (cfg_analyze fn) pred = bb_succs pb` by
    metis_tac[cfg_analyze_preserves_bb_succs] >>
  gvs[inst_wf_def] >>
  Cases_on `pb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, is_terminator_def,
      venomStateTheory.get_label_def, nub_def]
QED

Theorem release_dead_spills_stack:
  (release_dead_spills nl ps).ps_stack = ps.ps_stack
Proof
  simp[release_dead_spills_def] >>
  qspec_tac (`FILTER (\(op,off). case op of Lit v => T | Var v => ~MEM v nl | Label v => T)
    (fmap_to_alist ps.ps_spilled)`, `xs`) >>
  qid_spec_tac `ps` >> Induct_on `xs` >> simp[] >>
  Cases_on `h` >> simp[]
QED

(* Dominance boundaries moved from fnLineageStatic for acyclic inventory use. *)
Theorem ready_entry_no_preds:
  codegen_ready_fn fn /\ entry_block fn = SOME eb ==>
  cfg_preds_of (cfg_analyze fn) eb.bb_label = []
Proof
  strip_tac >> gvs[codegen_ready_fn_def, block_entries_ready_def, NULL_EQ]
QED

Theorem small_preds_not_dominates_pred:
  codegen_ready_fn fn /\ fn_reachable fn pred /\
  fn_cfg_edge fn pred succ /\
  LENGTH (cfg_preds_of (cfg_analyze fn) succ) <= 1 ==>
  ~fn_dominates fn succ pred
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `?eb. entry_block fn = SOME eb` by
    (gvs[wf_function_def, fn_has_entry_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) succ)` by
    metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond] >>
  `succ <> eb.bb_label` by metis_tac[ready_entry_no_preds, MEM] >>
  `cfg_reachable_of (cfg_analyze fn) succ` by
    metis_tac[fn_reachable_step, fn_reachable_cfg_analyze] >>
  drule_all exists_pred_not_dominated >>
  disch_then (qx_choose_then `other` strip_assume_tac) >>
  `other = pred` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) succ` >> gvs[] >>
     rename1 `SUC (LENGTH rest) <= 1` >> Cases_on `rest` >> gvs[]) >>
  metis_tac[fn_dominates_cfg_analyze]
QED

Theorem dominating_def_excludes_outputs:
  codegen_ready_fn fn /\
  MEM def_bb fn.fn_blocks /\ MEM inst def_bb.bb_instructions /\
  MEM v inst.inst_outputs /\ fn_dominates fn def_bb.bb_label pred /\
  MEM target fn.fn_blocks /\ ~fn_dominates fn target.bb_label pred ==>
  ~MEM v (FLAT (MAP (\i. i.inst_outputs) target.bb_instructions))
Proof
  strip_tac >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[ssa_unique_output_block]
QED

Theorem live_end_dominating_def:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
  ?def_bb inst. MEM def_bb fn.fn_blocks /\ MEM inst def_bb.bb_instructions /\
    MEM v inst.inst_outputs /\ fn_dominates fn def_bb.bb_label lbl
Proof
  strip_tac >>
  mp_tac (live_def_dominates |> Q.SPEC `fn` |> Q.SPEC `lbl` |>
    Q.SPEC `bb` |> Q.SPEC `LENGTH bb.bb_instructions` |> Q.SPEC `v`) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> decide_tac)) >>
  metis_tac[]
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

Theorem phi_disjoint_use_indices:
  !phis i j v.
    phi_uses_disjoint phis /\ i < LENGTH phis /\ j < LENGTH phis /\
    MEM v (inst_uses (EL i phis)) /\ MEM v (inst_uses (EL j phis)) ==> i = j
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> Cases_on `j` >>
  gvs[phi_uses_disjoint_def, EVERY_MEM] >> metis_tac[EL_MEM]
QED

Theorem phi_codegen_edge_wf:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst (collect_phis bb.bb_instructions) ==>
  phi_edge_uses_wf fn bb inst
Proof
  strip_tac >> drule livenessProofsTheory.collect_phis_mem >> strip_tac >>
  gvs[codegen_ready_fn_def, venomWfTheory.def_dominates_uses_def] >>
  metis_tac[]
QED

(* Canonical PHI membership facts relocated from fnFrameStepsPhi. *)
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

(* Canonical readiness boundaries relocated from fnFrameStepsPhi. *)
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

Theorem phi_codegen_input_dead_after_prefix:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v (inst_uses phi) ==>
  ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >> drule_all phi_codegen_block_ready >>
  simp[phi_block_ready_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ready_small_preds_no_phis:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1 ==>
  collect_phis bb.bb_instructions = []
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
  metis_tac[NULL_EQ]
QED

(* A block other than the entry has no parameter instructions. *)
Theorem nonentry_block_no_params:
  !fn lbl bb.
    canonical_param_prefix fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks ==>
    get_params bb.bb_instructions = [] /\
    non_param_insts bb = bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
  `no_param_insts bb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def, EVERY_MEM]) >>
  gvs[no_param_insts_def] >>
  conj_tac >- (Cases_on `bb.bb_instructions` >> gvs[get_params_def]) >>
  irule non_param_insts_all_neq >> simp[]
QED

Theorem regional_entry_structure:
  codegen_ready_fn fn ==>
  fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label /\
  lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks = SOME (HD fn.fn_blocks) /\
  fn_reachable fn (HD fn.fn_blocks).bb_label /\
  collect_phis (HD fn.fn_blocks).bb_instructions = [] /\
  bb_well_formed (HD fn.fn_blocks)
Proof
  strip_tac >>
  `wf_function fn /\ block_entries_ready (cfg_analyze fn) fn` by
    gvs[codegen_ready_fn_def] >>
  `fn.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `bb_well_formed (HD fn.fn_blocks)` by
    (Cases_on `fn.fn_blocks` >> gvs[wf_function_def]) >>
  Cases_on `fn.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm,
      block_entries_ready_def, NULL_EQ, fn_reachable_def, relationTheory.RTC_REFL]
QED
