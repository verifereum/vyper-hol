(*
 * The cross-block DFG alias invariant of the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation.
 *
 * gen_fn_frame_simulation assumes that every operand on the planner's
 * stack or in its spill map has the value of its ASSIGN-chain root
 * (normalize_operand), read through the frame view.  The planner's
 * alias-only reorder steps rely on it.  The induction must re-establish
 * it at the successor block, whose lineage state carries the stack and
 * spill map the current block's code leaves (fnPlanLineage).
 *
 * TOP-LEVEL:
 *   lineage_alias_successor — one block preserves the invariant
 *)

Theory fnAliasInv
Ancestors
  fnPlanLineage frameRel codegenRel unitShapeDefs stackPlanGen stackPlanTypes
  venomExecSemantics venomState livenessDefs dfgDefs cfgDefs
  fnLineageInv fnLiveDefDom fnLineageStatic fnBlockPlanStaticRegion
  fnBlockPlanStaticBodyPrefix fnBlockPlanStatic fnFrameStepsPhi fnEntryParams
  fnAliasStep fnAliasInvBridges fnAliasInvBody fnAliasInvPrefix fnAliasInvPhi
  fnPlanLineageJoin fnPlanPrefix cfgHelpers cfgAnalysisProps

(* Used at each jump of the block induction, for the successor's alias
   premise.  The invariant reads only ps_stack and ps_spilled, so the
   lineage entry state of the successor (its DFS state with ps_after's
   stack and spill map, lineage_entry) inherits it from ps_after.  The
   block's code is the one lineage_state_block_plan regenerates from the
   lineage state ps, with the cleanup fields it chooses.

   The ownership premise is the planner's static entry invariant: every
   variable live into the block along the edge taken is on the stack or
   spilled.  Without it a block could copy (ASSIGN) a variable the planner
   doesn't hold, whose value need not be its root's after a loop
   iteration, and push the copy.

   Why it should hold: a variable defined in the block by ASSIGN of an
   owned operand takes that operand's value, which is its root's; any
   other definition is its own root.  A root's value only changes when
   its definition runs again, and by SSA and def_dominates_uses a
   variable derived from it is then no longer live, so the planner has
   dropped it: popped, overwritten by a PHI poke, or left behind at the
   join reorder of a JMP (every loop header is a join).  An INVOKE
   changes only its own outputs among the caller's variables.  Return-PC
   variables all read ra in the frame view, and so do their roots. *)
(* Proof outline (argon).  Write ps0 for the cleanup-updated ps; it has
   ps's stack and spill map.  generate_block_plan runs prepare_params_plan,
   clean_stack_plan, then the instruction loop; run_block runs eval_phis,
   then one step_inst per non-PHI instruction.  Let k be the index after the
   PARAM or PHI prefix.  Carry, for k <= i <= LENGTH bb.bb_instructions:
     static:  regional_body_lower_inv liveness dfg spill_base bb i ps_i
              (marked wf, live coverage at (label,i), suffix output/root
              freshness of every slot and its root);
     dynamic: the alias equation for every slot of ps_i at vs_i.
   Establishing it at k, by the shape of lineage_state:
   - entry block: regional_entry_lower_start; entry_params_inventory and
     entry_param_normalize make every slot a PARAM output (its own root)
     with an empty spill map.
   - non-entry, no PHIs (k = 0): prepare_params_plan is the identity;
     clean_stack_plan only pops or writes dead_stack_marker, so the alias
     equation carries over (regional_clean_stack_identity_predicate);
     static side from regional_clean_stack_marked_wf,
     regional_clean_stack_protected_ownership and lineage_entry_non_phi_fresh.
   - non-entry with PHIs (joins only, phis_at_joins): clean_stack_plan is
     the identity, spill map empty (phi_join_entry_spill_empty).  Static:
     regional_selected_phi_inv at 0 (lineage_entry_inventory,
     lineage_entry_non_phi_fresh, regional_lineage_phi_source), stepped by
     regional_selected_phi_inv_prefix, converted by
     regional_selected_phi_exit_lower_inv.  Dynamic: phi_selected_input_vars
     plus the entry-coverage premise put each selected source on the stack,
     where regional_selected_phi_inv's uniqueness makes it the PHI's
     resident operand; then phi_stack_provenance / phi_provenance_advance /
     phi_run_final_alias (entry residents keep value and root,
     phi_eval_preserves_frame_alias; PHI outputs are their own roots,
     phi_output_normalize_self).
   The SSA lifetime fact is lineage_entry_inventory (slots of a lineage
   entry state are live out of the predecessor) with lineage_entry_small_fresh
   / lineage_entry_non_phi_fresh: a slot's variable and root strictly
   dominate the block, so neither is an output of it.  These need no
   generate_fn_plan_with_cleanup_analyzed premise, unlike
   lineage_state_static and regional_lineage_selected_phi_inv.
   Body step i: regional_body_lower_inv_step (static) and
   alias_step_preserve (dynamic), whose side conditions come from
   regional_body_lower_inv_operand_lookup, regional_body_lower_inv_output_roots
   and, at the final JMP, regional_jmp_target_static.  At the end
   ps_i = ps_after and vs_i = vs'. *)
Theorem lineage_alias_successor:
  !fuel ctx lo liveness dfg cfg ch growth spill_base lbl_ctr fn lbl bb ps h
   promised block_ops ps_after ra vs vs'.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    retpc_shape_ok fn /\ opaque_use_ok fn /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    vs.vs_current_bb = lbl /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan liveness dfg cfg fn bb
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    (!pred x. vs.vs_prev_bb = SOME pred /\
       MEM x (input_vars_from pred bb.bb_instructions
                (live_vars_at liveness lbl 0)) ==>
       MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    run_block fuel ctx bb vs = OK vs' /\ ~vs'.vs_halted
    ==>
    !at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs') lo at =
      operand_val (frame_view fn ra vs') lo (normalize_operand dfg [] at)
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  gvs[] >>
  `MEM bb fn.fn_blocks` by metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    metis_tac[fnPlanLineageJoinTheory.lineage_state_reachable] >>
  `fn_reachable fn bb.bb_label` by
    metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[venomWfPropsTheory.fn_reachable_in_cfg_dfs_pre] >>
  drule_all regional_canonical_body_layout >> strip_tac >>
  Cases_on `bb = HD fn.fn_blocks`
  >- (qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
      simp_tac (srw_ss() ++ boolSimps.LET_ss) [generate_block_plan_def] >>
      asm_rewrite_tac[] >>
      pairarg_tac >> gvs[] >>
      pairarg_tac >> gvs[] >>
      simp_tac std_ss [AllCaseEqs()] >> strip_tac >> gvs[] >>
      `cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = []` by
        metis_tac[regional_entry_no_preds] >>
      `collect_phis (HD fn.fn_blocks).bb_instructions = []` by
        metis_tac[regional_entry_structure] >>
      drule entry_run_block >> disch_then (qspecl_then [`fuel`, `ctx`, `vs`] mp_tac) >>
      strip_tac >>
      `exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) = OK vs'` by metis_tac[] >>
      drule ready_entry_param_execution_layout >>
      disch_then (qspec_then `HD fn.fn_blocks` mp_tac) >> simp[] >> strip_tac >>
      drule_at (Pat `exec_block _ _ _ _ = _`) exec_block_param_prefix_success >>
      disch_then (qspecl_then [`LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`, `0`] mp_tac) >>
      simp[] >> strip_tac >>
      `regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn)
         spill_base (HD fn.fn_blocks)
         (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps2 /\
       (!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
         operand_val (frame_view fn ra u) lo at =
         operand_val (frame_view fn ra u) lo (normalize_operand (dfg_build_function fn) [] at))` by
        (irule lineage_entry_params_alias >> metis_tac[]) >>
      `lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks = SOME (HD fn.fn_blocks)` by metis_tac[] >>
      drule_all ready_body_suffix_layout >> simp[] >> strip_tac >>
      qpat_x_assum `(HD fn.fn_blocks).bb_label = _`
        (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
      gen_tac >> disch_tac >>
      drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
        regional_body_alias_suffix >>
      disch_then irule >> simp[] >>
      metis_tac[]) >>
  `get_params bb.bb_instructions = []` by metis_tac[] >>
  qpat_x_assum `bb.bb_label = _`
    (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
  `?edge. lineage_entry (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) edge bb.bb_label ps` by
    (drule lineage_state_entry_cases >> strip_tac >-
      (gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def, AllCaseEqs()] >>
       metis_tac[phiTransformTheory.lookup_block_at_hd, listTheory.NULL_EQ]) >> metis_tac[]) >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss() ++ boolSimps.LET_ss) [generate_block_plan_def] >>
  asm_rewrite_tac[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  simp_tac std_ss [AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `collect_phis bb.bb_instructions = []`
  >- (`regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn)
         spill_base bb 0 ps2 /\
       (!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
         operand_val (frame_view fn ra vs) lo at =
         operand_val (frame_view fn ra vs) lo (normalize_operand (dfg_build_function fn) [] at))` by
        (irule lineage_no_phi_preparation_alias >> metis_tac[]) >>
      drule_all ready_body_suffix_layout >> simp[] >> strip_tac >>
      `eval_phis vs bb.bb_instructions = OK vs` by
        metis_tac[phi_eval_collect, eval_phis_def] >>
      `phi_prefix_length bb.bb_instructions = 0` by
        metis_tac[listTheory.LENGTH, regional_collect_phis_length] >>
      fs[run_block_def] >>
      gen_tac >> disch_tac >>
      drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
        regional_body_alias_suffix >> disch_then irule >> simp[] >>
      reverse conj_tac >- metis_tac[] >>
      qexistsl_tac [`ctx`, `fuel`, `vs with vs_inst_idx := 0`] >>
      simp[frame_view_def] >> gen_tac >> disch_tac >>
      qpat_x_assum `!at. MEM at ps2.ps_stack \/ _ ==> _` (drule_then mp_tac) >>
      Cases_on `normalize_operand (dfg_build_function fn) [] at'` >>
      Cases_on `at'` >>
      simp[frame_view_def, operand_val_def]) >>
  drule_all regional_phi_preparation_identity >>
  disch_then (qspecl_then [`liveness_analyze fn`,
    `ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`] mp_tac) >>
  strip_tac >> gvs[] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    metis_tac[livenessProofsTheory.current_collect_phis_length] >>
  qspecl_then [`LENGTH (collect_phis bb.bb_instructions)`, `bb.bb_instructions`]
    (drule_then (fn th => drule (iffLR (SPEC_ALL th))))
    generate_block_insts_plan_split >> strip_tac >>
  qspecl_then [`vs`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (fs[run_block_def] >>
      `?pred. vs.vs_prev_bb = SOME pred` by
        (Cases_on `bb.bb_instructions` >- gvs[collect_phis_def] >>
         rename1 `bb.bb_instructions = inst::rest` >>
         `inst.inst_opcode = PHI` by
           (Cases_on `inst.inst_opcode = PHI` >> gvs[collect_phis_def]) >>
         qpat_x_assum `eval_phis _ _ = OK _` mp_tac >>
         simp[Once eval_phis_def] >>
         Cases_on `vs.vs_prev_bb` >-
           (Cases_on `inst.inst_outputs` >> simp[eval_one_phi_def]) >> simp[]) >>
      `regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn)
         spill_base bb (LENGTH (collect_phis bb.bb_instructions)) ps_mid /\
       (!at. MEM at ps_mid.ps_stack \/ at IN FDOM ps_mid.ps_spilled ==>
         operand_val (frame_view fn ra s') lo at =
         operand_val (frame_view fn ra s') lo (normalize_operand (dfg_build_function fn) [] at))` by
        (irule lineage_phi_eval_exit >> metis_tac[]) >>
      drule_all ready_body_suffix_layout >> simp[] >> strip_tac >>
      `s'.vs_labels = vs.vs_labels` by
        metis_tac[venomExecPropsTheory.eval_phis_preserves_labels] >>
      `phi_prefix_length bb.bb_instructions = LENGTH (collect_phis bb.bb_instructions)` by
        metis_tac[regional_collect_phis_length] >>
      qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ 0 _ _ = _` kall_tac >>
      gen_tac >> disch_tac >>
      drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
        regional_body_alias_suffix >> disch_then irule >> simp[] >>
      reverse conj_tac >- metis_tac[] >>
      qexistsl_tac [`ctx`, `fuel`, `s' with vs_inst_idx := LENGTH (collect_phis bb.bb_instructions)`] >>
      simp[] >> reverse conj_tac >- metis_tac[] >>
      simp[frame_view_def] >> gen_tac >> disch_tac >>
      qpat_x_assum `!at. MEM at ps_mid.ps_stack \/ _ ==> _` (drule_then mp_tac) >>
      Cases_on `normalize_operand (dfg_build_function fn) [] at'` >>
      Cases_on `at'` >> simp[frame_view_def, operand_val_def]) >>
  fs[run_block_def]

QED
