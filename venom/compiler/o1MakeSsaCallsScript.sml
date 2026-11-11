Theory o1MakeSsaCalls
Ancestors
  o1MakeSsaCallAssembly o1MakeSsaCallCleanup o1MakeSsaRevertStages
  o1MakeSsaActualNames o1MakeSsaPreparation o1MakeSsaCallBlockBridge
  o1MakeSsaCallPaths o1MakeSsaTraversalFrames fmpStepList
  unitShapeDefs o1PassContract o1ContractSueStep o1MakeSsaEventFrames
  o1MakeSsaEventOwnership o1MakeSsaCallOwnership venomExecProps
  makeSsaCurrentDefs makeSsaCurrentProps o1MakeSsaFormats o1MakeSsaFrontier
  o1MakeSsaActualMaps o1MakeSsaOwnership makeSsaCurrentAnalysis
  venomWf venomInst venomFnScheduleRunner irSupply list pred_set simplifyCfgCallChecks

(* latest_current_name of the initial rename state is the identity *)
val _ = augment_srw_ss [rewrites [makeSsaCurrentTreeTraceTheory.current_initial_latest]];

Theorem prepared_prefix_calls_flagged[local]:
  prepared_prefix old new ==>
  (calls_flagged env new.bb_instructions = calls_flagged env old.bb_instructions)
Proof
  simp[prepared_prefix_def] >> rpt strip_tac >> gvs[] >>
  irule calls_flagged_prefix_no_calls >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem prepared_blocks_calls_flagged[local]:
  LIST_REL prepared_prefix old new /\
  EVERY (\bb. calls_flagged env bb.bb_instructions) old ==>
  EVERY (\bb. calls_flagged env bb.bb_instructions) new
Proof
  qid_spec_tac `new` >> Induct_on `old` >> Cases_on `new` >> simp[] >> rpt strip_tac
  >- metis_tac[prepared_prefix_calls_flagged] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem indexed_patch_frame_phi_prefix[local]:
  indexed_patch_frame bb out ==>
  (list_prefix (\i. i.inst_opcode = PHI) out.bb_instructions =
   list_prefix (\i. i.inst_opcode = PHI) bb.bb_instructions)
Proof
  simp[indexed_patch_frame_def, list_prefix_indexed] >> rpt strip_tac >>
  eq_tac >> rpt strip_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >> fs[] >> metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem visit_event_calls_flagged[local]:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\ MEM e events /\
  lookup_block e.sve_label bbs = SOME bb /\ bb_well_formed bb /\
  calls_flagged env bb.bb_instructions /\
  current_rename_owner V H e.sve_supply_in e.sve_in /\
  EVERY (\i. set i.inst_outputs SUBSET V) e.sve_before /\
  LENGTH env = LENGTH env' /\
  (!n l. revert_path env n l ==> revert_path env' n l) ==>
  calls_flagged env' e.sve_after
Proof
  strip_tac >> drule_all (cj 1 visit_event_input_frame) >> strip_tac >>
  `list_prefix (\i. i.inst_opcode = PHI) e.sve_before` by
    (drule indexed_patch_frame_phi_prefix >>
     simp[] >> metis_tac[mssa_well_formed_phi_list_prefix]) >>
  `calls_flagged env e.sve_before` by
    (drule indexed_patch_frame_calls_flagged >> simp[] >> metis_tac[]) >>
  `rename_current_block_insts e.sve_supply_in e.sve_in e.sve_before =
    (e.sve_out,e.sve_supply_out,e.sve_after)` by
    (qspecl_then [`tree`,`path`,`s`,`rs`,`bbs`,`sm`] mp_tac
       (cj 1 visit_local_rename) >> fs[EVERY_MEM]) >>
  qspecl_then [`\i. i.inst_opcode = PHI`,`e.sve_before`] mp_tac every_prefix_split >>
  fs[list_prefix_indexed] >> disch_then (fn th =>
    `?pre rest. e.sve_before = pre ++ rest /\
      EVERY (\i. i.inst_opcode = PHI) pre /\
      EVERY (\i. i.inst_opcode <> PHI) rest` by metis_tac[th]) >>
  irule current_calls_flagged_phi_prefix >>
  goal_assum (drule_at Any) >> simp[] >> fs[EVERY_APPEND] >> metis_tac[]
QED

Theorem visit_blocks_calls_flagged[local]:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!q. MEM q (dom_tree_postorder tree) ==> IS_SOME (lookup_block q bbs)) /\
  set (MAP (\bb. bb.bb_label) final) SUBSET set (dom_tree_postorder tree) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) final) /\
  EVERY bb_well_formed bbs /\
  EVERY (\bb. calls_flagged env bb.bb_instructions) bbs /\
  EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET V) bb.bb_instructions) bbs /\
  current_rename_owner V H s rs /\
  LENGTH env = LENGTH env' /\
  (!n l. revert_path env n l ==> revert_path env' n l) ==>
  EVERY (\bb. calls_flagged env' bb.bb_instructions) final
Proof
  strip_tac >>
  `!e. MEM e events ==> IS_SOME (lookup_block e.sve_label bbs)` by
    (drule (cj 1 o1MakeSsaVisitRetentionTheory.retention_event_labels) >>
     strip_tac >> metis_tac[]) >>
  drule_all visit_events_output_domain >> strip_tac >>
  drule_all (cj 1 visit_current_rename_owner) >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all visit_final_block_event_frame >> strip_tac >>
  `?src. lookup_block e.sve_label bbs = SOME src` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `MEM src bbs` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed src /\ calls_flagged env src.bb_instructions /\
   EVERY (\i. set i.inst_outputs SUBSET V) e.sve_before` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `?He. current_rename_owner V He e.sve_supply_in e.sve_in` by metis_tac[] >>
  drule_all visit_event_calls_flagged >> strip_tac >>
  drule indexed_patch_frame_calls_flagged >> simp[] >> metis_tac[]
QED

Theorem make_ssa_current_fn_call_checks_ok:
  make_ssa_current_fn s fn = (fn',s') /\ wf_function fn /\
  make_ssa_input_ok fn /\ ir_supply_covers_fn s fn /\
  ir_supply_inst_ok s /\ call_checks_ok fn ==> call_checks_ok fn'
Proof
  strip_tac >>
  drule_all make_ssa_current_fn_revert_environment >> strip_tac >>
  Cases_on `fn_entry_label fn`
  >- (fs[make_ssa_current_fn_def] >> gvs[]) >>
  qpat_x_assum `make_ssa_current_fn _ _ = _` mp_tac >>
  simp[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  `current_dom_tree fn = current_dom_tree_aux (dom_analyze (cfg_analyze fn) fn)
     (LENGTH (fn_labels fn)) x` by simp[current_dom_tree_def] >>
  gs[GSYM current_frontier_map_def, GSYM current_pred_map_def,
     GSYM current_succ_map_def] >>
  qmatch_asmsub_abbrev_tac `add_phi_nodes_supply s df pm li fn.fn_blocks defs` >>
  `EVERY bb_well_formed bbs1` by
    (drule (SRULE[current_frontier_map_def, current_pred_map_def, LET_THM]
       add_phi_nodes_supply_well_formed) >> disch_then irule >>
     gvs[Abbr `df`, Abbr `pm`, wf_function_def, EVERY_MEM, fn_labels_def, MEM_MAP] >>
     metis_tac[]) >>
  qpat_x_assum `current_dom_tree fn = _`
    (fn th => rule_assum_tac (REWRITE_RULE[GSYM th])) >>
  `EVERY (\bb. calls_flagged fn.fn_blocks bb.bb_instructions) bbs1` by
    (drule prepared_add_phi_nodes >> strip_tac >>
     irule prepared_blocks_calls_flagged >> goal_assum (drule_at Any) >>
     fs[call_checks_ok_def]) >>
  `EVERY bb_well_formed bbs2` by
    metis_tac[cj 1 rename_current_blocks_well_formed] >>
  `EVERY (\bb. list_prefix (\i. i.inst_opcode = PHI) bb.bb_instructions) bbs2` by
    (fs[EVERY_MEM] >> metis_tac[mssa_well_formed_phi_list_prefix]) >>
  simp[call_checks_ok_def] >>
  drule simplify_current_phis_if_calls_flagged >>
  disch_then (qspecl_then
    [`simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) bbs2`,
     `blocks_have_leading_phi fn.fn_blocks`] (fn th => rewrite_tac[th])) >>
  `EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET set (fn_ir_vars fn))
    bb.bb_instructions) bbs1` by
    (irule prepared_original_output_domain >> fs[Abbr `defs`] >> metis_tac[]) >>
  `ssa_vars_covered s1 (fn_ir_vars fn)` by
    (drule add_phi_nodes_supply_extends >> strip_tac >>
     irule ssa_vars_covered_mono >> goal_assum (drule_at Any) >>
     fs[ssa_vars_covered_def, ir_supply_covers_fn_def,
        list_subset_def, EVERY_MEM]) >>
  `current_rename_owner (set (fn_ir_vars fn)) {(v,v) | MEM v (fn_ir_vars fn)} s1
    (init_current_rename_state defs)` by
    (fs[Abbr `defs`] >> irule current_rename_owner_init_function >> simp[]) >>
  drule add_phi_nodes_supply_labels >> strip_tac >>
  drule (cj 1 rename_current_blocks_labels) >> strip_tac >>
  `?eb. entry_block fn = SOME eb` by fs[fn_entry_label_def, AllCaseEqs()] >>
  `PERM (dom_tree_postorder (current_dom_tree fn)) (fn_labels fn)` by
    (rewrite_tac[GSYM current_dom_postorder_def] >>
     irule current_dom_postorder_perm >> fs[make_ssa_input_ok_def] >> metis_tac[]) >>
  `ALL_DISTINCT (dom_tree_postorder (current_dom_tree fn))` by
    metis_tac[o1MakeSsaRootedTreeTheory.actual_rooted_tree_distinct] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs2)` by
    fs[wf_function_def, fn_labels_def] >>
  `set (MAP (\bb. bb.bb_label) bbs2) SUBSET set (dom_tree_postorder (current_dom_tree fn))` by
    (fs[SUBSET_DEF, fn_labels_def] >> metis_tac[sortingTheory.PERM_MEM_EQ]) >>
  `!q. MEM q (dom_tree_postorder (current_dom_tree fn)) ==>
      IS_SOME (lookup_block q bbs1)` by
    (rpt strip_tac >>
     `MEM q (MAP (\bb. bb.bb_label) bbs1)` by
       metis_tac[sortingTheory.PERM_MEM_EQ, fn_labels_def] >>
     `?b. MEM b bbs1 /\ b.bb_label = q` by (fs[MEM_MAP] >> metis_tac[]) >>
     `lookup_block q bbs1 = SOME b` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >> simp[]) >>
  qmatch_asmsub_rename_tac `rename_current_blocks s1 _ _ _ _ = (ct,s',bbs2)` >>
  `visit_blocks [] s1 (init_current_rename_state defs) bbs1 (current_succ_map fn)
      (current_dom_tree fn) = ((ct,s',bbs2),
       SND (visit_blocks [] s1 (init_current_rename_state defs) bbs1
         (current_succ_map fn) (current_dom_tree fn)))` by
    metis_tac[o1MakeSsaVisitTraceTheory.visit_erasure, pairTheory.PAIR] >>
  drule_all visit_blocks_calls_flagged >> simp[]
QED
