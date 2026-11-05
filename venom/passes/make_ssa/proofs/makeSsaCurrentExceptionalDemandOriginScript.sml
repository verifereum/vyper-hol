Theory makeSsaCurrentExceptionalDemandOrigin
Ancestors makeSsaCurrentDemandOrigin makeSsaCurrentDemandDominance
  makeSsaCurrentSingletonSelectors makeSsaCurrentDemandedCut
  makeSsaCurrentReinsertionSlots makeSsaCurrentPathBridge makeSsaCurrentGraphCut
  makeSsaCurrentDominanceBridge makeSsaCurrentTokens makeSsaCurrentDemand makeSsaCurrentAvailability
  venomWf venomInst venomExecProps cfgWf dominatorDefs list rich_list

Theorem current_certificate_rooted_exceptional_demand_exit:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) route eb.bb_label p /\
  MEM ep events /\ current_event_label ep = p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  current_demand fn v p (LENGTH pb.bb_instructions) /\
  (?ob phi. MEM ob fn.fn_blocks /\ MEM phi (collect_phis ob.bb_instructions) /\
            MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  current_event_exit_env ep v =
    current_chain_token fn (current_actual_inserted fn) v (route ++ [p]) (CurrentDefault v)
Proof
  strip_tac >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    metis_tac[current_phi_operand_single_bound] >>
  `blocks_have_leading_phi fn.fn_blocks` by
    metis_tac[current_phi_operand_has_leading_phi] >>
  drule_all current_demand_route_definition >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = l` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `?b. b < LENGTH fn.fn_blocks /\ EL b fn.fn_blocks = bb` by metis_tac[MEM_EL] >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = i` by
    metis_tac[MEM_EL] >>
  `current_defining_sites fn v = [(b,j)]` by
    (irule current_single_definition_indexed_site >>
     simp[current_defining_sites_member] >> metis_tac[]) >>
  `current_chain_token fn (current_actual_inserted fn) v (route ++ [p]) (CurrentDefault v) =
   current_canonical_instruction_token fn v (b,j)` by
    (irule current_single_definition_chain_token >> metis_tac[]) >>
  `current_available fn v p (LENGTH pb.bb_instructions)` by
    metis_tac[current_demand_available] >>
  `fn_reachable fn p` by
    (gvs[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `fn_dominates fn bb.bb_label p` by
    metis_tac[current_available_unique_dominates] >>
  `MEM p (fn_labels fn) /\ MEM bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `dominates (dom_analyze (cfg_analyze fn) fn) bb.bb_label p` by
    metis_tac[current_semantic_dominates] >>
  drule_all current_certificate_static_env >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label (REVERSE path) p` by
    metis_tac[current_actual_path_chain] >>
  `MEM bb.bb_label (path ++ [p])` by
    (Cases_on `bb.bb_label = p` >> simp[] >>
     `strict_dominates (dom_analyze (cfg_analyze fn) fn) bb.bb_label p` by
       simp[strict_dominates_def] >>
     drule_all current_actual_chain_membership >> simp[] >> metis_tac[]) >>
  `current_block_token fn (current_actual_inserted fn) v p
      (current_inherited_token fn (current_actual_inserted fn) v path) =
    current_canonical_instruction_token fn v (b,j)` by
    (rewrite_tac[GSYM current_inherited_token_step, current_inherited_token_def] >>
     irule current_single_definition_chain_token >> metis_tac[]) >>
  metis_tac[]
QED
