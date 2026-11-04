Theory makeSsaCurrentExitTokens
Ancestors
  makeSsaCurrentTokenOwnership makeSsaCurrentTreePaths makeSsaCurrentTokens
  makeSsaCurrentPathBridge makeSsaCurrentGraphCut makeSsaCurrentDemandDominance
  makeSsaCurrentAvailability
  makeSsaCurrentDominanceBridge venomWf cfgWf dominatorDefs venomExecProps venomInst list

Theorem current_output_token_nondefault:
  !xs start t. (!w. t <> CurrentDefault w) ==>
    !w. current_output_token v l i start xs t <> CurrentDefault w
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >> disch_tac >> gen_tac >>
  first_x_assum irule >> Cases_on `h = v` >> simp[]
QED

Theorem current_original_scan_nondefault:
  !insts start t. (!w. t <> CurrentDefault w) ==>
    !w. current_original_scan v l start insts t <> CurrentDefault w
Proof
  Induct >> simp[current_original_scan_def] >> rpt gen_tac >> disch_tac >> gen_tac >>
  first_x_assum irule >> irule current_output_token_nondefault >> simp[]
QED

Theorem current_block_token_nondefault:
  (!w. t <> CurrentDefault w) ==>
  !w. current_block_token fn ins v l t <> CurrentDefault w
Proof
  strip_tac >> simp[current_block_token_def] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  irule current_original_scan_nondefault >> Cases_on `ins v l` >> simp[]
QED

Theorem current_chain_token_nondefault:
  !path t. (!w. t <> CurrentDefault w) ==>
    !w. current_chain_token fn ins v path t <> CurrentDefault w
Proof
  Induct >> simp[current_chain_token_def] >> rpt gen_tac >> disch_tac >> gen_tac >>
  first_x_assum irule >> irule current_block_token_nondefault >> simp[]
QED

Theorem current_chain_token_definition_nondefault:
  !path t. (?l bb inst. MEM l path /\ lookup_block l fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) ==>
    !w. current_chain_token fn ins v path t <> CurrentDefault w
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  gvs[MEM, current_chain_token_def]
  >- (irule current_chain_token_nondefault >>
      metis_tac[current_block_token_definition_nondefault]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_dominating_definition_exit_token:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_tree_ancestor_path (current_dom_tree fn) p path /\
  MEM p (fn_labels fn) /\ MEM db fn.fn_blocks /\
  MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  fn_dominates fn db.bb_label p ==>
  (!w. current_block_token fn ins v p
    (current_inherited_token fn ins v path) <> CurrentDefault w) /\
  current_token_owns fn (current_block_token fn ins v p
    (current_inherited_token fn ins v path)) v
Proof
  strip_tac >>
  `lookup_block db.bb_label fn.fn_blocks = SOME db` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `MEM db.bb_label (fn_labels fn)` by (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label p` by
    metis_tac[current_semantic_dominates] >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label (REVERSE path) p` by
    metis_tac[current_actual_path_chain] >>
  `MEM db.bb_label (path ++ [p])` by
    (Cases_on `db.bb_label = p` >> simp[] >>
     `strict_dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label p` by
       simp[strict_dominates_def] >>
     drule_all current_actual_chain_membership >> simp[]) >>
  conj_tac
  >- (rewrite_tac[GSYM current_inherited_token_step, current_inherited_token_def] >>
      irule current_chain_token_definition_nondefault >> metis_tac[]) >>
  irule current_block_token_owns >> simp[current_inherited_token_owns]
QED

Theorem current_phi_operand_dominating_definition:
  wf_function fn /\ all_reachable fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ lookup_block p fn.fn_blocks = SOME pred /\
  MEM succ fn.fn_blocks /\ MEM phi succ.bb_instructions /\
  phi.inst_opcode = PHI /\ MEM (p,v) (phi_pairs phi.inst_operands) /\
  fn_cfg_edge fn p succ.bb_label ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\ fn_dominates fn db.bb_label p
Proof
  strip_tac >>
  `MEM pred fn.fn_blocks /\ pred.bb_label = p` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `fn_reachable fn p` by
    (gvs[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `def_on_all_paths fn pred NONE v` by
    (gvs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  `current_available fn v p (LENGTH pred.bb_instructions)` by
    metis_tac[current_available_from_exit] >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    (gvs[fn_phi_operands_single_def_def] >> metis_tac[]) >>
  drule_all current_available_definition >> strip_tac >>
  qexistsl_tac [`db`, `di`] >> simp[] >>
  metis_tac[current_available_unique_dominates]
QED

Theorem current_actual_phi_operand_exit_token:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  LENGTH fn.fn_blocks = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (fn.fn_blocks,bbs)) annsss /\
  (!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old) /\
  (!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l bbs)) /\
  current_tree_trace (current_annotation_map bbs annsss) sm (current_dom_tree fn)
    s rs bbs H CurrentDefault visited ctrs' s' bbs' H' visited' events /\
  MEM ev events /\ current_event_label ev = p /\
  lookup_block p fn.fn_blocks = SOME pred /\
  MEM succ fn.fn_blocks /\ MEM phi succ.bb_instructions /\
  phi.inst_opcode = PHI /\ MEM (p,v) (phi_pairs phi.inst_operands) /\
  fn_cfg_edge fn p succ.bb_label ==>
  (!w. current_event_exit_env ev v <> CurrentDefault w) /\
  current_token_owns fn (current_event_exit_env ev v) v
Proof
  strip_tac >>
  drule_all current_provenance_tree_static_env >> strip_tac >>
  drule_all current_phi_operand_dominating_definition >> strip_tac >>
  `MEM p (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  asm_rewrite_tac[] >> irule current_dominating_definition_exit_token >> metis_tac[]
QED
