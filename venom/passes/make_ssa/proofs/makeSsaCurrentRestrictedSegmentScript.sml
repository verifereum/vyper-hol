Theory makeSsaCurrentRestrictedSegment
Ancestors
  makeSsaCurrentDemandedCut makeSsaCurrentLiveTransport makeSsaCurrentLastSite
  makeSsaCurrentTokens makeSsaCurrentCutTokens makeSsaCurrentPlacement makeSsaCurrentDefs
  makeSsaCurrentAllocation makeSsaCurrentSourceCuts makeSsaCurrentReinsertionSlots
  makeSsaCurrentCertificate makeSsaCurrentTraceCertificate makeSsaCurrentTreePaths
  makeSsaCurrentPathBridge makeSsaCurrentTokenGraph venomExecProps
  venomInst venomWf cfgWf list rich_list alist

(* This records the actual CFG path and static absence of definitions/merges,
   not derived liveness, name equality, or runtime availability. *)
Definition current_restricted_path_def:
  current_restricted_path fn v labels <=>
    labels <> [] /\
    (!k. SUC k < LENGTH labels ==>
      fn_cfg_edge fn (EL k labels) (EL (SUC k) labels)) /\
    EVERY (\l. (?bb. lookup_block l fn.fn_blocks = SOME bb) /\
      ~current_changing_site fn (current_actual_inserted fn) v l) labels
End

Theorem current_restricted_path_tail:
  current_restricted_path fn v (a::b::rest) ==>
  current_restricted_path fn v (b::rest) /\ fn_cfg_edge fn a b /\
  ~current_changing_site fn (current_actual_inserted fn) v a
Proof
  simp[current_restricted_path_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem current_restricted_segment_live:
  !labels. wf_function fn /\ all_reachable fn /\
  current_restricted_path fn v labels /\
  (!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) (LAST labels) = SOME vs /\ MEM v vs) ==>
  !l. MEM l labels ==>
  ?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) l = SOME vs /\ MEM v vs
Proof
  Induct >- simp[current_restricted_path_def] >>
  Cases_on `labels` >- simp[] >> rpt strip_tac >>
  rename1 `current_restricted_path fn v (a::b::rest)` >>
  drule current_restricted_path_tail >> strip_tac >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs` by
    (first_x_assum irule >> gvs[LAST_CONS] >> metis_tac[]) >>
  gvs[MEM] >- (
    irule current_selected_live_route_step >> simp[] >>
    qexists_tac `b` >> simp[] >>
    irule current_non_site_live_edge >> simp[] >>
    conj_tac >- metis_tac[] >> conj_tac
    >- (qexists_tac `current_actual_inserted fn` >> simp[]) >>
    irule current_non_site_cut_clear >>
    qexists_tac `current_actual_inserted fn` >>
    gvs[current_restricted_path_def]) >>
  first_x_assum irule >> gvs[LAST_CONS] >> metis_tac[]
QED

Theorem current_restricted_adjacent_tokens:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  ~current_changing_site fn (current_actual_inserted fn) v a /\
  ~current_changing_site fn (current_actual_inserted fn) v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) ==>
  current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps) =
  current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs)
Proof
  strip_tac >>
  `current_phi_cut_clear fn v b` by metis_tac[current_non_site_cut_clear] >>
  `~current_actual_inserted fn v b` by gvs[current_changing_site_def] >>
  mp_tac current_actual_demanded_cut_tokens >>
  simp[current_non_site_block_token] >> disch_then irule >>
  simp[] >> metis_tac[]
QED

Theorem current_restricted_segment_tokens:
  !labels. wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_restricted_path fn v labels /\
  (!l. MEM l labels ==>
    current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label (paths l) l) /\
  (!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) (LAST labels) = SOME vs /\ MEM v vs) ==>
  !a b. MEM a labels /\ MEM b labels ==>
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths a)) =
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths b))
Proof
  Induct >- simp[current_restricted_path_def] >>
  Cases_on `labels` >- simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `current_restricted_path fn v (a::b::rest)` >>
  drule current_restricted_path_tail >> strip_tac >>
  `!x y. MEM x (b::rest) /\ MEM y (b::rest) ==>
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths x)) =
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths y))` by
    (rpt gen_tac >> strip_tac >> first_x_assum irule >>
     gvs[LAST_CONS] >> metis_tac[]) >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs` by
    (irule current_restricted_segment_live >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexists_tac `a::b::rest` >> simp[] >> metis_tac[]) >>
  `current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths a)) =
   current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths b))` by
    (irule current_restricted_adjacent_tokens >> simp[] >>
     qexistsl_tac [`a`, `b`] >> gvs[current_restricted_path_def] >> metis_tac[]) >>
  qpat_x_assum `_ ==> !a b. _` kall_tac >>
  gvs[MEM] >> metis_tac[]
QED

(* H is the allocation map of the actual supplied certificate.  The token
   theorem is stronger: it does not depend on any allocation map at all. *)
Theorem current_restricted_segment_names:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_structural_certificate s fn fn' s' A H events /\
  current_restricted_path fn v labels /\
  (!l. MEM l labels ==>
    current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label (paths l) l) /\
  (!pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) (LAST labels) = SOME vs /\ MEM v vs) ==>
  !a b. MEM a labels /\ MEM b labels ==>
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths a)) =
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths b)) /\
    current_token_name H
      (current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths a))) =
    current_token_name H
      (current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths b)))
Proof
  rpt strip_tac >>
  `current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths a)) =
   current_inherited_token fn (current_actual_inserted fn) v (REVERSE (paths b))` by
    (irule current_restricted_segment_tokens >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexists_tac `labels` >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem current_restricted_adjacent_names:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  ~current_changing_site fn (current_actual_inserted fn) v a /\
  ~current_changing_site fn (current_actual_inserted fn) v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) ==>
  current_token_name H
    (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) =
  current_token_name H
    (current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs))
Proof
  strip_tac >> AP_TERM_TAC >>
  irule current_restricted_adjacent_tokens >> simp[] >> metis_tac[]
QED

Theorem current_certificate_entry_static_env:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\ MEM ev events ==>
  ?path. current_tree_ancestor_path (current_dom_tree fn) (current_event_label ev) path /\
    (!v. current_event_entry_env ev v =
      current_inherited_token fn (current_actual_inserted fn) v path)
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >> gvs[] >>
  drule current_add_phi_nodes_unique_prefix >> strip_tac >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LIST_REL_LENGTH] >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[current_unique_prefix_labels] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old` by
    (rpt strip_tac >> irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  drule_all current_provenance_tree_static_env >> metis_tac[]
QED

Theorem current_certificate_entry_chain_env:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\ MEM ev events /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps
    (current_event_label ev) ==>
  current_event_entry_env ev v =
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)
Proof
  strip_tac >> drule_all current_certificate_entry_static_env >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label
    (REVERSE path) (current_event_label ev)` by
    metis_tac[current_actual_path_chain] >>
  `ps = REVERSE path` by
    (irule current_token_chain_unique >> metis_tac[current_token_root_idom]) >>
  simp[]
QED

Theorem current_restricted_adjacent_entries:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ MEM ea events /\ MEM eb' events /\
  fn_cfg_edge fn (current_event_label ea) (current_event_label eb') /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps
    (current_event_label ea) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs
    (current_event_label eb') /\
  ~current_changing_site fn (current_actual_inserted fn) v (current_event_label ea) /\
  ~current_changing_site fn (current_actual_inserted fn) v (current_event_label eb') /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) (current_event_label eb') = SOME vs /\ MEM v vs) ==>
  current_event_entry_env ea v = current_event_entry_env eb' v /\
  current_token_name H (current_event_entry_env ea v) =
    current_token_name H (current_event_entry_env eb' v)
Proof
  strip_tac >>
  `current_event_entry_env ea v =
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)` by
    (irule current_certificate_entry_chain_env >> metis_tac[]) >>
  `current_event_entry_env eb' v =
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs)` by
    (irule current_certificate_entry_chain_env >> metis_tac[]) >>
  `current_event_entry_env ea v = current_event_entry_env eb' v` by
    (simp[] >> irule current_restricted_adjacent_tokens >> simp[] >> metis_tac[]) >>
  simp[]
QED
