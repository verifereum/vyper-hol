Theory makeSsaCurrentNonDegDefault
Ancestors
  makeSsaCurrentNonDegTokenSources makeSsaCurrentTraceCertificate
  makeSsaCurrentTreePaths
  makeSsaCurrentDemandedCut makeSsaCurrentAvailability makeSsaCurrentPathBridge
  makeSsaCurrentLiveTransport makeSsaCurrentLastSite makeSsaCurrentTokens
  makeSsaCurrentDemandDominance makeSsaCurrentAnalysis makeSsaCurrentTokenGraph
  o1PassContract unitShapeDefs venomWf venomInst venomExecProps
  cfgWf list rich_list alist

Theorem current_nondeg_output_token_default:
  !xs j t. current_output_token v l i j xs t = CurrentDefault v <=>
    t = CurrentDefault v /\ ~MEM v xs
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h = v` >> simp[] >> metis_tac[]
QED

Theorem current_nondeg_original_scan_default:
  !insts i t. current_original_scan v l i insts t = CurrentDefault v <=>
    t = CurrentDefault v /\ EVERY (\inst. ~MEM v inst.inst_outputs) insts
Proof
  Induct >> simp[current_original_scan_def, current_nondeg_output_token_default] >>
  metis_tac[]
QED

Theorem current_nondeg_block_token_default:
  current_block_token fn ins v l t = CurrentDefault v <=>
  t = CurrentDefault v /\
  (!bb. lookup_block l fn.fn_blocks = SOME bb ==>
    ~ins v l /\ EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions)
Proof
  Cases_on `lookup_block l fn.fn_blocks` >>
  simp[current_block_token_def, current_nondeg_original_scan_default] >>
  Cases_on `ins v l` >> simp[]
QED

Theorem current_nondeg_chain_token_default:
  !ls t. current_chain_token fn ins v ls t = CurrentDefault v <=>
    t = CurrentDefault v /\
    EVERY (\l. current_block_token fn ins v l (CurrentDefault v) = CurrentDefault v) ls
Proof
  Induct >> simp[current_chain_token_def, current_nondeg_block_token_default] >>
  metis_tac[]
QED

Theorem current_nondeg_live_default_edge:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  ~blocks_have_leading_phi fn.fn_blocks /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
  ~current_actual_inserted fn v b /\ current_phi_cut_clear fn v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs) =
    CurrentDefault v ==>
  ~current_actual_inserted fn v a /\ current_phi_cut_clear fn v a /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs) /\
  ?ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps) =
      CurrentDefault v
Proof
  strip_tac >>
  `?ab bb. lookup_block a fn.fn_blocks = SOME ab /\
           lookup_block b fn.fn_blocks = SOME bb` by
    (gvs[fn_cfg_edge_def, wf_function_def, fn_succs_closed_def,
         fn_labels_def, MEM_MAP] >> metis_tac[MEM_lookup_block]) >>
  `MEM a (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_actual_token_chain >> strip_tac >>
  `current_block_token fn (current_actual_inserted fn) v a
     (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) =
     CurrentDefault v` by
    (irule EQ_TRANS >> qexists `current_inherited_token fn
       (current_actual_inserted fn) v (REVERSE qs)` >> conj_tac
     >- (irule current_actual_demanded_cut_tokens >> simp[] >>
         qexists_tac `b` >> gvs[]) >> simp[]) >>
  `~current_actual_inserted fn v a /\
   EVERY (\inst. ~MEM v inst.inst_outputs) ab.bb_instructions /\
   current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps) =
      CurrentDefault v` by
    (gvs[current_nondeg_block_token_default] >> metis_tac[]) >>
  `!k. k < LENGTH ab.bb_instructions ==>
    ~MEM v (inst_defs (EL k ab.bb_instructions))` by
    (fs[EVERY_MEM, inst_defs_def] >> metis_tac[EL_MEM]) >>
  `current_phi_cut_clear fn v a` by
    (simp[current_phi_cut_clear_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[current_collect_phis_length, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs` by
    (irule current_selected_live_edge >> simp[] >>
     qexistsl_tac [`b`, `bb`] >> simp[] >>
     `collect_phis bb.bb_instructions = []` by
       metis_tac[current_no_leading_phi_cut] >> gvs[]) >>
  simp[] >> metis_tac[]
QED

Theorem current_nondeg_live_default_route:
  !ls a b. wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  ~blocks_have_leading_phi fn.fn_blocks /\
  entry_block fn = SOME eb /\ LRC (fn_cfg_edge fn) ls a b /\
  ~current_actual_inserted fn v b /\ current_phi_cut_clear fn v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
  (?qs. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs) =
      CurrentDefault v) ==>
  ~current_actual_inserted fn v a /\ current_phi_cut_clear fn v a /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs) /\
  ?ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps) =
      CurrentDefault v
Proof
  Induct
  >- (pure_rewrite_tac[LRC_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  pure_rewrite_tac[LRC_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`z`, `b`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  irule current_nondeg_live_default_edge >> simp[] >>
  qexistsl_tac [`z`, `ps`] >> gvs[]
QED

Theorem current_nondeg_entry_unavailable:
  fn_entry_label fn = SOME l ==> ~current_available fn v l 0
Proof
  strip_tac >> simp[current_available_def] >> rpt strip_tac >>
  qexists_tac `[l]` >> simp[is_fn_path_def]
QED

Theorem current_nondeg_selected_live_nondefault:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ ~blocks_have_leading_phi fn.fn_blocks /\
  entry_block fn = SOME eb /\ lookup_block l fn.fn_blocks = SOME bb /\
  current_tree_ancestor_path (current_dom_tree fn) l path /\
  ~current_actual_inserted fn v l /\ current_phi_cut_clear fn v l /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) l = SOME vs /\ MEM v vs) ==>
  current_inherited_token fn (current_actual_inserted fn) v path <> CurrentDefault v
Proof
  strip_tac >> spose_not_then assume_tac >>
  `MEM l (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_actual_path_chain >> strip_tac >>
  drule_all current_reachable_cfg_route >> strip_tac >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) eb.bb_label = SOME vs /\ MEM v vs` by
    (mp_tac current_nondeg_live_default_route >>
     disch_then (qspecl_then [`ls`, `eb.bb_label`, `l`] mp_tac) >>
     (impl_tac >- (simp[] >> qexists_tac `REVERSE path` >> simp[])) >>
     metis_tac[]) >>
  `lookup_block eb.bb_label fn.fn_blocks = SOME eb` by
    (irule MEM_lookup_block >>
     gvs[entry_block_def, wf_function_def, fn_labels_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  `collect_phis eb.bb_instructions = []` by
    metis_tac[current_no_leading_phi_cut] >>
  `MEM v (live_vars_at (liveness_analyze fn) eb.bb_label 0)` by
    metis_tac[current_selected_live_iff, LENGTH] >>
  `current_available fn v eb.bb_label 0` by
    (irule current_live_post_phi_available >> simp[] >> metis_tac[]) >>
  `fn_entry_label fn = SOME eb.bb_label` by simp[fn_entry_label_def] >>
  metis_tac[current_nondeg_entry_unavailable]
QED

Theorem current_nondeg_live_pred_exit_nondefault:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ ~blocks_have_leading_phi fn.fn_blocks /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\
  current_tree_ancestor_path (current_dom_tree fn) p path /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs) ==>
  current_block_token fn (current_actual_inserted fn) v p
    (current_inherited_token fn (current_actual_inserted fn) v path) <>
      CurrentDefault w
Proof
  strip_tac >> spose_not_then assume_tac >>
  `current_inherited_token fn (current_actual_inserted fn) v path = CurrentDefault w` by
    metis_tac[current_nondeg_block_token_local, current_nondeg_token_at_def] >>
  `w = v` by
    (fs[current_inherited_token_def] >>
     metis_tac[current_nondeg_chain_token_local, current_nondeg_token_at_def,
               current_token_11]) >>
  gvs[current_nondeg_block_token_default] >>
  `!k. k < LENGTH pb.bb_instructions ==>
    ~MEM v (inst_defs (EL k pb.bb_instructions))` by
    (fs[EVERY_MEM, inst_defs_def] >> metis_tac[EL_MEM]) >>
  `current_phi_cut_clear fn v p` by
    (simp[current_phi_cut_clear_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[current_collect_phis_length, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `collect_phis hb.bb_instructions = []` by
    metis_tac[current_no_leading_phi_cut] >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) p = SOME vs /\ MEM v vs` by
    (irule current_selected_live_edge >> simp[] >>
     qexistsl_tac [`h`, `hb`] >> gvs[]) >>
  `current_inherited_token fn (current_actual_inserted fn) v path <> CurrentDefault v` by
    (irule current_nondeg_selected_live_nondefault >> simp[] >>
     qexistsl_tac [`pb`, `p`] >> gvs[] >> metis_tac[]) >>
  gvs[]
QED

Theorem current_nondeg_tree_label_path:
  !tree l. MEM l (dom_tree_labels tree) ==>
    ?path. current_tree_ancestor_path tree l path
Proof
  Induct >> simp[makeSsaDefsTheory.dom_tree_labels_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> metis_tac[current_tree_ancestor_path_rules]
QED

Theorem current_nondeg_actual_chain_path:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM p (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p ==>
  current_tree_ancestor_path (current_dom_tree fn) p (REVERSE ps)
Proof
  strip_tac >>
  `MEM p (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_label_member] >>
  drule current_nondeg_tree_label_path >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn)
    eb.bb_label (REVERSE path) p` by metis_tac[current_actual_path_chain] >>
  `REVERSE path = ps` by
    metis_tac[current_token_chain_unique, current_token_root_idom] >>
  metis_tac[REVERSE_REVERSE]
QED

Theorem current_nondeg_live_pred_chain_nondefault:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ ~blocks_have_leading_phi fn.fn_blocks /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs) ==>
  current_inherited_token fn (current_actual_inserted fn) v (REVERSE (p::ps)) <>
    CurrentDefault w
Proof
  strip_tac >>
  `MEM p (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_nondeg_actual_chain_path >> strip_tac >>
  rewrite_tac[current_parent_inherited_token] >>
  irule current_nondeg_live_pred_exit_nondefault >> simp[] >>
  qexistsl_tac [`h`, `hb`] >> gvs[] >> metis_tac[]
QED
