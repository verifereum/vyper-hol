Theory makeSsaCurrentCutTokens
Ancestors
  makeSsaCurrentLastSite makeSsaCurrentTokens makeSsaCurrentGraphCut
  makeSsaCurrentAnalysis makeSsaCurrentDefs makeSsaCurrentSelectedLive
  venomInst venomWf venomExecProps list rich_list alist dominatorDefs
  cfgAnalysisProps dominatorProofs cfgCorrectnessProof

Theorem current_output_token_constant:
  !xs j t u. MEM v xs ==>
    current_output_token v l i j xs t = current_output_token v l i j xs u
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `h = v`
  >- (qpat_x_assum `!j t u. _` kall_tac >> simp[current_output_token_def]) >>
  `MEM v xs` by metis_tac[MEM] >>
  rewrite_tac[current_output_token_def] >> first_x_assum irule >> simp[]
QED

Theorem current_original_scan_constant:
  !insts i t u. (?inst. MEM inst insts /\ MEM v inst.inst_outputs) ==>
    current_original_scan v l i insts t = current_original_scan v l i insts u
Proof
  Induct >> simp[current_original_scan_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[current_output_token_constant]
QED

Theorem current_non_site_block_token:
  ~current_changing_site fn ins v l ==>
  current_block_token fn ins v l t = t
Proof
  simp[current_block_token_def] >> strip_tac >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block l fn.fn_blocks = SOME bb` >>
  `~ins v l /\ EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions` by
    (gvs[current_changing_site_def, EVERY_MEM] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  simp[current_original_scan_absent]
QED

Theorem current_non_site_chain_token:
  !ls t. EVERY (\l. ~current_changing_site fn ins v l) ls ==>
    current_chain_token fn ins v ls t = t
Proof
  Induct >> simp[current_chain_token_def] >> rpt strip_tac >>
  simp[current_non_site_block_token]
QED

Theorem current_site_block_constant:
  wf_function fn /\ MEM l (fn_labels fn) /\ current_changing_site fn ins v l ==>
  current_block_token fn ins v l t = current_block_token fn ins v l u
Proof
  strip_tac >>
  `?bb. lookup_block l fn.fn_blocks = SOME bb` by
    (gvs[fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  simp[current_block_token_def] >> Cases_on `ins v l` >> simp[] >>
  irule current_original_scan_constant >>
  gvs[current_changing_site_def] >>
  `lookup_block bb'.bb_label fn.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem current_common_last_site_tokens:
  wf_function fn /\ MEM d (fn_labels fn) /\ current_changing_site fn ins v d /\
  xs = pre ++ d::post /\ ys = pre' ++ d::post' /\
  EVERY (\e. ~current_changing_site fn ins v e) post /\
  EVERY (\e. ~current_changing_site fn ins v e) post' ==>
  current_chain_token fn ins v xs t = current_chain_token fn ins v ys u
Proof
  strip_tac >> gvs[current_chain_token_append, current_chain_token_def,
    current_non_site_chain_token] >>
  irule current_site_block_constant >> simp[]
QED

Theorem current_cut_ordinary_token_equality:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  ~ins v b /\ current_phi_cut_clear fn v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
  (!pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  (!x y. current_changing_site fn ins v x /\
    MEM y (frontier_of (dom_analyze (cfg_analyze fn) fn) x) /\
    (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) y = SOME vs /\ MEM v vs) ==> ins v y) ==>
  current_block_token fn ins v a (current_inherited_token fn ins v (REVERSE ps)) =
  current_inherited_token fn ins v (REVERSE qs)
Proof
  strip_tac >>
  mp_tac current_cut_common_last_site >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac
  >- (pure_rewrite_tac[GSYM current_inherited_token_step] >>
      simp[current_inherited_token_def, current_non_site_chain_token]) >>
  pure_rewrite_tac[GSYM current_inherited_token_step, current_inherited_token_def] >>
  irule current_common_last_site_tokens >> simp[] >>
  `MEM b (fn_labels fn)` by
    metis_tac[current_cfg_edge_succs, cfg_analyze_succ_labels] >>
  `MEM d qs` by metis_tac[MEM_REVERSE, MEM_APPEND, MEM] >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) d b` by
    metis_tac[current_actual_chain_membership] >>
  metis_tac[dom_labels_bounded, strict_dominates_def, dominates_def]
QED
