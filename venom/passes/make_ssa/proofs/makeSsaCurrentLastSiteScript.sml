Theory makeSsaCurrentLastSite
Ancestors
  livenessTransferProofs
  makeSsaCurrentGraphCut makeSsaCurrentLiveTransport makeSsaCurrentFrontier
  makeSsaCurrentTokens dominatorAnalysisProps
  makeSsaCurrentAnalysis makeSsaCurrentSelectedLive makeSsaCurrentDefs
  venomInst venomWf venomExecProps cfgAnalysisProps dominatorDefs
  list rich_list alist arithmetic makeSsaCurrentDemandDominance dominatorProofs cfgDefs relation

Definition current_changing_site_def:
  current_changing_site fn ins v l <=> ins v l \/
    ?bb inst. MEM bb fn.fn_blocks /\ bb.bb_label = l /\
      MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs
End

Definition current_phi_cut_clear_def:
  current_phi_cut_clear fn v l <=>
    !bb k. lookup_block l fn.fn_blocks = SOME bb /\
      k < LENGTH (collect_phis bb.bb_instructions) ==>
      ~MEM v (inst_defs (EL k bb.bb_instructions))
End

Theorem current_non_site_outputs:
  ~current_changing_site fn ins v l /\
  lookup_block l fn.fn_blocks = SOME bb /\ k < LENGTH bb.bb_instructions ==>
  ~MEM v (inst_defs (EL k bb.bb_instructions))
Proof
  simp[current_changing_site_def, inst_defs_def] >> rpt strip_tac >>
  metis_tac[lookup_block_MEM, lookup_block_label, MEM_EL]
QED

Theorem current_non_site_cut_clear:
  ~current_changing_site fn ins v l ==> current_phi_cut_clear fn v l
Proof
  simp[current_phi_cut_clear_def] >> rpt strip_tac >>
  `k < LENGTH bb.bb_instructions` by
    metis_tac[current_collect_phis_length, LESS_LESS_EQ_TRANS] >>
  metis_tac[current_non_site_outputs]
QED

Theorem current_non_site_live_edge:
  wf_function fn /\ fn_cfg_edge fn a b /\
  ~current_changing_site fn ins v a /\ current_phi_cut_clear fn v b /\
  (!pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  current_live_route_edge fn v a b
Proof
  strip_tac >>
  `MEM a (fn_labels fn) /\ MEM b (fn_labels fn)` by
    metis_tac[current_cfg_edge_succs, current_cfg_edge_preds,
      cfg_analyze_succ_labels, cfg_analyze_pred_labels] >>
  `?ab. lookup_block a fn.fn_blocks = SOME ab` by
    (gvs[fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  `?bb. lookup_block b fn.fn_blocks = SOME bb` by
    (gvs[fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  simp[current_live_route_edge_def] >> conj_tac
  >- metis_tac[current_non_site_outputs] >>
  conj_tac >- metis_tac[current_phi_cut_clear_def] >>
  metis_tac[lookup_block_MEM]
QED

Theorem current_non_site_live_route:
  !ls a b. wf_function fn /\ LRC (fn_cfg_edge fn) ls a b /\
  EVERY (\l. ~current_changing_site fn ins v l) ls /\
  current_phi_cut_clear fn v b /\
  (!pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  LRC (current_live_route_edge fn v) ls a b
Proof
  Induct >> simp[LRC_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `z` >> conj_tac
  >- (`current_phi_cut_clear fn v z` by
        (Cases_on `ls` >> gvs[LRC_def] >>
         metis_tac[current_non_site_cut_clear]) >>
      metis_tac[current_non_site_live_edge]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem current_last_site_route_dominates:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ MEM d (fn_labels fn) /\
  current_changing_site fn ins v d /\
  LRC (fn_cfg_edge fn) ls d b /\ ls <> [] /\
  EVERY (\l. ~current_changing_site fn ins v l) (TL ls) /\
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
  strict_dominates (dom_analyze (cfg_analyze fn) fn) d b
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule_all current_route_frontier_crossing >> strip_tac >>
  `EVERY (\l. ~current_changing_site fn ins v l) post` by
    (Cases_on `pre` >> gvs[]) >>
  `LRC (current_live_route_edge fn v) post y b` by
    metis_tac[current_non_site_live_route] >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) y = SOME vs /\ MEM v vs` by
    metis_tac[current_selected_live_route] >>
  `MEM y (frontier_of (dom_analyze (cfg_analyze fn) fn) d)` by
    gvs[ALOOKUP_current_frontier_map] >>
  `ins v y` by metis_tac[] >>
  Cases_on `post` >> gvs[LRC_def, current_changing_site_def]
QED

Theorem current_list_last_site:
  !ls. EVERY (\l. ~P l) ls \/
    ?pre d post. ls = pre ++ d::post /\ P d /\ EVERY (\l. ~P l) post
Proof
  Induct >- simp[] >> gen_tac >>
  Cases_on `EVERY (\l. ~P l) ls`
  >- (Cases_on `P h` >> gvs[] >>
      qexistsl_tac [`[]`, `h`, `ls`] >> simp[]) >>
  gvs[] >> qexistsl_tac [`h::pre`, `d`, `post`] >> simp[]
QED

Theorem current_dominates_route_backwards:
  !ls a b. wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) ls a b /\
  dominates (dom_analyze (cfg_analyze fn) fn) e b /\
  ~MEM e (TL ls ++ [b]) ==>
  dominates (dom_analyze (cfg_analyze fn) fn) e a
Proof
  Induct >> simp[LRC_def] >> rpt strip_tac >> gvs[] >>
  `e <> z` by (Cases_on `ls` >> gvs[LRC_def]) >>
  `~MEM e (TL ls)` by (Cases_on `ls` >> gvs[]) >>
  `dominates (dom_analyze (cfg_analyze fn) fn) e z` by metis_tac[] >>
  `cfg_reachable_of (cfg_analyze fn) h /\
   cfg_reachable_of (cfg_analyze fn) z` by
    metis_tac[current_all_labels_reachable, current_cfg_edge_succs,
      current_cfg_edge_preds, cfg_analyze_succ_labels, cfg_analyze_pred_labels] >>
  metis_tac[dom_dominates_pred, current_cfg_edge_preds]
QED

Theorem current_lrc_append:
  !xs ys a c. LRC R (xs ++ ys) a c <=>
    ?b. LRC R xs a b /\ LRC R ys b c
Proof
  Induct >> simp[LRC_def] >> metis_tac[]
QED

Theorem current_route_last_site:
  LRC R ls root b ==>
  EVERY (\l. ~P l) ls \/
  ?pre d post. ls = pre ++ d::post /\ P d /\ EVERY (\l. ~P l) post /\
    LRC R pre root d /\ LRC R (d::post) d b
Proof
  strip_tac >>
  Cases_on `EVERY (\l. ~P l) ls` >> simp[] >>
  `?pre d post. ls = pre ++ d::post /\ P d /\ EVERY (\l. ~P l) post` by
    metis_tac[current_list_last_site] >>
  qexistsl_tac [`pre`, `d`, `post`] >> gvs[current_lrc_append, LRC_def] >> metis_tac[]
QED

Theorem current_reachable_cfg_route:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) ==>
  ?ls. LRC (fn_cfg_edge fn) ls eb.bb_label a
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) a` by
    metis_tac[current_all_labels_reachable] >>
  drule_all cfg_analyze_semantic_reachability >> strip_tac >>
  ` (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) = fn_cfg_edge fn` by
    simp[FUN_EQ_THM, current_cfg_edge_succs] >>
  gvs[cfg_path_def, RTC_eq_NRC, NRC_LRC] >> metis_tac[]
QED

Theorem current_strict_dom_cfg_pred:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_cfg_edge fn a b /\
  strict_dominates (dom_analyze (cfg_analyze fn) fn) d b ==>
  dominates (dom_analyze (cfg_analyze fn) fn) d a
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) a /\
   cfg_reachable_of (cfg_analyze fn) b` by
    metis_tac[current_all_labels_reachable, current_cfg_edge_succs,
      current_cfg_edge_preds, cfg_analyze_succ_labels, cfg_analyze_pred_labels] >>
  metis_tac[dom_dominates_pred, current_cfg_edge_preds, strict_dominates_def]
QED

Theorem current_site_route_nearest:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) ls d b /\
  EVERY (\l. ~current_changing_site fn ins v l) (TL ls) /\
  current_changing_site fn ins v e /\
  strict_dominates (dom_analyze (cfg_analyze fn) fn) e b ==>
  dominates (dom_analyze (cfg_analyze fn) fn) e d
Proof
  strip_tac >> irule current_dominates_route_backwards >> simp[] >>
  qexistsl_tac [`b`, `ls`] >>
  gvs[EVERY_MEM, strict_dominates_def] >> metis_tac[]
QED

Theorem current_cfg_path_last_site:
  !ls root a. LRC R ls root a ==>
  EVERY (\l. ~P l) (ls ++ [a]) \/
  ?pre d post. ls = pre ++ post /\ LRC R pre root d /\
    LRC R post d a /\ P d /\ EVERY (\l. ~P l) (TL (post ++ [a]))
Proof
  Induct
  >- (simp[LRC_def] >> rpt strip_tac >> Cases_on `P a` >> simp[] >>
      qexistsl_tac [`[]`, `a`, `[]`] >> simp[LRC_def]) >>
  simp[LRC_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac
  >- (Cases_on `P h` >> simp[] >>
      qexistsl_tac [`[]`, `h`, `h::ls`] >> simp[LRC_def] >>
      qexists_tac `z` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`h::pre`, `d`, `post`] >> simp[LRC_def] >>
  qexists_tac `z` >> simp[]
QED

Theorem current_site_path_nearest:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) post d a /\
  EVERY (\l. ~current_changing_site fn ins v l) (TL (post ++ [a])) /\
  current_changing_site fn ins v e /\
  dominates (dom_analyze (cfg_analyze fn) fn) e a ==>
  dominates (dom_analyze (cfg_analyze fn) fn) e d
Proof
  strip_tac >> Cases_on `post` >- gvs[LRC_def] >>
  irule current_dominates_route_backwards >> simp[] >>
  qexistsl_tac [`a`, `h::t`] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_cfg_path_dom_member:
  wf_function fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) ls eb.bb_label a /\
  dominates (dom_analyze (cfg_analyze fn) fn) e a ==>
  MEM e (ls ++ [a])
Proof
  strip_tac >>
  ` (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) = fn_cfg_edge fn` by
    simp[FUN_EQ_THM, current_cfg_edge_succs] >>
  drule dom_on_every_path >>
  disch_then (qspecl_then [`eb`, `ls`, `a`] mp_tac) >>
  gvs[dominates_def] >> metis_tac[]
QED

Theorem current_cut_nearest_site:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
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
  (!e. dominates (dom_analyze (cfg_analyze fn) fn) e a ==>
    ~current_changing_site fn ins v e) \/
  ?d. current_changing_site fn ins v d /\
    dominates (dom_analyze (cfg_analyze fn) fn) d a /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) d b /\
    (!e. current_changing_site fn ins v e /\
      dominates (dom_analyze (cfg_analyze fn) fn) e a ==>
      dominates (dom_analyze (cfg_analyze fn) fn) e d)
Proof
  strip_tac >>
  `MEM a (fn_labels fn)` by
    metis_tac[current_cfg_edge_preds, cfg_analyze_pred_labels] >>
  drule_all current_reachable_cfg_route >> strip_tac >>
  drule current_cfg_path_last_site >>
  disch_then (qspec_then `current_changing_site fn ins v` mp_tac) >> strip_tac
  >- (disj1_tac >> rpt strip_tac >>
      `MEM e (ls ++ [a])` by metis_tac[current_cfg_path_dom_member] >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `d` >> simp[] >>
  `MEM d (fn_labels fn)` by
    (Cases_on `post` >> gvs[LRC_def] >>
     metis_tac[current_cfg_edge_preds, cfg_analyze_pred_labels]) >>
  `LRC (fn_cfg_edge fn) (post ++ [a]) d b` by
    (simp[current_lrc_append, LRC_def] >> metis_tac[]) >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) d b` by
    (irule current_last_site_route_dominates >> simp[] >>
     qexistsl_tac [`ins`, `post ++ [a]`, `v`] >> simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[current_strict_dom_cfg_pred] >>
  simp[] >> metis_tac[current_site_path_nearest]
QED

Theorem current_chain_prefix_dominated:
  !ps a pre d ds. wf_function fn /\ all_reachable fn /\
  entry_block fn = SOME eb /\ MEM a (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  a::ps = pre ++ d::ds ==>
  !e. MEM e pre ==> dominates (dom_analyze (cfg_analyze fn) fn) d e
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (Cases_on `pre` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps h /\
    idom_of (dom_analyze (cfg_analyze fn) fn) a = SOME h` by
    gvs[current_token_chain_def] >>
  `MEM h (fn_labels fn)` by
    metis_tac[idom_is_immediate, strict_dominates_def, dom_labels_bounded,
      dominates_def, current_all_labels_reachable] >>
  Cases_on `pre` >- simp[] >>
  fs[] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d a` by
    (qspecl_then [`t ++ [d] ++ ds`, `a`] mp_tac current_actual_chain_membership >>
     simp[] >> disch_then (qspec_then `d` mp_tac) >>
     simp[strict_dominates_def]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_chain_nearest_site_split:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  MEM d (a::ps) /\ P d /\
  (!e. MEM e (a::ps) /\ P e ==>
    dominates (dom_analyze (cfg_analyze fn) fn) e d) ==>
  ?pre ds. a::ps = pre ++ d::ds /\ EVERY (\e. ~P e) pre
Proof
  strip_tac >> drule_all current_token_chain_member_suffix >> strip_tac >>
  qexistsl_tac [`pre`, `ds`] >> simp[EVERY_MEM] >> rpt strip_tac >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d e` by
    metis_tac[current_chain_prefix_dominated] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) e d` by
    metis_tac[MEM_APPEND, MEM] >>
  `cfg_reachable_of (cfg_analyze fn) d` by
    (drule_all current_actual_chain_membership >>
     disch_then (qspec_then `d` mp_tac) >>
     gvs[strict_dominates_def] >>
     metis_tac[dominates_reachable, current_all_labels_reachable]) >>
  `cfg_reachable_of (cfg_analyze fn) e` by metis_tac[dominates_reachable] >>
  `e = d` by metis_tac[dominates_antisym] >>
  `ALL_DISTINCT (pre ++ d::ds)` by metis_tac[current_actual_chain_distinct] >>
  fs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem current_nearest_site_common_scans:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_cfg_edge fn a b /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  current_changing_site fn ins v d /\
  dominates (dom_analyze (cfg_analyze fn) fn) d a /\
  strict_dominates (dom_analyze (cfg_analyze fn) fn) d b /\
  (!e. current_changing_site fn ins v e /\
    dominates (dom_analyze (cfg_analyze fn) fn) e a ==>
    dominates (dom_analyze (cfg_analyze fn) fn) e d) ==>
  ?apre apost bpre bpost.
    REVERSE ps ++ [a] = apre ++ d::apost /\
    REVERSE qs = bpre ++ d::bpost /\
    EVERY (\e. ~current_changing_site fn ins v e) apost /\
    EVERY (\e. ~current_changing_site fn ins v e) bpost
Proof
  strip_tac >>
  `MEM a (fn_labels fn) /\ MEM b (fn_labels fn)` by
    metis_tac[current_cfg_edge_succs, current_cfg_edge_preds,
      cfg_analyze_succ_labels, cfg_analyze_pred_labels] >>
  `!e. MEM e ps <=> strict_dominates (dom_analyze (cfg_analyze fn) fn) e a` by
    metis_tac[current_actual_chain_membership] >>
  `!e. MEM e qs <=> strict_dominates (dom_analyze (cfg_analyze fn) fn) e b` by
    metis_tac[current_actual_chain_membership] >>
  `MEM d (a::ps)` by gvs[strict_dominates_def] >>
  `?pre ds. a::ps = pre ++ d::ds /\
    EVERY (\e. ~current_changing_site fn ins v e) pre` by
    (irule current_chain_nearest_site_split >> simp[] >>
     metis_tac[strict_dominates_def, dom_self, current_all_labels_reachable]) >>
  `?pre' ds'. b::qs = pre' ++ d::ds' /\
    EVERY (\e. ~(e <> b /\ current_changing_site fn ins v e)) pre'` by
    (irule (BETA_RULE (Q.INST [`P` |-> `\e. e <> b /\ current_changing_site fn ins v e`]
       current_chain_nearest_site_split)) >> simp[] >>
     rpt strip_tac >>
     metis_tac[current_strict_dom_cfg_pred, strict_dominates_def]) >>
  Cases_on `pre'` >- gvs[strict_dominates_def] >>
  `qs = t ++ d::ds'` by gvs[] >>
  qexistsl_tac [`REVERSE ds`, `REVERSE pre`, `REVERSE ds'`, `REVERSE t`] >>
  conj_tac
  >- (pure_rewrite_tac[GSYM (CONJUNCT2 REVERSE_DEF)] >>
      once_asm_rewrite_tac[] >> simp[REVERSE_APPEND]) >>
  simp[REVERSE_APPEND] >> gvs[EVERY_MEM] >>
  metis_tac[strict_dominates_def]
QED

Theorem current_no_site_common_scans:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_cfg_edge fn a b /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  (!e. dominates (dom_analyze (cfg_analyze fn) fn) e a ==>
    ~current_changing_site fn ins v e) ==>
  EVERY (\e. ~current_changing_site fn ins v e) (REVERSE ps ++ [a]) /\
  EVERY (\e. ~current_changing_site fn ins v e) (REVERSE qs)
Proof
  strip_tac >>
  `MEM a (fn_labels fn) /\ MEM b (fn_labels fn)` by
    metis_tac[current_cfg_edge_succs, current_cfg_edge_preds,
      cfg_analyze_succ_labels, cfg_analyze_pred_labels] >>
  `!e. MEM e ps <=> strict_dominates (dom_analyze (cfg_analyze fn) fn) e a` by
    metis_tac[current_actual_chain_membership] >>
  `!e. MEM e qs <=> strict_dominates (dom_analyze (cfg_analyze fn) fn) e b` by
    metis_tac[current_actual_chain_membership] >>
  simp[EVERY_MEM] >>
  metis_tac[current_strict_dom_cfg_pred, strict_dominates_def,
    dom_self, current_all_labels_reachable]
QED

Theorem current_cut_common_last_site:
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
  (EVERY (\e. ~current_changing_site fn ins v e) (REVERSE ps ++ [a]) /\
   EVERY (\e. ~current_changing_site fn ins v e) (REVERSE qs)) \/
  ?d apre apost bpre bpost.
    current_changing_site fn ins v d /\
    REVERSE ps ++ [a] = apre ++ d::apost /\
    REVERSE qs = bpre ++ d::bpost /\
    EVERY (\e. ~current_changing_site fn ins v e) apost /\
    EVERY (\e. ~current_changing_site fn ins v e) bpost
Proof
  strip_tac >> drule current_cut_nearest_site >>
  disch_then (qspecl_then [`v`, `ins`, `eb`, `b`, `a`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac
  >- (disj1_tac >> metis_tac[current_no_site_common_scans]) >>
  disj2_tac >> qexists_tac `d` >> simp[] >>
  irule (SRULE [] current_nearest_site_common_scans) >> simp[] >> metis_tac[]
QED
