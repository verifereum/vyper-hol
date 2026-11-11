Theory makeSsaCurrentGraphCut
Ancestors
  makeSsaCurrentTokenGraph makeSsaCurrentTokens makeSsaCurrentAnalysis
  makeSsaCurrentFrontier dominatorProofs cfgDefs venomWf cfgAnalysisProps
  dominatorProofs dominatorDefs venomInst list pred_set cfgCorrectnessProof

Theorem current_strict_dom_parent:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) l /\
  idom_of (dom_analyze (cfg_analyze fn) fn) l = SOME p ==>
  !d. strict_dominates (dom_analyze (cfg_analyze fn) fn) d l <=>
    d = p \/ strict_dominates (dom_analyze (cfg_analyze fn) fn) d p
Proof
  strip_tac >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) p l /\
   (!d. strict_dominates (dom_analyze (cfg_analyze fn) fn) d l /\ d <> p ==>
      dominates (dom_analyze (cfg_analyze fn) fn) d p)` by
    metis_tac[idom_is_immediate] >>
  gen_tac >> eq_tac
  >- (strip_tac >> Cases_on `d = p` >> simp[] >>
      metis_tac[strict_dominates_def]) >>
  strip_tac >- gvs[] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d l` by
    metis_tac[dominates_trans, strict_dominates_def] >>
  `cfg_reachable_of (cfg_analyze fn) p` by
    metis_tac[dominates_reachable, strict_dominates_def] >>
  `d <> l` by metis_tac[dominates_antisym, strict_dominates_def] >>
  simp[strict_dominates_def]
QED

Theorem current_actual_chain_membership:
  !ps l. wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l ==>
  !d. MEM d ps <=> strict_dominates (dom_analyze (cfg_analyze fn) fn) d l
Proof
  Induct >> simp[current_token_chain_def] >> rpt strip_tac
  >- (`set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators
         eb.bb_label) = {eb.bb_label}` by metis_tac[dom_entry_self] >>
      gvs[EXTENSION, dominates_def, strict_dominates_def] >> metis_tac[]) >>
  `cfg_reachable_of (cfg_analyze fn) l` by metis_tac[current_all_labels_reachable] >>
  `MEM h (fn_labels fn)` by
    metis_tac[idom_is_immediate, strict_dominates_def, dom_labels_bounded,
      dominates_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all current_strict_dom_parent >> simp[] >> metis_tac[]
QED

Theorem current_actual_chain_distinct:
  !ps l. wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l ==>
  ALL_DISTINCT (l::ps)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps h /\
   idom_of (dom_analyze (cfg_analyze fn) fn) l = SOME h` by
    gvs[current_token_chain_def] >>
  `cfg_reachable_of (cfg_analyze fn) l` by metis_tac[current_all_labels_reachable] >>
  `MEM h (fn_labels fn)` by
    metis_tac[idom_is_immediate, strict_dominates_def, dom_labels_bounded,
      dominates_def] >>
  `ALL_DISTINCT (h::ps)` by metis_tac[] >>
  `~MEM l (h::ps)` by
    (qpat_x_assum `current_token_chain _ _ ps h` kall_tac >>
     drule_all current_actual_chain_membership >>
     disch_then (qspec_then `l` mp_tac) >> simp[strict_dominates_def]) >>
  simp[]
QED

Theorem current_token_chain_member_suffix:
  !ps l d. current_token_chain dom root ps l /\ MEM d (l::ps) ==>
  ?pre ds. l::ps = pre ++ d::ds /\ current_token_chain dom root ds d
Proof
  Induct >> simp[current_token_chain_def] >> rpt strip_tac
  >- (qexistsl_tac [`[]`, `[]`] >> simp[current_token_chain_def]) >>
  Cases_on `d = l`
  >- (qexistsl_tac [`[]`, `h::ps`] >> simp[current_token_chain_def]) >>
  `MEM d (h::ps)` by gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`l::pre`, `ds`] >> simp[]
QED

Theorem current_token_chain_root_member:
  !ps l. current_token_chain dom root ps l ==> MEM root (l::ps)
Proof
  Induct >> simp[current_token_chain_def] >> metis_tac[]
QED

Theorem current_token_chain_common_suffix:
  !ps a qs b. idom_of dom root = NONE /\
    current_token_chain dom root ps a /\ current_token_chain dom root qs b ==>
  ?common xs ys. a::ps = xs ++ common /\ b::qs = ys ++ common /\
    DISJOINT (set xs) (set ys)
Proof
  Induct >> rpt strip_tac
  >- (gvs[current_token_chain_def] >>
      `MEM a (b::qs)` by metis_tac[current_token_chain_root_member] >>
      drule_all current_token_chain_member_suffix >> strip_tac >>
      `ds = []` by metis_tac[current_token_chain_root] >>
      gvs[] >> qexistsl_tac [`[a]`, `[]`, `pre`] >> simp[]) >>
  Cases_on `MEM a (b::qs)`
  >- (drule_all current_token_chain_member_suffix >> strip_tac >>
      `ds = h::ps` by metis_tac[current_token_chain_unique] >>
      gvs[] >> qexistsl_tac [`a::h::ps`, `[]`, `pre`] >> simp[]) >>
  gvs[current_token_chain_def] >> first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`common`, `a::xs`, `ys`] >> simp[] >>
  gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[MEM_APPEND, MEM]
QED

Theorem current_token_chain_common_prefix:
  idom_of dom root = NONE /\ current_token_chain dom root ps a /\
  current_token_chain dom root qs b ==>
  ?common xs ys. REVERSE (a::ps) = common ++ xs /\
    REVERSE (b::qs) = common ++ ys /\ DISJOINT (set xs) (set ys)
Proof
  strip_tac >> drule current_token_chain_common_suffix >>
  disch_then (qspecl_then [`ps`, `a`, `qs`, `b`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`REVERSE common`, `REVERSE xs`, `REVERSE ys`] >>
  pure_rewrite_tac [GSYM (CONJUNCT2 REVERSE_DEF), GSYM REVERSE_APPEND] >>
  conj_tac >- (AP_TERM_TAC >> asm_rewrite_tac[]) >>
  conj_tac >- (AP_TERM_TAC >> asm_rewrite_tac[]) >> simp[]
QED

Theorem current_actual_ancestors_comparable:
  !ps l. wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l ==>
  !d e. MEM d (l::ps) /\ MEM e (l::ps) ==>
    dominates (dom_analyze (cfg_analyze fn) fn) d e \/
    dominates (dom_analyze (cfg_analyze fn) fn) e d
Proof
  Induct
  >- (simp[] >> rpt strip_tac >> gvs[] >> metis_tac[dom_self]) >>
  rpt gen_tac >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps h /\
   idom_of (dom_analyze (cfg_analyze fn) fn) l = SOME h` by
    gvs[current_token_chain_def] >>
  `cfg_reachable_of (cfg_analyze fn) l` by metis_tac[current_all_labels_reachable] >>
  `MEM h (fn_labels fn)` by
    metis_tac[idom_is_immediate, strict_dominates_def, dom_labels_bounded,
      dominates_def] >>
  `!d. MEM d (h::ps) ==> dominates (dom_analyze (cfg_analyze fn) fn) d l` by
    (qpat_x_assum `current_token_chain _ _ ps h` kall_tac >>
     drule_all current_actual_chain_membership >>
     simp[strict_dominates_def]) >>
  rpt gen_tac >> strip_tac >> Cases_on `d = l` >> Cases_on `e = l` >>
  gvs[] >> metis_tac[dom_self]
QED

Theorem current_frontier_edge_intro:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ MEM d (fn_labels fn) /\
  MEM y (fn_labels fn) /\ MEM p (cfg_preds_of (cfg_analyze fn) y) /\
  dominates (dom_analyze (cfg_analyze fn) fn) d p /\
  ~strict_dominates (dom_analyze (cfg_analyze fn) fn) d y ==>
  MEM y (THE (ALOOKUP (current_frontier_map fn) d))
Proof
  strip_tac >>
  `fn_entry_label fn <> SOME y` by
    (strip_tac >> drule_all current_entry_preds_empty >> simp[] >>
     strip_tac >> gvs[]) >>
  `y <> eb.bb_label` by gvs[fn_entry_label_def] >>
  `cfg_reachable_of (cfg_analyze fn) y` by
    metis_tac[current_all_labels_reachable] >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) y) > 1` by
    (spose_not_then assume_tac >>
     `cfg_preds_of (cfg_analyze fn) y = [p]` by
       (Cases_on `cfg_preds_of (cfg_analyze fn) y` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>
     Cases_on `d = y`
     >- (drule_all exists_pred_not_dominated >> gvs[]) >>
     `set (cfg_preds_of (cfg_analyze fn) y) = {p}` by simp[] >>
     drule_all current_single_pred_dominates >>
     disch_then (qspec_then `d` mp_tac) >> gvs[strict_dominates_def]) >>
  `!q. MEM q (cfg_preds_of (cfg_analyze fn) y) ==>
     cfg_reachable_of (cfg_analyze fn) q` by
    (rpt strip_tac >> irule current_all_labels_reachable >> simp[] >>
     gvs[GSYM current_cfg_edge_preds, fn_cfg_edge_def, fn_labels_def, MEM_MAP] >>
     metis_tac[]) >>
  `cfg_reachable_of (cfg_analyze fn) d` by
    metis_tac[current_all_labels_reachable] >>
  mp_tac (Q.INST [`n` |-> `d`] current_frontier_query_correct) >>
  simp[] >> metis_tac[]
QED

(* The prefix includes its source and excludes the first failing vertex. *)
Theorem current_route_first_exit:
  !ls a b. LRC R ls a b /\ P a /\ ~P b ==>
  ?pre p y post. ls = pre ++ p::post /\
    LRC R pre a p /\ EVERY P pre /\ P p /\ R p y /\ ~P y /\
    LRC R post y b
Proof
  Induct >> simp[LRC_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `P z`
  >- (first_x_assum drule_all >> strip_tac >>
      qexistsl_tac [`h::pre`, `p`, `y`, `post`] >> simp[LRC_def] >>
      qexists_tac `z` >> simp[]) >>
  qexistsl_tac [`[]`, `h`, `z`, `ls`] >> simp[LRC_def]
QED

Theorem current_route_first_subsequent_exit:
  !ls a b. LRC R ls a b /\ ls <> [] /\ ~P b ==>
  ?pre p y post. ls = pre ++ p::post /\
    LRC R pre a p /\ EVERY P (TL (pre ++ [p])) /\
    (p = a \/ P p) /\ R p y /\ ~P y /\ LRC R post y b
Proof
  Cases >> simp[LRC_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `P z`
  >- (`?pre p y post. t = pre ++ p::post /\
         LRC R pre z p /\ EVERY P pre /\ P p /\ R p y /\ ~P y /\
         LRC R post y b` by metis_tac[current_route_first_exit] >>
      qexistsl_tac [`h::pre`, `p`, `y`, `post`] >> simp[LRC_def] >>
      qexists_tac `z` >> simp[]) >>
  qexistsl_tac [`[]`, `h`, `z`, `t`] >> simp[LRC_def]
QED

Theorem current_route_frontier_crossing:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ MEM d (fn_labels fn) /\
  LRC (fn_cfg_edge fn) ls d b /\ ls <> [] /\
  ~strict_dominates (dom_analyze (cfg_analyze fn) fn) d b ==>
  ?pre p y post. ls = pre ++ p::post /\
    LRC (fn_cfg_edge fn) pre d p /\
    EVERY (strict_dominates (dom_analyze (cfg_analyze fn) fn) d)
      (TL (pre ++ [p])) /\
    fn_cfg_edge fn p y /\
    dominates (dom_analyze (cfg_analyze fn) fn) d p /\
    ~strict_dominates (dom_analyze (cfg_analyze fn) fn) d y /\
    MEM y (THE (ALOOKUP (current_frontier_map fn) d)) /\
    LRC (fn_cfg_edge fn) post y b
Proof
  strip_tac >> drule_all current_route_first_subsequent_exit >> strip_tac >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d p` by
    metis_tac[dom_self, strict_dominates_def] >>
  `MEM y (THE (ALOOKUP (current_frontier_map fn) d))` by
    (irule current_frontier_edge_intro >>
     simp[GSYM current_cfg_edge_preds] >>
     conj_tac >- metis_tac[current_cfg_edge_succs, cfg_analyze_succ_labels] >>
     qexists_tac `p` >> simp[]) >>
  qexistsl_tac [`pre`, `p`, `y`, `post`] >> metis_tac[]
QED
