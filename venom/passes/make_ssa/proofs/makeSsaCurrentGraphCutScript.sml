Theory makeSsaCurrentGraphCut
Ancestors
  makeSsaCurrentTokenGraph makeSsaCurrentTokens makeSsaCurrentAnalysis
  dominatorAnalysisProps dominatorDefs venomInst list pred_set

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
