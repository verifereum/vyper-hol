Theory makeSsaCurrentTokenGraph
Ancestors
  makeSsaCurrentTokens makeSsaCurrentAnalysis makeSsaCurrentTree
  dominatorAnalysisProps dominatorRankProofs dominatorDefs pred_set

Theorem current_token_root_idom:
  wf_function fn /\ entry_block fn = SOME eb ==>
  idom_of (dom_analyze (cfg_analyze fn) fn) eb.bb_label = NONE
Proof
  metis_tac[idom_entry_none]
QED

Theorem current_actual_token_chain:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) ==>
  ?ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l
Proof
  completeInduct_on `dominator_query_rank fn l` >> rpt strip_tac >>
  Cases_on `l = eb.bb_label`
  >- (qexists_tac `[]` >> simp[current_token_chain_def]) >>
  drule_all current_dom_parent_exists >> strip_tac >>
  `dominator_query_rank fn p < dominator_query_rank fn l` by
    metis_tac[current_dom_child_rank] >>
  first_x_assum (qspec_then `dominator_query_rank fn p` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`fn`, `p`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `p::ps` >> irule current_token_chain_parent >>
  gvs[current_tree_edge_def, dominatorQueryProofsTheory.dominated_query_membership]
QED

Theorem current_actual_token_chain_unique:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) ==>
  ?!ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l
Proof
  strip_tac >> simp[EXISTS_UNIQUE_THM] >> conj_tac
  >- metis_tac[current_actual_token_chain] >>
  metis_tac[current_token_chain_unique, current_token_root_idom]
QED

Theorem current_actual_root_chain:
  wf_function fn /\ entry_block fn = SOME eb ==>
  (current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps
     eb.bb_label <=> ps = [])
Proof
  metis_tac[current_token_root_idom, current_token_chain_root]
QED

Theorem current_actual_root_token:
  wf_function fn /\ entry_block fn = SOME eb /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps eb.bb_label ==>
  current_inherited_token fn ins v (REVERSE ps) = CurrentDefault v
Proof
  strip_tac >> `ps = []` by metis_tac[current_actual_root_chain] >>
  simp[current_inherited_token_root]
QED

Theorem current_single_pred_dominates:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM b (fn_labels fn) /\ b <> eb.bb_label /\
  set (cfg_preds_of (cfg_analyze fn) b) = {a} ==>
  !d. dominates (dom_analyze (cfg_analyze fn) fn) d b <=>
      d = b \/ dominates (dom_analyze (cfg_analyze fn) fn) d a
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) b` by
    metis_tac[current_all_labels_reachable] >>
  `cfg_preds_of (cfg_analyze fn) b <> []` by
    (strip_tac >> gvs[]) >>
  qspecl_then [`fn`, `cfg_analyze fn`, `eb`, `b`] mp_tac dom_fixpoint_equation >>
  simp[] >> strip_tac >>
  simp[dominates_def] >> metis_tac[IN_UNION, IN_SING, listTheory.MEM]
QED

Theorem current_single_pred_idom:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\ MEM b (fn_labels fn) /\
  b <> eb.bb_label /\ a <> b /\
  set (cfg_preds_of (cfg_analyze fn) b) = {a} ==>
  idom_of (dom_analyze (cfg_analyze fn) fn) b = SOME a
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) a /\
   cfg_reachable_of (cfg_analyze fn) b` by
    metis_tac[current_all_labels_reachable] >>
  `?d. idom_of (dom_analyze (cfg_analyze fn) fn) b = SOME d` by
    metis_tac[idom_exists] >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) a b` by
    (simp[strict_dominates_def] >>
     drule_all current_single_pred_dominates >>
     disch_then (qspec_then `a` mp_tac) >> metis_tac[dom_self]) >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) d b /\
   (!c. strict_dominates (dom_analyze (cfg_analyze fn) fn) c b /\ c <> d ==>
     dominates (dom_analyze (cfg_analyze fn) fn) c d)` by
    metis_tac[idom_is_immediate] >>
  Cases_on `a = d` >- gvs[] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) a d` by metis_tac[] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d a` by
    (drule_all current_single_pred_dominates >>
     disch_then (qspec_then `d` mp_tac) >> gvs[strict_dominates_def]) >>
  `cfg_reachable_of (cfg_analyze fn) d` by metis_tac[dominates_reachable] >>
  metis_tac[dominates_antisym]
QED

Theorem current_single_pred_token:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\ MEM b (fn_labels fn) /\
  b <> eb.bb_label /\ a <> b /\
  set (cfg_preds_of (cfg_analyze fn) b) = {a} /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b ==>
  current_block_token fn ins v a (current_inherited_token fn ins v (REVERSE ps)) =
  current_inherited_token fn ins v (REVERSE qs)
Proof
  strip_tac >> sym_tac >> irule current_token_parent_edge >>
  metis_tac[current_single_pred_idom, current_token_root_idom]
QED

(* DIAGNOSTIC ONLY -- proposed pruned cut, NOT a theorem or an axiom.

   Ordinary/non-PHI-operand branch (all variables universally quantified):

   wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\
   fn_defs_reach_uses fn /\ entry_block fn = SOME eb /\
   MEM a (fn_labels fn) /\ MEM b (fn_labels fn) /\
   fn_cfg_edge fn a b /\ b <> eb.bb_label /\
   LENGTH (cfg_preds_of (cfg_analyze fn) b) > 1 /\
   fn_entry_label fn <> SOME b /\
   (!p. MEM p (cfg_preds_of (cfg_analyze fn) b) ==>
        cfg_reachable_of (cfg_analyze fn) p) /\
   (!w l. ins w l ==> MEM l (fn_labels fn)) /\
   (!d y.
     ((?db di. MEM db fn.fn_blocks /\ db.bb_label = d /\
                MEM di db.bb_instructions /\ MEM v di.inst_outputs) \/ ins v d) /\
     MEM y (frontier_of (dom_analyze (cfg_analyze fn) fn) d) /\
     (?vs. ALOOKUP
       (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
          (liveness_analyze fn) fn) y = SOME vs /\ MEM v vs) ==>
     ins v y) /\
   current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
   current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
   lookup_block b fn.fn_blocks = SOME bb /\ ~ins v b /\
   (!phi. MEM phi (collect_phis bb.bb_instructions) ==>
          ~MEM v phi.inst_outputs) /\
   MEM v (live_vars_at (liveness_analyze fn) b
     (LENGTH (collect_phis bb.bb_instructions))) /\
   (?vs. ALOOKUP
     (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
        (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
   ~(?pb phi pred. MEM pb fn.fn_blocks /\
        MEM phi (collect_phis pb.bb_instructions) /\
        MEM (pred,v) (phi_pairs phi.inst_operands))
   ==>
   current_block_token fn ins v a
     (current_inherited_token fn ins v (REVERSE ps)) =
   current_inherited_token fn ins v (REVERSE qs).

   The duplicate-looking selected-map and cut-slot premises intentionally
   expose the missing adapter rather than assume the two queries coincide.
   Original defining blocks are stated directly, not via an unproved converse
   of compute_defs_support.  Actual placement must eventually instantiate
   ins from its insertion provenance, NOT the larger processed/has_phi set.

   Exceptional PHI-operand branch: replace the final negated existential by
   its positive form and add fn_phi_operands_single_def fn.  At the demanded
   cut use current_live_phi_cut_single_definition to obtain one defining
   occurrence, semantic dominance, and a local earlier index if appropriate.
   This branch must not use ordinary liveness propagation through PHI inputs.

   Missing interfaces, not assumptions silently available to a proof:
   1. Finite analyzed parent-chain membership <=> semantic fn_dominates,
      plus comparability/common prefix, with an adapter from fn_dominates
      to the analyzed dominates relation.  Chain existence alone does not
      identify which sites lie on a predecessor's chain.
   2. A differing-token witness: the last original/inserted changing site on
      one suffix after the chains' common prefix, together with a CFG route
      to the target and a definition-free suffix.  Must handle loops and
      revisited blocks, not assume the dominator chain is a CFG path.
   3. First frontier crossing: such a site dominates a reachable predecessor
      of a crossing y but does not strictly dominate y.  dom_frontier_correct
      additionally requires y non-entry, >1 predecessors and all reachable;
      these must be proved at y, not merely assumed at final block b.
   4. Selected-liveness backward transport on that definition-free suffix.
      current_demand is an over-approximation of the selected live sets:
      demand alone cannot activate live-filtered closure.  The source audit
      found no exported current_demand_path/current_demand_at_phi_cut/
      current_demand_cross_block under those names.  The available boundary
      current_liveness_edge_origin gives an inversion, not this converse.
   5. For the exceptional branch, singleton-definition availability gives
      semantic dominance (DemandDominance), but still needs (1) and an
      insertion-locality argument.  current_phi_operand_available currently
      lives in Defined with protected SCCP prerequisites; do not import it
      into this lightweight graph boundary or presume it is build-verified.

   None of (1)--(5), nor either candidate cut, is exported by this file.
*)
