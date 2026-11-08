Theory makeSsaCurrentNonDegTokenSources
Ancestors
  makeSsaCurrentTokens makeSsaCurrentCutTokens makeSsaCurrentLastSite
  makeSsaCurrentGraphCut dominatorProofs dominatorDefs
  venomWf venomInst list

Definition current_nondeg_token_at_def:
  (current_nondeg_token_at l (CurrentDefault v) = F) /\
  (current_nondeg_token_at l (CurrentOriginal b i j) = (b = l)) /\
  (current_nondeg_token_at l (CurrentInserted v b) = (b = l))
End

Theorem current_nondeg_token_at_unique:
  current_nondeg_token_at l t /\ current_nondeg_token_at k t ==> l = k
Proof
  Cases_on `t` >> simp[current_nondeg_token_at_def] >> metis_tac[]
QED

Theorem current_nondeg_output_token_local:
  !xs j t. current_output_token v l i j xs t = t \/
    current_nondeg_token_at l (current_output_token v l i j xs t)
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h = v` >> simp[] >>
  metis_tac[current_nondeg_token_at_def]
QED

Theorem current_nondeg_original_scan_local:
  !insts i t. current_original_scan v l i insts t = t \/
    current_nondeg_token_at l (current_original_scan v l i insts t)
Proof
  Induct >> simp[current_original_scan_def] >>
  metis_tac[current_nondeg_output_token_local]
QED

Theorem current_nondeg_block_token_local:
  current_block_token fn ins v l t = t \/
  current_nondeg_token_at l (current_block_token fn ins v l t)
Proof
  simp[current_block_token_def] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  Cases_on `ins v l` >> simp[] >>
  metis_tac[current_nondeg_original_scan_local, current_nondeg_token_at_def]
QED

Theorem current_nondeg_changing_block_reset:
  wf_function fn /\ MEM l (fn_labels fn) /\ current_changing_site fn ins v l ==>
  current_nondeg_token_at l (current_block_token fn ins v l t)
Proof
  strip_tac >>
  drule_all current_site_block_constant >>
  disch_then (qspecl_then [`t`, `CurrentInserted v l`] assume_tac) >>
  metis_tac[current_nondeg_block_token_local, current_nondeg_token_at_def]
QED

Theorem current_nondeg_chain_token_local:
  !ls t. current_chain_token fn ins v ls t = t \/
    ?l. MEM l ls /\ current_nondeg_token_at l (current_chain_token fn ins v ls t)
Proof
  Induct >> simp[current_chain_token_def] >>
  metis_tac[current_nondeg_block_token_local]
QED

Theorem current_nondeg_changing_chain_source:
  wf_function fn /\ MEM d (fn_labels fn) /\ current_changing_site fn ins v d ==>
  ?l. MEM l (d::xs) /\
      current_nondeg_token_at l (current_chain_token fn ins v (d::xs) t)
Proof
  strip_tac >> simp[current_chain_token_def] >>
  drule_all current_nondeg_changing_block_reset >> strip_tac >>
  metis_tac[current_nondeg_chain_token_local]
QED

Theorem current_nondeg_disjoint_chain_tokens:
  wf_function fn /\ MEM d (fn_labels fn) /\ current_changing_site fn ins v d /\
  DISJOINT (set (d::xs)) (set ys) /\
  (!l. MEM l (d::xs) ==> ~current_nondeg_token_at l u) ==>
  current_chain_token fn ins v (d::xs) t <> current_chain_token fn ins v ys u
Proof
  strip_tac >>
  drule_all current_nondeg_changing_chain_source >> strip_tac >>
  spose_not_then assume_tac >>
  `current_chain_token fn ins v ys u = u \/
   ?k. MEM k ys /\ current_nondeg_token_at k (current_chain_token fn ins v ys u)` by
    metis_tac[current_nondeg_chain_token_local] >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[current_nondeg_token_at_unique]
QED

Theorem current_nondeg_actual_exit_source:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\ MEM d (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  dominates (dom_analyze (cfg_analyze fn) fn) d a /\
  current_changing_site fn ins v d ==>
  ?l. current_nondeg_token_at l
        (current_chain_token fn ins v (REVERSE ps ++ [a]) t) /\
      dominates (dom_analyze (cfg_analyze fn) fn) d l
Proof
  strip_tac >>
  `MEM d (a::ps)` by
    (Cases_on `d = a` >> simp[] >>
     metis_tac[current_actual_chain_membership, strict_dominates_def]) >>
  drule_all current_token_chain_member_suffix >> strip_tac >>
  `REVERSE ps ++ [a] = REVERSE ds ++ d::REVERSE pre` by
    metis_tac[listTheory.REVERSE_APPEND, listTheory.REVERSE_DEF,
              listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  qpat_x_assum `REVERSE ps ++ [a] = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[current_chain_token_append] >>
  drule_all current_nondeg_changing_chain_source >>
  disch_then (qspecl_then [`REVERSE pre`,
    `current_chain_token fn ins v (REVERSE ds) t`] strip_assume_tac) >>
  qexists `l` >> simp[] >>
  Cases_on `l = d` >- (gvs[] >> metis_tac[dom_self]) >>
  `MEM l pre` by gvs[] >>
  metis_tac[current_chain_prefix_dominated]
QED

Theorem current_nondeg_actual_exit_tokens_distinct:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\ MEM b (fn_labels fn) /\ MEM d (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  current_changing_site fn ins v d /\
  dominates (dom_analyze (cfg_analyze fn) fn) d a /\
  ~dominates (dom_analyze (cfg_analyze fn) fn) d b ==>
  current_chain_token fn ins v (REVERSE ps ++ [a]) (CurrentDefault v) <>
  current_chain_token fn ins v (REVERSE qs ++ [b]) (CurrentDefault v)
Proof
  strip_tac >>
  drule_all current_nondeg_actual_exit_source >>
  disch_then (qspec_then `CurrentDefault v` strip_assume_tac) >>
  spose_not_then assume_tac >>
  qspec_then `REVERSE qs ++ [b]`
    (qspec_then `CurrentDefault v` strip_assume_tac)
    current_nondeg_chain_token_local
  >- metis_tac[current_nondeg_token_at_def] >>
  `l = l'` by metis_tac[current_nondeg_token_at_unique] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) l b` by
    (gvs[] >> Cases_on `l = b` >- (gvs[] >> metis_tac[dom_self]) >>
     metis_tac[current_actual_chain_membership, strict_dominates_def]) >>
  `cfg_reachable_of (cfg_analyze fn) b` by
    metis_tac[makeSsaCurrentAnalysisTheory.current_all_labels_reachable] >>
  metis_tac[dominates_trans]
QED

Theorem current_nondeg_output_preserves_noninserted:
  !xs j t. t <> CurrentInserted w h ==>
    current_output_token v l i j xs t <> CurrentInserted w h
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h' = v` >> simp[]
QED

Theorem current_nondeg_output_resets_inserted:
  !xs j t. MEM v xs ==>
    current_output_token v l i j xs t <> CurrentInserted w h
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h' = v` >> simp[current_nondeg_output_preserves_noninserted]
QED

Theorem current_nondeg_original_preserves_noninserted:
  !insts i t. t <> CurrentInserted w h ==>
    current_original_scan v l i insts t <> CurrentInserted w h
Proof
  Induct >- simp[current_original_scan_def] >>
  rpt gen_tac >> disch_tac >> rewrite_tac[current_original_scan_def] >>
  first_x_assum irule >> simp[current_nondeg_output_preserves_noninserted]
QED

Theorem current_nondeg_original_resets_inserted:
  !insts i t. (?inst. MEM inst insts /\ MEM v inst.inst_outputs) ==>
    current_original_scan v l i insts t <> CurrentInserted w h
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  rewrite_tac[current_original_scan_def] >>
  Cases_on `inst = h'`
  >- (irule current_nondeg_original_preserves_noninserted >>
      gvs[current_nondeg_output_resets_inserted]) >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED

Theorem current_nondeg_chain_preserves_noninserted:
  !ls t. ~MEM h ls /\ t <> CurrentInserted w h ==>
    current_chain_token fn ins v ls t <> CurrentInserted w h
Proof
  rpt strip_tac >>
  qspec_then `ls` (qspec_then `t` strip_assume_tac)
    current_nondeg_chain_token_local >>
  gvs[current_nondeg_token_at_def]
QED

Theorem current_nondeg_original_ancestor_exit_nonself:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\ MEM h (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  dominates (dom_analyze (cfg_analyze fn) fn) h a /\
  lookup_block h fn.fn_blocks = SOME bb /\
  (?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) ==>
  current_chain_token fn ins v (REVERSE ps ++ [a]) t <> CurrentInserted w h
Proof
  strip_tac >>
  `MEM h (a::ps)` by
    (Cases_on `h = a` >> simp[] >>
     metis_tac[current_actual_chain_membership, strict_dominates_def]) >>
  drule_all current_token_chain_member_suffix >> strip_tac >>
  `ALL_DISTINCT (a::ps)` by
    metis_tac[current_actual_chain_distinct] >>
  `~MEM h pre` by
    (qpat_x_assum `ALL_DISTINCT (a::ps)` mp_tac >>
     qpat_assum `a::ps = _` (fn th => rewrite_tac[th]) >>
     simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `REVERSE ps ++ [a] = REVERSE ds ++ h::REVERSE pre` by
    metis_tac[REVERSE_APPEND, REVERSE_DEF, APPEND_ASSOC, APPEND] >>
  qpat_x_assum `REVERSE ps ++ [a] = _` (fn th => once_rewrite_tac[th]) >>
  rewrite_tac[current_chain_token_append, current_chain_token_def] >>
  irule current_nondeg_chain_preserves_noninserted >> simp[] >>
  simp[current_block_token_def] >>
  irule current_nondeg_original_resets_inserted >> metis_tac[]
QED

Theorem current_nondeg_dominated_exit_nonself:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\ MEM d (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  dominates (dom_analyze (cfg_analyze fn) fn) d a /\
  current_changing_site fn ins v d /\
  ~dominates (dom_analyze (cfg_analyze fn) fn) d h ==>
  current_chain_token fn ins v (REVERSE ps ++ [a]) t <> CurrentInserted w h
Proof
  strip_tac >> drule_all current_nondeg_actual_exit_source >>
  disch_then (qspec_then `t` strip_assume_tac) >>
  spose_not_then assume_tac >> gvs[current_nondeg_token_at_def]
QED

Theorem current_nondeg_outside_exit_nonself:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM b (fn_labels fn) /\ MEM h (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  ~dominates (dom_analyze (cfg_analyze fn) fn) h b ==>
  current_chain_token fn ins v (REVERSE qs ++ [b]) (CurrentDefault v) <>
    CurrentInserted w h
Proof
  strip_tac >> irule current_nondeg_chain_preserves_noninserted >> simp[] >>
  Cases_on `h = b` >- metis_tac[dom_self] >>
  metis_tac[current_actual_chain_membership, strict_dominates_def]
QED
