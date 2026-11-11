(* Finite-tree distinctness slice from the proved MakeSSA reference. *)
Theory makeSsaRfDomDistinct
Ancestors dominatorQueryProofs dominatorRankProofs makeSsaCurrentAnalysis makeSsaCurrentTree makeSsaCurrentTreeTrace
  makeSsaDefs makeSsaCurrentInduct
  dominatorDefs relation list sorting combin cfgAnalysisProps cfgHelpers
  dominatorProofs venomWf cfgWf cfgDefs venomInst venomExecProps






















Theorem rf_current_actual_tree_labels_distinct:
  wf_function fn /\ all_reachable fn ==>
  ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))
Proof
  strip_tac >> Cases_on `fn_entry_label fn`
  >- simp[current_dom_tree_def, dom_tree_labels_def] >>
  `MEM x (fn_labels fn)` by
    (gvs[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
     Cases_on `fn.fn_blocks` >> gvs[fn_labels_def]) >>
  simp[current_dom_tree_def, current_tree_labels_postorder] >>
  irule current_tree_postorder_distinct >>
  qexistsl [`fn_labels fn`, `dominator_query_rank fn`] >> simp[] >>
  conj_tac
  >- (simp[current_tree_edge_def, dominated_query_membership] >> rpt strip_tac >> gvs[]) >>
  conj_tac >- metis_tac[current_dom_child_rank] >>
  simp[dominated_query_distinct]
QED
