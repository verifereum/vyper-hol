Theory makeSsaCurrentPathBridge
Ancestors
  makeSsaCurrentTreePaths makeSsaCurrentTokenGraph dominatorQueryProofs
  makeSsaDefs makeSsaCurrentTokens venomWf venomInst
  list rich_list

Theorem current_tree_aux_path_chain:
  !n x l path qs root.
    (!p c. MEM c (dominated_of dom p) ==> idom_of dom c = SOME p) /\
    current_tree_ancestor_path (current_dom_tree_aux dom n x) l path /\
    current_token_chain dom root qs x ==>
    current_token_chain dom root (REVERSE path ++ qs) l
Proof
  Induct >> rpt gen_tac
  >- (simp[current_dom_tree_aux_def] >>
      once_rewrite_tac[current_tree_ancestor_path_cases] >> simp[] >>
      rpt strip_tac >> gvs[]) >>
  simp[current_dom_tree_aux_def] >>
  once_rewrite_tac[current_tree_ancestor_path_cases] >>
  simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC] >> first_x_assum irule >> simp[] >>
  metis_tac[current_token_chain_parent]
QED

Theorem current_actual_path_chain:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_tree_ancestor_path (current_dom_tree fn) l path ==>
  current_token_chain (dom_analyze (cfg_analyze fn) fn)
    eb.bb_label (REVERSE path) l
Proof
  strip_tac >>
  gvs[current_dom_tree_def, fn_entry_label_def, entry_block_def] >>
  drule_at (Pos (el 2)) current_tree_aux_path_chain >>
  simp[dominated_query_membership, current_token_chain_def] >>
  disch_then (qspecl_then [`[]`, `(HD fn.fn_blocks).bb_label`] mp_tac) >> simp[current_token_chain_def]
QED

Theorem current_actual_path_unique:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_tree_ancestor_path (current_dom_tree fn) l ps /\
  current_tree_ancestor_path (current_dom_tree fn) l qs ==>
  ps = qs
Proof
  strip_tac >>
  `REVERSE ps = REVERSE qs` by
    (irule current_token_chain_unique >>
     metis_tac[current_actual_path_chain, current_token_root_idom]) >>
  metis_tac[REVERSE_REVERSE]
QED

Theorem current_actual_entry_path:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb ==>
  (current_tree_ancestor_path (current_dom_tree fn) eb.bb_label path <=> path = [])
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule_all current_actual_path_chain >>
      simp[current_actual_root_chain] >> metis_tac[REVERSE_REVERSE, REVERSE_DEF]) >>
  strip_tac >> gvs[current_dom_tree_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `LENGTH (fn_labels fn)` >>
  simp[current_dom_tree_aux_def, current_tree_ancestor_path_rules]
QED
