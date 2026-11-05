Theory o1MakeSsaActualMaps
Ancestors
  makeSsaCurrentDefs cfgAnalysisProps dominatorDefs cfgDefs venomWf
  venomInst list alist finite_map

(* Adapted from the admitted-free reference TraceCertificate boundary;
   it needs no all_reachable hypothesis. *)
Theorem actual_query_map_domain:
  !labels query p ss.
  ALOOKUP (current_query_map labels query) p = SOME ss ==> MEM p labels
Proof
  Induct >> simp[current_query_map_def] >> rpt gen_tac >>
  Cases_on `h = p` >> fs[current_query_map_def] >> metis_tac[]
QED

Theorem actual_succ_map_distinct:
  wf_function fn /\ ALOOKUP (current_succ_map fn) p = SOME ss ==>
  ALL_DISTINCT ss
Proof
  strip_tac >>
  `MEM p (fn_labels fn)` by
    (fs[current_succ_map_def] >> metis_tac[actual_query_map_domain]) >>
  `?b. MEM b fn.fn_blocks /\ b.bb_label = p` by
    (fs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `ss = bb_succs b` by
    metis_tac[ALOOKUP_current_succ_map, cfg_analyze_preserves_bb_succs,
      optionTheory.SOME_11] >>
  simp[bb_succs_def] >> Cases_on `b.bb_instructions` >> simp[all_distinct_nub]
QED

(* General accumulator version of the local dominatorProofs boundary. *)
Theorem actual_children_fold_mem:
  !labels (idom:'a |-> 'b) (m:'b |-> 'a list) n c.
    MEM c (fmap_lookup_list (FOLDL (\m lbl.
      case FLOOKUP idom lbl of NONE => m
      | SOME parent => m |+ (parent,
          set_insert lbl (fmap_lookup_list m parent))) m labels) n) <=>
    MEM c (fmap_lookup_list m n) \/
    (MEM c labels /\ FLOOKUP idom c = SOME n)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP idom h` >>
  simp[fmap_lookup_list_def, FLOOKUP_UPDATE, set_insert_def] >>
  Cases_on `c = h` >> gvs[] >>
  rpt IF_CASES_TAC >> gvs[fmap_lookup_list_def]
QED

Theorem actual_children_mem:
  MEM c (fmap_lookup_list (compute_dominated idom labels) p) <=>
    MEM c labels /\ FLOOKUP idom c = SOME p
Proof
  simp[compute_dominated_def] >>
  once_rewrite_tac[actual_children_fold_mem] >>
  simp[fmap_lookup_list_def, FLOOKUP_DEF]
QED

Theorem actual_children_fold_distinct:
  !labels idom m.
  (!p. ALL_DISTINCT (fmap_lookup_list m p)) ==>
  !p. ALL_DISTINCT (fmap_lookup_list
    (FOLDL (\m lbl. case FLOOKUP idom lbl of NONE => m
      | SOME parent => m |+ (parent,set_insert lbl (fmap_lookup_list m parent)))
      m labels) p)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP idom h` >> simp[] >>
  first_x_assum irule >> gen_tac >>
  simp[fmap_lookup_list_def, FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> simp[] >>
  fs[fmap_lookup_list_def, set_insert_def] >> IF_CASES_TAC >> simp[]
QED

Theorem actual_children_distinct:
  ALL_DISTINCT (fmap_lookup_list (compute_dominated idom labels) p)
Proof
  simp[compute_dominated_def] >> irule actual_children_fold_distinct >>
  simp[fmap_lookup_list_def, FLOOKUP_DEF]
QED

Theorem actual_dom_children:
  MEM c (dominated_of (dom_analyze (cfg_analyze fn) fn) p) <=>
    MEM c (fn_labels fn) /\
    idom_of (dom_analyze (cfg_analyze fn) fn) c = SOME p
Proof
  simp[dominated_of_def, idom_of_def, dom_analyze_def, actual_children_mem]
QED

Theorem actual_dom_children_distinct:
  ALL_DISTINCT (dominated_of (dom_analyze (cfg_analyze fn) fn) p)
Proof
  simp[dominated_of_def, dom_analyze_def, actual_children_distinct]
QED
