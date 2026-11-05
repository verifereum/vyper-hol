Theory o1MakeSsaActualMaps
Ancestors
  makeSsaCurrentDefs cfgAnalysisProps dominatorDefs cfgDefs venomWf
  venomInst list alist finite_map dominatorQueryProofs

(* Adapted from the admitted-free reference TraceCertificate boundary;
   it needs no all_reachable hypothesis. *)
(* General accumulator version of the local dominatorProofs boundary. *)
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

Theorem actual_dom_children:
  MEM c (dominated_of (dom_analyze (cfg_analyze fn) fn) p) <=>
    MEM c (fn_labels fn) /\
    idom_of (dom_analyze (cfg_analyze fn) fn) c = SOME p
Proof
  simp[dominated_of_def, idom_of_def, dom_analyze_def, compute_dominated_membership]
QED

Theorem actual_dom_children_distinct:
  ALL_DISTINCT (dominated_of (dom_analyze (cfg_analyze fn) fn) p)
Proof
  simp[dominated_of_def, dom_analyze_def, compute_dominated_distinct]
QED
