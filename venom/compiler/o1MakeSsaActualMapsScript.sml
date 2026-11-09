Theory o1MakeSsaActualMaps
Ancestors
  makeSsaDefs cfgAnalysisProps dominatorDefs cfgDefs venomWf
  venomInst list alist finite_map dominatorQueryProofs

(* Adapted from the admitted-free reference TraceCertificate boundary;
   it needs no all_reachable hypothesis. *)
(* General accumulator version of the local dominatorProofs boundary. *)
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
