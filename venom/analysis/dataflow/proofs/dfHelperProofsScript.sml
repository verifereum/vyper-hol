(*
 * Dataflow Shared Helpers — Proofs
 *)

Theory dfHelperProofs
Ancestors
  dfHelperDefs pred_set list

Theorem list_intersect_set_proof:
  !xs ys. set (list_intersect xs ys) = set xs INTER set ys
Proof
  cheat
QED

Theorem list_intersect_mem_proof:
  !v xs ys. MEM v (list_intersect xs ys) <=> MEM v xs /\ MEM v ys
Proof
  cheat
QED

Theorem list_intersect_all_set_proof:
  !ls. ls <> [] ==>
    set (list_intersect_all ls) = BIGINTER (IMAGE set (set ls))
Proof
  cheat
QED

Theorem list_intersect_all_mono_proof:
  !l ls. set (list_intersect_all (l :: ls)) SUBSET set l
Proof
  cheat
QED

(* list_union: membership iff member of either list *)
Theorem list_union_mem_proof:
  !v xs ys. MEM v (list_union xs ys) <=> MEM v xs \/ MEM v ys
Proof
  rw[list_union_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

(* list_union: set semantics *)
Theorem list_union_set_proof:
  !xs ys. set (list_union xs ys) = set xs UNION set ys
Proof
  rw[list_union_def, LIST_TO_SET_APPEND, LIST_TO_SET_FILTER, EXTENSION] >>
  rw[MEM_FILTER] >> metis_tac[]
QED
