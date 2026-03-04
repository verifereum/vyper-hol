(*
 * Dataflow Shared Helpers — Proofs
 *)

Theory dfHelperProofs
Ancestors
  dfHelperDefs pred_set

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
