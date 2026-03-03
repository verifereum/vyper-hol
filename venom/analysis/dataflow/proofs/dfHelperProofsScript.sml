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

Theorem fmap_lookup_default_found_proof:
  !d f k v. FLOOKUP f k = SOME v ==> fmap_lookup_default d f k = v
Proof
  cheat
QED

Theorem fmap_lookup_default_missing_proof:
  !d f k. FLOOKUP f k = NONE ==> fmap_lookup_default d f k = d
Proof
  cheat
QED
