(*
 * Dataflow Shared Helpers — Properties (Statements Only)
 *
 * Re-exports from proofs/dfHelperProofsScript.sml via ACCEPT_TAC.
 *
 * TOP-LEVEL:
 *   list_intersect_set      — set (list_intersect xs ys) = set xs ∩ set ys
 *   list_intersect_mem      — MEM characterization
 *   list_intersect_all_set  — set result = BIGINTER ...
 *   list_intersect_all_mono — result ⊆ first element
 *   fmap_lookup_default_found   — SOME case
 *   fmap_lookup_default_missing — NONE case
 *)

Theory dfHelperProps
Ancestors
  dfHelperProofs

Theorem list_intersect_set:
  !xs ys. set (list_intersect xs ys) = set xs INTER set ys
Proof
  ACCEPT_TAC list_intersect_set_proof
QED

Theorem list_intersect_mem:
  !v xs ys. MEM v (list_intersect xs ys) <=> MEM v xs /\ MEM v ys
Proof
  ACCEPT_TAC list_intersect_mem_proof
QED

Theorem list_intersect_all_set:
  !ls. ls <> [] ==>
    set (list_intersect_all ls) = BIGINTER (IMAGE set (set ls))
Proof
  ACCEPT_TAC list_intersect_all_set_proof
QED

Theorem list_intersect_all_mono:
  !l ls. set (list_intersect_all (l :: ls)) SUBSET set l
Proof
  ACCEPT_TAC list_intersect_all_mono_proof
QED

Theorem fmap_lookup_default_found:
  !d f k v. FLOOKUP f k = SOME v ==> fmap_lookup_default d f k = v
Proof
  ACCEPT_TAC fmap_lookup_default_found_proof
QED

Theorem fmap_lookup_default_missing:
  !d f k. FLOOKUP f k = NONE ==> fmap_lookup_default d f k = d
Proof
  ACCEPT_TAC fmap_lookup_default_missing_proof
QED
