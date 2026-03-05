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
 *)

Theory dfHelperProps
Ancestors
  dfHelperProofs

(* Set of list_intersect is the set intersection. *)
Theorem list_intersect_set:
  !xs ys. set (list_intersect xs ys) = set xs INTER set ys
Proof
  ACCEPT_TAC list_intersect_set_proof
QED

(* Membership in list_intersect iff member of both lists. *)
Theorem list_intersect_mem:
  !v xs ys. MEM v (list_intersect xs ys) <=> MEM v xs /\ MEM v ys
Proof
  ACCEPT_TAC list_intersect_mem_proof
QED

(* For nonempty input, iterated intersection equals BIGINTER of the sets. *)
Theorem list_intersect_all_set:
  !ls. ls <> [] ==>
    set (list_intersect_all ls) = BIGINTER (IMAGE set (set ls))
Proof
  ACCEPT_TAC list_intersect_all_set_proof
QED

(* Iterated intersection is a subset of the first list. *)
Theorem list_intersect_all_mono:
  !l ls. set (list_intersect_all (l :: ls)) SUBSET set l
Proof
  ACCEPT_TAC list_intersect_all_mono_proof
QED
