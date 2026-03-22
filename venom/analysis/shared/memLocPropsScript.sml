(*
 * Memory Location Properties
 *
 * Algebraic properties of may_overlap and completely_contains.
 * Used by mem_alias, load_elimination, dead_store_elimination.
 *
 * TOP-LEVEL:
 *   may_overlap_sym, may_overlap_comm,
 *   different_alloca_no_overlap,
 *   empty_no_overlap_l, empty_no_overlap_r,
 *   empty_contained,
 *   completely_contains_trans, completely_contains_refl,
 *   contains_implies_overlap
 *)

Theory memLocProps
Ancestors
  memLocDefs memLocProofs
Libs
  finite_mapTheory

(* ===== may_overlap ===== *)

Theorem may_overlap_sym:
  ∀m1 m2. may_overlap m1 m2 ⇔ may_overlap m2 m1
Proof
  ACCEPT_TAC memLocProofsTheory.may_overlap_sym_proof
QED

Theorem may_overlap_comm:
  ∀m1 m2. may_overlap m1 m2 = may_overlap m2 m1
Proof
  metis_tac[may_overlap_sym]
QED

Theorem empty_no_overlap_l:
  ∀m. ¬may_overlap ml_empty m
Proof
  rw[may_overlap_def, ml_empty_def]
QED

Theorem empty_no_overlap_r:
  ∀m. ¬may_overlap m ml_empty
Proof
  rw[may_overlap_def, ml_empty_def]
QED

(* Locations with different allocations never overlap. *)
Theorem different_alloca_no_overlap:
  ∀m1 m2 a1 a2.
    m1.ml_alloca = SOME a1 ∧ m2.ml_alloca = SOME a2 ∧ a1 ≠ a2 ⇒
    ¬may_overlap m1 m2
Proof
  rw[may_overlap_def]
QED

(* ===== completely_contains ===== *)

Theorem empty_contained:
  ∀outer. completely_contains outer ml_empty
Proof
  rw[completely_contains_def, ml_empty_def]
QED

(* completely_contains is transitive. *)
Theorem completely_contains_trans:
  ∀m1 m2 m3.
    completely_contains m1 m2 ∧ completely_contains m2 m3 ⇒
    completely_contains m1 m3
Proof
  ACCEPT_TAC memLocProofsTheory.completely_contains_trans_proof
QED

(* Reflexive when offset and size are both known. *)
Theorem completely_contains_refl:
  ∀m. IS_SOME m.ml_offset ∧ IS_SOME m.ml_size ⇒
    completely_contains m m
Proof
  rw[completely_contains_def]
QED

(* Containment of a non-empty region implies overlap. *)
Theorem contains_implies_overlap:
  ∀m1 m2.
    completely_contains m1 m2 ∧ m2.ml_size ≠ SOME 0 ⇒
    may_overlap m1 m2
Proof
  ACCEPT_TAC memLocProofsTheory.contains_implies_overlap_proof
QED

