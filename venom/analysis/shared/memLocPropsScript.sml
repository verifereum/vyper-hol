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
  memLocDefs
Libs
  finite_mapTheory

(* ===== may_overlap ===== *)

Theorem may_overlap_sym:
  ∀m1 m2. may_overlap m1 m2 ⇔ may_overlap m2 m1
Proof
  rw[may_overlap_def] >>
  Cases_on `m1.ml_size = SOME 0` >> simp[] >>
  Cases_on `m2.ml_size = SOME 0` >> simp[] >>
  Cases_on `IS_SOME m1.ml_alloca` >>
  Cases_on `IS_SOME m2.ml_alloca` >> simp[] >>
  Cases_on `m1.ml_alloca = m2.ml_alloca` >> simp[] >>
  Cases_on `m1.ml_offset` >> simp[] >>
  Cases_on `m2.ml_offset` >> simp[] >>
  Cases_on `m1.ml_size` >> Cases_on `m2.ml_size` >> simp[] >>
  rw[LET_THM] >> DECIDE_TAC
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
  rw[completely_contains_def] >>
  Cases_on `m3.ml_size = SOME 0` >> gvs[] >>
  Cases_on `m2.ml_size = SOME 0` >> gvs[] >>
  Cases_on `m1.ml_offset` >> Cases_on `m1.ml_size` >>
  Cases_on `m2.ml_offset` >> Cases_on `m2.ml_size` >>
  Cases_on `m3.ml_offset` >> Cases_on `m3.ml_size` >>
  gvs[]
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
  rw[completely_contains_def, may_overlap_def] >>
  Cases_on `m1.ml_offset` >> Cases_on `m1.ml_size` >>
  Cases_on `m2.ml_offset` >> Cases_on `m2.ml_size` >>
  Cases_on `m1.ml_alloca` >> Cases_on `m2.ml_alloca` >>
  gvs[LET_THM]
QED

