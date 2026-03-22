(*
 * Memory Location — Proofs
 *
 * Algebraic properties of may_overlap and completely_contains.
 *
 * TOP-LEVEL:
 *   may_overlap_sym_proof             — may_overlap is symmetric
 *   completely_contains_trans_proof   — completely_contains is transitive
 *   contains_implies_overlap_proof    — containment implies overlap
 *)

Theory memLocProofs
Ancestors
  memLocDefs
Libs
  finite_mapTheory

Theorem may_overlap_sym_proof:
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

Theorem completely_contains_trans_proof:
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

Theorem contains_implies_overlap_proof:
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
