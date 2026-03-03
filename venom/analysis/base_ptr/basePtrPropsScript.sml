(*
 * Base Pointer Analysis — Properties
 *
 * Safety properties for mem_loc predicates and base pointer analysis.
 *
 * TOP-LEVEL:
 *   may_overlap_sym, may_overlap_comm,
 *   completely_contains_trans,
 *   different_alloca_no_overlap,
 *   empty_no_overlap, empty_contained,
 *   contains_implies_overlap,
 *   bp_alloca_singleton, bp_get_ptrs_update_same/diff,
 *   bp_handle_inst_other_var, bp_handle_inst_no_output_unchanged
 *)

Theory basePtrProps
Ancestors
  basePtrDefs memLocDefs venomInst venomEffects
Libs
  finite_mapTheory pred_setTheory

(* ===== may_overlap properties ===== *)

(* may_overlap is symmetric *)
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

(* Empty locations never overlap *)
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

(* Different allocations never overlap *)
Theorem different_alloca_no_overlap:
  ∀m1 m2 a1 a2.
    m1.ml_alloca = SOME a1 ∧ m2.ml_alloca = SOME a2 ∧ a1 ≠ a2 ⇒
    ¬may_overlap m1 m2
Proof
  rw[may_overlap_def]
QED

(* ===== completely_contains properties ===== *)

Theorem empty_contained:
  ∀outer. completely_contains outer ml_empty
Proof
  rw[completely_contains_def, ml_empty_def]
QED

Theorem completely_contains_trans:
  ∀m1 m2 m3.
    completely_contains m1 m2 ∧ completely_contains m2 m3 ⇒
    completely_contains m1 m3
Proof
  rw[completely_contains_def] >> gvs[] >>
  Cases_on `m3.ml_size = SOME 0` >> gvs[] >>
  Cases_on `m2.ml_size = SOME 0` >> gvs[] >>
  Cases_on `m1.ml_offset` >> Cases_on `m1.ml_size` >>
  Cases_on `m2.ml_offset` >> Cases_on `m2.ml_size` >>
  Cases_on `m3.ml_offset` >> Cases_on `m3.ml_size` >>
  gvs[] >> DECIDE_TAC
QED

Theorem contains_implies_overlap:
  ∀m1 m2.
    completely_contains m1 m2 ∧ m2.ml_size ≠ SOME 0 ⇒
    may_overlap m1 m2
Proof
  rw[completely_contains_def, may_overlap_def] >>
  Cases_on `m1.ml_offset` >> Cases_on `m1.ml_size` >>
  Cases_on `m2.ml_offset` >> Cases_on `m2.ml_size` >>
  Cases_on `m1.ml_alloca` >> Cases_on `m2.ml_alloca` >>
  gvs[] >> rw[LET_THM] >> DECIDE_TAC
QED

Theorem completely_contains_refl:
  ∀m. IS_SOME m.ml_offset ∧ IS_SOME m.ml_size ⇒
    completely_contains m m
Proof
  rw[completely_contains_def]
QED

(* ===== Base pointer analysis properties ===== *)

Theorem bp_alloca_singleton:
  ∀result inst out.
    inst_output inst = SOME out ∧
    inst.inst_opcode ∈ {ALLOCA; PALLOCA} ⇒
    bp_get_ptrs (result |+ (out, {ptr_from_alloca inst})) out =
      {ptr_from_alloca inst}
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_update_same:
  ∀result k v. bp_get_ptrs (result |+ (k, v)) k = v
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_update_diff:
  ∀result k1 k2 v. k1 ≠ k2 ⇒
    bp_get_ptrs (result |+ (k1, v)) k2 = bp_get_ptrs result k2
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_fempty:
  ∀v. bp_get_ptrs FEMPTY v = {}
Proof
  rw[bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* bp_handle_inst preserves pointers for non-output variables *)
Theorem bp_handle_inst_other_var:
  ∀ctx result inst c r v.
    bp_handle_inst ctx result inst = (c, r) ∧
    inst_output inst ≠ SOME v ⇒
    bp_get_ptrs r v = bp_get_ptrs result v
Proof
  rw[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> gvs[LET_THM] >>
  rename1 `SOME out` >>
  Cases_on `inst.inst_opcode` >> gvs[LET_THM, bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_handle_inst_no_output_unchanged:
  ∀ctx result inst c r.
    bp_handle_inst ctx result inst = (c, r) ∧
    inst_output inst = NONE ⇒
    r = result
Proof
  rw[bp_handle_inst_def] >> gvs[]
QED

