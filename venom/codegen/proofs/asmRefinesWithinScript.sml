(* Composition needs terminal refinement to establish the intermediate
   program's well-formedness before applying its bounded refinement. *)
Theory asmRefinesWithin
Ancestors
  asmSymSemWithin finalizerContract asmSymSem relation

Overload asm_refines_both = ``asm_refines RINTER asm_refines_within``

Theorem sym_run_within_for_sym_step:
  !k ss. sym_run_within P Q p env k ss <=>
    sym_run_within_for (sym_step p env) P Q p k ss
Proof
  Induct >> simp[sym_run_within_def, sym_run_within_for_def] >>
  gen_tac >> Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> simp[]
QED

Theorem sym_run_within_mono:
  ∀k k' ss.
    sym_run_within P Q p env k ss ∧ k ≤ k' ⇒ sym_run_within P Q p env k' ss
Proof
  Induct >> simp[sym_run_within_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `k'` >> gvs[sym_run_within_def] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> gvs[]
QED

Theorem asm_refines_both_refl:
  asm_refines_both p p
Proof
  simp[RINTER, asm_refines_refl, asm_refines_within_def] >>
  strip_tac >> qexists_tac `1` >> simp[]
QED

Theorem asm_refines_both_trans:
  asm_refines_both p q ∧ asm_refines_both q r ⇒ asm_refines_both p r
Proof
  simp[RINTER] >> strip_tac >>
  conj_tac >- metis_tac[asm_refines_trans] >>
  fs[asm_refines_within_def] >> strip_tac >>
  `asm_static_wf q` by fs[asm_refines_def] >>
  gvs[] >>
  qmatch_asmsub_rename_tac `sym_run_within _ _ q _ (ca * _) _` >>
  qmatch_asmsub_rename_tac `sym_run_within _ _ r _ (cb * _) _` >>
  qexists_tac `cb * ca` >> rpt strip_tac >>
  `cb * ca * k = cb * (ca * k)` by simp[] >> pop_assum SUBST1_TAC >>
  metis_tac[]
QED
