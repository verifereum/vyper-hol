(* Affine arithmetic at the FMP stage boundary. *)
Theory fmpStageOpSimPureAffine
Ancestors
  fmpStageOpBase fmpStageRel o1LowerDloadRelocationKernel
  ptrStaticDiscipline ptrDiscipline o1PassContract contextCodegenRel
  venomExecSemantics venomState venomInst pointerConfinedDefs
  finite_map list pred_set words

Theorem fmp_value_rel_add[local]:
  fmp_value_rel sm h1 {} x1 y1 /\ fmp_value_rel sm h2 {} x2 y2 /\
  (h1 = NONE \/ h2 = NONE) ==>
  fmp_value_rel sm (case h1 of NONE => h2 | SOME id => h1) {}
    (x1 + x2) (y1 + y2)
Proof
  Cases_on `h1` >> Cases_on `h2` >>
  simp[fmp_value_rel_def] >> rpt strip_tac >>
  imp_res_tac ld_value_agree_clean >> gvs[] >>
  gvs[ld_value_agree_pointer, ld_value_agree_scalar, word_agree_except_def] >>
  qexistsl [`b`,`c`,`z`] >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem fmp_value_rel_sub[local]:
  fmp_value_rel sm h {} x1 y1 /\ fmp_value_rel sm NONE {} x2 y2 ==>
  fmp_value_rel sm h {} (x1 - x2) (y1 - y2)
Proof
  Cases_on `h` >> simp[fmp_value_rel_def] >> rpt strip_tac >>
  imp_res_tac ld_value_agree_clean >> gvs[] >>
  gvs[ld_value_agree_pointer, ld_value_agree_scalar, word_agree_except_def] >>
  qexistsl [`b`,`c`,`z`] >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED
