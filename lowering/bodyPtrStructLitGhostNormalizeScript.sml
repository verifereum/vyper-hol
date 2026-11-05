(* Finite-step normalization boundaries for the concrete callee experiment.
   Fresh ALLOCA normalization already lives in allocationPtr and is reused. *)
Theory bodyPtrStructLitGhostNormalize
Ancestors allocationPtr ptrDiscipline finite_map pred_set

Theorem structlit_new_site_bytes_unchanged:
  !s t. t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
    new_site_bytes s t = {}
Proof
  rpt strip_tac >> simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem structlit_new_site_bytes_fresh_update:
  !s t aid b sz.
    t.vs_allocas = s.vs_allocas |+ (aid,(b,sz)) /\
    aid NOTIN FDOM s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
    new_site_bytes s t = {i | b <= i /\ i < b + sz}
Proof
  rpt strip_tac >>
  rw[new_site_bytes_def, EXTENSION, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs(), FLOOKUP_DEF] >>
  eq_tac
  >- (strip_tac >> gvs[]) >>
  strip_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[]
QED
