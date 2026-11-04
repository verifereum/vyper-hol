Theory concretizePtrActivationSupport
Ancestors concretizePtrRootCover concretizePtrFrameOrigins concretizePtrClosure
  concretizePtrRuntimeOrigins pointerClosure pointerConfinedDefs
  ptrDiscipline venomInst finite_map pred_set list

Theorem ptr_frame_roots_extend:
  (!aid p. FLOOKUP A aid = SOME p ==> FLOOKUP B aid = SOME p) ==>
  ptr_frame_site_roots fn A PG site SUBSET ptr_frame_site_roots fn B PG site
Proof
  simp[SUBSET_DEF, ptr_frame_site_roots_def] >> metis_tac[]
QED

Theorem ptr_frame_support_extend:
  (!aid p. FLOOKUP A aid = SOME p ==> FLOOKUP B aid = SOME p) /\
  ptr_site_supported (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site ==>
  ptr_site_supported (pointer_derived_vars fn (ptr_frame_site_roots fn B PG site)) G site
Proof
  strip_tac >>
  `pointer_derived_vars fn (ptr_frame_site_roots fn A PG site) SUBSET
   pointer_derived_vars fn (ptr_frame_site_roots fn B PG site)` by
    (irule ptr_derived_mono >> simp[ptr_frame_site_roots_finite] >>
     metis_tac[ptr_frame_roots_extend]) >>
  fs[ptr_site_supported_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_site_support_restrict:
  ptr_site_supported X G site ==> ptr_site_supported X (DRESTRICT G keys) site
Proof
  simp[ptr_site_supported_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED
