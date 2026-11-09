(* Finite-fuel interfaces for supported place types. *)
Theory bodyIntCallFamAggAttributeSupport
Ancestors
  supportedTypes vyperAST list arithmetic pred_set

Theorem supported_nested_type_mono:
  !leaf m tops ty.
    !n. m <= n /\ supported_nested_type leaf m tops ty ==>
      supported_nested_type leaf n tops ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  Cases_on `ty` >> once_rewrite_tac[supported_nested_type_def] >>
  simp[NoAsms, EVERY_MEM] >> rpt strip_tac >>
  gvs[AllCaseEqs(), EVERY_MEM]
  >~ [`ArrayT elem bound`] >- (Cases_on `bound` >> gvs[])
  >> Cases_on `supported_struct_fields tops p` >> gvs[] >>
  `fuel <= (n - 1) + 1` by decide_tac >> metis_tac[]
QED

Theorem supported_nested_type_struct_agree:
  !leaf m n tops.
    (!id. supported_nested_type leaf m tops (StructT id) <=>
          supported_nested_type leaf n tops (StructT id)) ==>
    !ty. supported_nested_type leaf m tops ty <=>
         supported_nested_type leaf n tops ty
Proof
  rpt gen_tac >> strip_tac >> Induct using type_induction >> rpt gen_tac
  >~ [`StructT id`] >- simp[]
  >> once_rewrite_tac[supported_nested_type_def] >>
  simp[NoAsms, EVERY_MEM]
  >~ [`ArrayT elem bound`] >- (Cases_on `bound` >> simp[])
  >> simp[]
QED

Theorem supported_nested_type_agree_suc:
  (!ty. supported_nested_type leaf m tops ty <=>
        supported_nested_type leaf n tops ty) ==>
  !ty. supported_nested_type leaf (SUC m) tops ty <=>
       supported_nested_type leaf (SUC n) tops ty
Proof
  strip_tac >> irule supported_nested_type_struct_agree >> gen_tac >>
  once_rewrite_tac[supported_nested_type_def] >>
  simp[EVERY_MEM]
QED

Theorem supported_nested_type_stable:
  (!ty. supported_nested_type leaf n tops ty <=>
        supported_nested_type leaf (SUC n) tops ty) ==>
  !k ty. supported_nested_type leaf (n + k) tops ty <=>
         supported_nested_type leaf n tops ty
Proof
  strip_tac >> Induct >> simp[] >>
  drule supported_nested_type_agree_suc >> simp[ADD_CLAUSES]
QED
