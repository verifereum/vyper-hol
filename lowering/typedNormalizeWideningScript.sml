(* Legal constructor transitions for recursive normalization. *)
Theory typedNormalizeWidening
Ancestors
  vyperTypeSystem vyperTypeArgFits list arithmetic

Theorem arg_type_fits_fixed_array:
  arg_type_fits (ArrayT s (Fixed n)) (ArrayT d (Fixed m)) ==>
  n = m /\ arg_type_fits s d
Proof
  simp[arg_type_fits_def]
QED

Theorem arg_type_fits_dynamic_array:
  arg_type_fits (ArrayT s (Dynamic n)) (ArrayT d (Dynamic m)) ==>
  n <= m /\ arg_type_fits s d
Proof
  simp[arg_type_fits_def]
QED

Theorem arg_types_fit_EL:
  !ss ds i. arg_types_fit ss ds /\ i < LENGTH ss ==>
    arg_type_fits (EL i ss) (EL i ds)
Proof
  Induct >> Cases_on `ds` >> simp[arg_type_fits_def] >>
  rpt gen_tac >> Cases_on `i` >> simp[arg_type_fits_def]
QED

Theorem arg_type_fits_tuple_length:
  arg_type_fits (TupleT ss) (TupleT ds) ==> LENGTH ss = LENGTH ds
Proof
  simp[arg_type_fits_def, arg_types_fit_LENGTH]
QED

Theorem type_widens_to_struct:
  type_widens_to tenv s (StructT nsid) ==> s = StructT nsid
Proof
  Cases_on `s` >> simp[type_widens_to_def, arg_type_fits_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem type_widens_to_fixed_array:
  type_widens_to tenv (ArrayT s (Fixed n)) (ArrayT d (Fixed m)) ==>
  n = m /\ type_widens_to tenv s d
Proof
  rw[type_widens_to_def, arg_type_fits_def] >> simp[] >>
  gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
  strip_tac >> simp[well_formed_type_def]
QED

Theorem type_widens_to_dynamic_array:
  type_widens_to tenv (ArrayT s (Dynamic n)) (ArrayT d (Dynamic m)) ==>
  n <= m /\ type_widens_to tenv s d
Proof
  rw[type_widens_to_def, arg_type_fits_def] >> simp[] >>
  gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
  strip_tac >> simp[well_formed_type_def]
QED

Theorem type_widens_to_tuple_length:
  type_widens_to tenv (TupleT ss) (TupleT ds) ==>
  LENGTH ss = LENGTH ds
Proof
  rw[type_widens_to_def] >> gvs[] >>
  drule arg_type_fits_tuple_length >> simp[]
QED

Theorem type_widens_to_tuple_EL:
  type_widens_to tenv (TupleT ss) (TupleT ds) /\ i < LENGTH ss ==>
  type_widens_to tenv (EL i ss) (EL i ds)
Proof
  rw[type_widens_to_def] >> gvs[] >>
  `arg_types_fit ss ds` by fs[arg_type_fits_def] >>
  `arg_type_fits (EL i ss) (EL i ds)` by metis_tac[arg_types_fit_EL] >>
  simp[] >>
  gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >>
  gvs[listTheory.LIST_REL_EL_EQN] >>
  `i < LENGTH ds` by metis_tac[arg_types_fit_LENGTH] >>
  disj2_tac >> qexists_tac `EL i tvs` >>
  first_x_assum irule >> decide_tac
QED
