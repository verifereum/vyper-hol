(* Reused structural assignability of a narrower source layout. *)
Theory bodyMemAssignPlaceSourceTypes
Ancestors
  vyperTypeArgFits vyperTypeSystem vyperTypeValues vyperAST compileEnv list

Theorem arg_type_fits_source_assignable:
  (!t u. arg_type_fits t u ==>
    !tenv. assignable_type tenv u /\ well_formed_type tenv t ==>
      assignable_type tenv t) /\
  (!ts us. arg_types_fit ts us ==>
    !tenv. EVERY (assignable_type tenv) us /\ EVERY (well_formed_type tenv) ts ==>
      EVERY (assignable_type tenv) ts)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  gvs[assignable_type_def] >>
  all_tac
  >>~- ([`assignable_type tenv t`],
     first_x_assum irule >> simp[] >>
     gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
     drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >>
     metis_tac[]) >>
  `EVERY (well_formed_type tenv) ts` by
    (gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
     drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >>
     gvs[listTheory.EVERY_MEM, listTheory.LIST_REL_EL_EQN,
         listTheory.MEM_EL] >>
     metis_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  metis_tac[arg_types_fit_LENGTH, listTheory.LENGTH_NIL]
QED

