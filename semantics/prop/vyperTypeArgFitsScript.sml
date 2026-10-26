(*
 * A value of an external-call argument whose type fits the declared
 * parameter type (arg_type_fits) also has the declared type.
 *)

Theory vyperTypeArgFits
Ancestors
  list vyperValue vyperTyping vyperTypeSystem vyperTypeValues

Theorem arg_type_fits_default_value:
  (!t u tv tu.
     arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
     evaluate_type tenv u = SOME tu ==>
     default_value tv = default_value tu) /\
  (!ts us tvs tus.
     arg_types_fit ts us /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us tus ==>
     MAP default_value tvs = MAP default_value tus)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def, default_value_def, default_value_tuple_MAP] >>
  metis_tac[]
QED

Theorem sparse_has_type_mono[local]:
  (!v. value_has_type tv v ==> value_has_type tu v) /\
  default_value tv = default_value tu ==>
  !sp. sparse_has_type tv n sp ==> sparse_has_type tu n sp
Proof
  strip_tac >> Induct >> simp[value_has_type_def] >>
  Cases >> simp[value_has_type_def]
QED

Theorem arg_type_fits_value_has_type:
  (!t u tv tu v.
     arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
     evaluate_type tenv u = SOME tu /\ value_has_type tv v ==>
     value_has_type tu v) /\
  (!ts us tvs tus vs.
     arg_types_fit ts us /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us tus /\
     values_have_types tvs vs ==>
     values_have_types tus vs)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def]
  >~ [`values_have_types (_::_) _`]
  >- (Cases_on `vs` >> fs[value_has_type_def] >> metis_tac[])
  >~ [`value_has_type (TupleTV _) _`]
  >- (Cases_on `v` >> fs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> fs[value_has_type_def] >>
      metis_tac[])
  >~ [`value_has_type (ArrayTV _ (Fixed _)) _`]
  >- (Cases_on `v` >> fs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> fs[value_has_type_def] >>
      metis_tac[sparse_has_type_mono, arg_type_fits_default_value])
  >~ [`value_has_type (ArrayTV _ (Dynamic _)) _`]
  >- (Cases_on `v` >> fs[value_has_type_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> fs[value_has_type_def] >>
      fs[all_have_type_EVERY, EVERY_MEM])
  >> Cases_on `v` >> fs[value_has_type_def]
QED

Theorem arg_types_fit_LENGTH:
  !ts us. arg_types_fit ts us ==> LENGTH ts = LENGTH us
Proof
  Induct >> Cases_on `us` >> simp[arg_type_fits_def]
QED

Theorem well_formed_types_evaluate:
  !ts. EVERY (well_formed_type tenv) ts ==>
       ?tvs. LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs
Proof
  Induct >> rw[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  gvs[well_formed_type_def] >> simp[LIST_REL_CONS1] >> metis_tac[]
QED

(* The operand types of an external call, split as its typing rule does. *)
Theorem MAP_HD_TAKE_DROP:
  0 < LENGTH xs ==>
  MAP f xs = f (HD xs) :: MAP f (TAKE n (TL xs)) ++ MAP f (DROP (1 + n) xs)
Proof
  Cases_on `xs` >> simp[DROP_def] >>
  REWRITE_TAC[GSYM MAP_APPEND, TAKE_DROP]
QED
