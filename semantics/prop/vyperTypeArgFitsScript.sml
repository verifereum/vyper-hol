(*
 * A value whose type fits a wider declared type (arg_type_fits: an external
 * call argument; type_widens_to: implicit bound widening in the checker) also
 * has the declared type, and an assignment target the checker accepts is a
 * well-typed target.
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

(* ===== Implicit bound widening (type_widens_to) ===== *)

Theorem type_widens_to_refl[simp]:
  type_widens_to tenv t t
Proof
  simp[type_widens_to_def]
QED

(* KEY LEMMA: a value of type t also has the wider declared type u. *)
Theorem type_widens_to_value_has_type:
  type_widens_to tenv t u /\ evaluate_type tenv t = SOME tv /\
  value_has_type tv v ==>
  ?tu. evaluate_type tenv u = SOME tu /\ value_has_type tu v
Proof
  rw[type_widens_to_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  gvs[] >> metis_tac[arg_type_fits_value_has_type]
QED

Theorem type_widens_to_values_have_types:
  !ts us tvs vs.
    LIST_REL (type_widens_to tenv) ts us /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
    LIST_REL value_has_type tvs vs ==>
    ?tus. LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us tus /\
          LIST_REL value_has_type tus vs
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[LIST_REL_CONS1] >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `tu::tus` >> simp[]
QED

Theorem type_widens_to_NoneT[simp]:
  type_widens_to tenv NoneT u <=> u = NoneT
Proof
  Cases_on `u` >> rw[type_widens_to_def, arg_type_fits_def]
QED

Theorem type_widens_to_not_NoneT:
  type_widens_to tenv t u /\ u <> NoneT ==> t <> NoneT
Proof
  rpt strip_tac >> gvs[]
QED

Theorem well_formed_type_ArrayT_elem[local]:
  well_formed_type tenv (ArrayT t bd) ==> well_formed_type tenv t
Proof
  rw[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_ArrayT_cases >> rw[] >> simp[]
QED

Theorem well_formed_type_TupleT_EVERY[local]:
  well_formed_type tenv (TupleT ts) ==> EVERY (well_formed_type tenv) ts
Proof
  rw[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> rw[] >>
  rw[EVERY_MEM, MEM_EL, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  gvs[LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem arg_type_fits_assignable_type[local]:
  (!t u. arg_type_fits t u ==>
     !tenv. assignable_type tenv t /\ well_formed_type tenv u ==>
            assignable_type tenv u) /\
  (!ts us. arg_types_fit ts us ==>
     !tenv. EVERY (assignable_type tenv) ts /\ EVERY (well_formed_type tenv) us ==>
            EVERY (assignable_type tenv) us)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  gvs[assignable_type_def] >>
  metis_tac[well_formed_type_ArrayT_elem, well_formed_type_TupleT_EVERY]
QED

Theorem type_widens_to_assignable_type:
  type_widens_to tenv t u /\ assignable_type tenv t ==> assignable_type tenv u
Proof
  rw[type_widens_to_def] >> metis_tac[arg_type_fits_assignable_type]
QED

Theorem atarget_accepts_well_typed_atarget:
  atarget_accepts env tgt t /\ assignable_type env.type_defs t ==>
  ?ty. well_typed_atarget env tgt ty /\ type_widens_to env.type_defs t ty /\
       assignable_type env.type_defs ty
Proof
  Cases_on `tgt` >> rw[atarget_accepts_def]
  >- (Cases_on `type_place_target env b` >> gvs[] >>
      rename1 `type_place_target env b = SOME pt` >> Cases_on `pt` >> gvs[] >>
      rename1 `type_place_target env b = SOME (Type tty)` >>
      qexists_tac `tty` >>
      simp[well_typed_atarget_def, well_typed_target_def] >>
      metis_tac[type_widens_to_assignable_type]) >>
  qexists_tac `t` >> simp[]
QED
