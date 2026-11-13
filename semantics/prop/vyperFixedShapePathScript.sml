(*
 * Paths that cross no dynamic array.  A path that steps only into
 * fixed-size arrays (in bounds) and struct fields reads every well-typed
 * value of its type: no value of the type can make it dead.
 *
 * TOP-LEVEL:
 *   fixed_shape_path_def     — the path steps into no dynamic array
 *   fixed_shape_path_append  — splitting such a path
 *   fixed_shape_path_live    — such a path reads every well-typed value
 *)

Theory vyperFixedShapePath
Ancestors
  vyperPlaceStatePreservation vyperTypeStatePreservation vyperTyping
  vyperValueOperation vyperValue vyperState vyperAST list alist

(* Only the containers the path steps into must have a fixed shape; the
   path may end at a dynamic array. *)
Definition fixed_shape_path_def:
  fixed_shape_path tv [] = T /\
  fixed_shape_path tv (sb::rest) =
    (~(?et n. tv = ArrayTV et (Dynamic n)) /\
     ?et. subscript_type tv sb = SOME et /\ fixed_shape_path et rest)
End

Theorem fixed_shape_path_append:
  !p tv q. fixed_shape_path tv (p ++ q) <=>
    ?pt. subscripts_type tv p = SOME pt /\ fixed_shape_path tv p /\
         fixed_shape_path pt q
Proof
  Induct >> simp[fixed_shape_path_def, subscripts_type_def] >>
  rpt gen_tac >> Cases_on `subscript_type tv h` >>
  simp[fixed_shape_path_def, subscripts_type_def] >> metis_tac[]
QED

Theorem fixed_shape_step_live[local]:
  !tv sb a et. ~(?t n. tv = ArrayTV t (Dynamic n)) /\
    subscript_type tv sb = SOME et /\
    well_formed_type_value tv /\ value_has_type tv a ==>
    ?v. evaluate_subscripts tv a [sb] = INL v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `sb`
  >- (drule subscript_type_value_int_shape >> strip_tac >> gvs[] >>
      Cases_on `tv` >> gvs[subscript_type_def] >>
      Cases_on `a` >> gvs[value_has_type_def] >>
      Cases_on `a'` >> gvs[value_has_type_def]
      >- (imp_res_tac vyperTypingTheory.values_have_types_length >>
          simp[evaluate_subscripts_def, array_index_def, oEL_THM]) >>
      Cases_on `b` >> gvs[value_has_type_def] >>
      simp[evaluate_subscripts_def, array_index_def, bound_length_def,
           AllCaseEqs()] >>
      Cases_on `ALOOKUP l (Num i)` >> simp[]) >>
  Cases_on `tv` >> gvs[subscript_type_def] >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  Cases_on `ALOOKUP l' s`
  >- metis_tac[struct_has_type_alookup_none, optionTheory.NOT_NONE_SOME] >>
  simp[evaluate_subscripts_def]
QED

Theorem fixed_shape_path_live:
  !path tv a. fixed_shape_path tv path /\
    well_formed_type_value tv /\ value_has_type tv a ==>
    ?v. evaluate_subscripts tv a path = INL v
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> simp[fixed_shape_path_def] >> strip_tac >>
  `?v. evaluate_subscripts tv a [h] = INL v` by
    metis_tac[fixed_shape_step_live] >>
  `well_formed_type_value et` by metis_tac[subscript_type_well_formed] >>
  `value_has_type et v` by
    (irule evaluate_subscripts_type >>
     qexistsl [`a`, `[h]`, `tv`] >>
     simp[subscripts_type_def]) >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `a`] mp_tac) >>
  simp[] >> metis_tac[]
QED
