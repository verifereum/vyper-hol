(*
 * Expression-result typing definitions shared by statement soundness helper theories.
 *)

Theory vyperTypeExprResult
Ancestors
  list rich_list arithmetic option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeExprSoundness
Libs
  wordsLib

Definition expr_result_typed_def:
  expr_result_typed env e tv <=>
    expr_runtime_typed env e tv /\
    (is_HashMapRef tv ==> ?kt vt. type_place_expr env e = SOME (HashMapT kt vt))
End

Definition place_expr_result_typed_def:
  place_expr_result_typed env tv vt <=>
    case vt of
    | Type ty => ?tyv. evaluate_type env.type_defs ty = SOME tyv /\
                         toplevel_value_typed tv tyv /\ ~is_HashMapRef tv
    | HashMapT kt vt' => ?is_t slot. tv = HashMapRef is_t slot kt vt'
End

Theorem well_typed_expr_not_hashmap_place:
  !e env kt vt.
    well_typed_expr env e ==>
    type_place_expr env e <> SOME (HashMapT kt vt)
Proof
  Induct >>
  rw[well_typed_expr_def, vtype_annotation_ok_def] >>
  gvs[well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
  TRY (PairCases_on `p` >>
       gvs[well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
       NO_TAC) >>
  TRY (Cases_on `expr_type e` >> gvs[subscript_type_ok_def] >>
       Cases_on `vt'` >> gvs[subscript_vtype_def] >>
       Cases_on `t'` >> gvs[subscript_vtype_def] >>
       NO_TAC) >>
  metis_tac[]
QED
