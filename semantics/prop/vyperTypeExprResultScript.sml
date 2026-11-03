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
                         value_result_typed tv tyv /\ ~is_HashMapRef tv
    | HashMapT kt vt' => ?is_t slot. tv = HashMapRef is_t slot kt vt'
End

(* The value of a literal index must agree with its syntax; ordinary result
   typing alone cannot identify the selected component of a heterogeneous tuple. *)
Definition subscript_index_matches_def:
  subscript_index_matches (TupleT _) ie idx =
    (?ity n. ie = Literal ity (IntL n) /\ idx = IntV n) /\
  subscript_index_matches _ _ _ = T
End

Theorem subscript_type_ok_tuple:
  subscript_type_ok (TupleT ts) ie rt <=>
  ?ity n. ie = Literal ity (IntL n) /\ is_int_type ity /\
          0 <= n /\ Num n < LENGTH ts /\ EL (Num n) ts = rt
Proof
  Cases_on `ie` >> simp[subscript_type_ok_def] >>
  CASE_TAC >> simp[]
QED

Theorem well_typed_expr_not_hashmap_place:
  !e env kt vt.
    well_typed_expr env e ==>
    type_place_expr env e <> SOME (HashMapT kt vt)
Proof
  ho_match_mp_tac
    (expr_induction |> Q.SPEC `P` |> Q.SPEC `λ_. T` |> SIMP_RULE (srw_ss()) []) >>
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
