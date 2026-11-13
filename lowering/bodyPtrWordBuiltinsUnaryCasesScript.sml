(* Unary family dispatch. Ill-arity forms cannot meet the typed body precondition. *)
Theory bodyPtrWordBuiltinsUnaryCases
Ancestors bodyPtrWordBuiltinsAbsCompose bodyPtrWordBuiltinsNegCompose
  bodyPtrWordBuiltinsNotCompose bodyPtrPreds exprSimHypsDefs vyperTyping
  vyperTypeSystem vyperAST vyperInterpreter vyperContext list

Theorem body_word_unary_bad_arity_ptr_ok:
  (bt = Not \/ bt = Neg \/ bt = Abs) /\ LENGTH es <> 1 ==>
  body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  strip_tac >> gvs[] >> simp[body_expr_ptr_ok_def] >> rpt strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]
QED

Theorem body_word_unary_ptr_ok:
  !cx ty bt es.
    (bt = Not \/ bt = Neg \/ bt = Abs) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_tac >> Cases_on `LENGTH es = 1`
  >- (Cases_on `es` >> gvs[] >>
      gvs[builtin_args_length_ok_def, body_exprs_ptr_ok_def] >>
      metis_tac[body_word_not_singleton_ptr_ok, body_word_neg_singleton_ptr_ok,
                body_word_abs_singleton_ptr_ok]) >>
  irule body_word_unary_bad_arity_ptr_ok >> simp[]
QED
