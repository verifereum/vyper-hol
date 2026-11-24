(* Lift singleton full-body cases through the dispatcher's arity guard. *)
Theory bodyFullUnaryBuiltin
Ancestors
  bodyFullPreds exprSimHypsDefs vyperTypeBuiltins vyperTypeSystem vyperAST list

Theorem unary_builtin_expr_full_ok:
  !cx ann bt es.
    (!m. builtin_args_length_ok bt m ==> m = 1) /\
    (!e. body_expr_full_ok cx e ==> body_expr_full_ok cx (Builtin ann bt [e])) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ann bt es)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (`LENGTH es = 1` by metis_tac[] >>
      fs[LENGTH_EQ_1] >>
      qpat_x_assum `!e. body_expr_full_ok _ e ==> _` irule >>
      fs[body_exprs_full_ok_def]) >>
  once_rewrite_tac[body_expr_full_ok_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[expr_body_pre_def, cj 9 well_typed_expr_def] >>
      drule well_typed_builtin_app_length >> simp[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
