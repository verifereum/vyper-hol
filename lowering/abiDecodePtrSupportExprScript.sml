(* Support traversal for predicates confined to type-builtin roots. *)
Theory abiDecodePtrSupportExpr
Ancestors
  supportedExprTraverse supportedExprs supportedExprForms vyperAST list

Theorem supported_pure_type_builtin_exclusion[local]:
  (!e. p e ==> ?ann tb target args. e = TypeBuiltin ann tb target args) ==>
  (!tops e.
    (!ann tb target args. supported_type_builtin_form tops ann tb target args ==>
       ~p (TypeBuiltin ann tb target args)) ==>
    supported_pure_expr tops e ==> ~supported_expr_exists p e) /\
  (!tops es.
    (!ann tb target args. supported_type_builtin_form tops ann tb target args ==>
       ~p (TypeBuiltin ann tb target args)) ==>
    supported_pure_exprs tops es ==> ~supported_exprs_exists p es) /\
  (!tops fields.
    (!ann tb target args. supported_type_builtin_form tops ann tb target args ==>
       ~p (TypeBuiltin ann tb target args)) ==>
    supported_pure_fields tops fields ==> ~supported_fields_exists p fields) /\
  (!tops e.
    (!ann tb target args. supported_type_builtin_form tops ann tb target args ==>
       ~p (TypeBuiltin ann tb target args)) ==>
    supported_place_expr tops e ==> ~supported_expr_exists p e)
Proof
  strip_tac >>
  ho_match_mp_tac supported_pure_expr_ind >>
  rw[supported_pure_expr_def, supported_expr_exists_def] >>
  simp[] >> strip_tac >>
  qpat_x_assum `!e. p e ==> ?ann tb target args. _` drule >> simp[] >> metis_tac[]
QED

Theorem supported_effect_type_builtin_exclusion[local]:
  (!e. p e ==> ?ann tb target args. e = TypeBuiltin ann tb target args) ==>
  (!tops e.
    (!ann tb target args. supported_type_builtin_form tops ann tb target args ==>
       ~p (TypeBuiltin ann tb target args)) ==>
    supported_effect_expr tops e ==> ~supported_expr_exists p e) /\
  (!tops e.
    (!ann tb target args. supported_type_builtin_form tops ann tb target args ==>
       ~p (TypeBuiltin ann tb target args)) ==>
    supported_effect_place_expr tops e ==> ~supported_expr_exists p e)
Proof
  strip_tac >>
  drule supported_pure_type_builtin_exclusion >> strip_tac >>
  ho_match_mp_tac supported_effect_expr_ind >>
  rw[supported_effect_expr_def, supported_expr_exists_def] >>
  rpt strip_tac >>
  qpat_assum `!e. p e ==> ?ann tb target args. _` imp_res_tac >>
  gvs[] >> metis_tac[]
QED

Theorem supported_expr_type_builtin_exclusion:
  (!e. p e ==> ?ann tb target args. e = TypeBuiltin ann tb target args) /\
  (!ann tb target args. supported_type_builtin_form tops ann tb target args ==>
     ~p (TypeBuiltin ann tb target args)) ==>
  !e. supported_expr tops e ==> ~supported_expr_exists p e
Proof
  strip_tac >>
  drule supported_pure_type_builtin_exclusion >> strip_tac >>
  drule supported_effect_type_builtin_exclusion >> strip_tac >>
  rw[supported_expr_def] >> metis_tac[]
QED
