Theory assignPlaceEmptyCompose
Ancestors
  assignPlaceEmpty assignPlacePureCode assignPlaceGasCompose placeStore
  targetPlaceSimCases stmtSimDefs gasContext vyperExprNoControl vyperState
Libs monadsyntax

Theorem assign_place_empty_target_admissible:
  expr_body_pre cenv cx env e es /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  strip_tac >> drule_all assign_place_empty_source_action >> strip_tac >>
  rw[gas_admissible_def] >>
  Cases_on `res` >- simp[target_place_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by metis_tac[eval_target_place_no_control] >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl_tac [`ee`, `gs`] >> simp[bind_def]) >>
  gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]
QED

