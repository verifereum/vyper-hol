(* Source-action boundary for counted local declarations. *)
Theory stmtSimDeclSource
Ancestors
  stmtSimDefs exprSimDefs gasContext vyperInterpreter vyperState vyperExprNoControl
Libs
  monadsyntax

Theorem eval_annassign_action:
  evaluate_type (get_tenv cx) typ = SOME tyv ==>
  eval_stmt cx (AnnAssign id typ e) =
    bind (bind (eval_expr cx e) (read_result cx)) (new_variable id tyv)
Proof
  strip_tac >> simp[Once evaluate_def, lift_option_type_def,
    bind_assoc, bind_return, SF ETA_ss]
QED

Theorem annassign_admissible_type:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es ==>
  ?tyv. evaluate_type (get_tenv cx) typ = SOME tyv
Proof
  Cases_on `evaluate_type (get_tenv cx) typ` >> simp[] >>
  simp[gas_admissible_def, Once evaluate_def, lift_option_type_def,
    bind_def, raise_def, stmt_res_ok_def, ignore_bind_def, return_def]
QED

Theorem annassign_admissible_rhs:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> drule annassign_admissible_type >> strip_tac >>
  rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >> gvs[]
     >- metis_tac[read_result_no_control]
     >> metis_tac[cj 1 eval_expr_no_control]) >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >>
     disch_then irule >>
     qexistsl [`ee`, `gs`] >>
     drule eval_annassign_action >>
     disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
     simp[Once bind_def]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem new_variable_admissible_success:
  stmt_res_ok lctx (FST (new_variable id tyv v ee)) ==>
  ?sc rest.
    ee.scopes = sc :: rest /\ lookup_scopes id ee.scopes = NONE /\
    new_variable id tyv v ee =
      (INL (), ee with scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
Proof
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def] >>
  Cases_on `lookup_scopes id ee.scopes` >>
  simp[raise_def, stmt_res_ok_def] >>
  Cases_on `ee.scopes` >> simp[raise_def, stmt_res_ok_def,
                              set_scopes_def, return_def]
QED

Theorem annassign_continuation_success:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  ?sc rest.
    ee.scopes = sc :: rest /\ lookup_scopes id ee.scopes = NONE /\
    new_variable id tyv v ee =
      (INL (), ee with scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
Proof
  strip_tac >> irule new_variable_admissible_success >>
  qexists `lctx` >>
  drule gas_admissible_result >> disch_then irule >>
  qexistsl [`SND (new_variable id tyv v ee)`, `gs`] >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  simp[Once bind_def] >> simp[]
QED

Theorem new_variable_success_gas_obs:
  new_variable id tyv v ee = (INL (), ee') ==>
  !tail. new_variable id tyv v (ee with gas_obs := tail) =
    (INL (), ee' with gas_obs := tail)
Proof
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def] >>
  Cases_on `lookup_scopes id ee.scopes` >>
  simp[raise_def] >> Cases_on `ee.scopes` >>
  simp[raise_def, set_scopes_def, return_def] >>
  strip_tac >> gvs[]
QED

Theorem annassign_continuation_all_tails:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := prefix ++ tail) = (INL v, ee with gas_obs := tail)) ==>
  ?sc rest.
    ee.scopes = sc :: rest /\ lookup_scopes id ee.scopes = NONE /\
    !tail. new_variable id tyv v (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
        with gas_obs := tail)
Proof
  strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  drule_all annassign_continuation_success >>
  strip_tac >> qexistsl [`sc`, `rest`] >> gvs[] >>
  drule new_variable_success_gas_obs >> simp[]
QED
