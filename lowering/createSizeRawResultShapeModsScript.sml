Theory createSizeRawResultShapeMods
Ancestors
  exprSimDefs vyperAST vyperState vyperInterpreter vyperTypeInvariants
  vyperTypeExprSoundness vyperExprNoControl

Theorem create_raw_error_vv_ok:
  no_type_error_result (INR (Error err) : eval_result + vyperState$exception) ==>
  expr_vv_res_ok (INR (Error err))
Proof
  Cases_on `err` >> simp[no_type_error_result_def, expr_vv_res_ok_def]
QED

Theorem create_raw_eval_vv_ok:
  eval_expr cx e st = (res,ee) /\ no_type_error_result res /\
  (case res of INL tv => eval_result_typed (env,cx,ee) tv (Type (expr_type e))
             | INR _ => T) ==>
  expr_vv_res_ok res
Proof
  Cases_on `res`
  >- (Cases_on `x` >> simp[eval_result_typed_def, expr_vv_res_ok_def]) >>
  strip_tac >>
  drule_then assume_tac (CONJUNCT1 eval_expr_no_control) >>
  rename1 `expr_vv_res_ok (INR exc)` >>
  Cases_on `exc` >>
  fs[no_control_exc_def] >>
  simp[expr_vv_res_ok_def, create_raw_error_vv_ok]
QED

