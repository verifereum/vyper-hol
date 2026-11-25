(* Source sequencing for a unary Convert: force the operand, then convert. *)
Theory bodyFullConvertDynamicSource
Ancestors
  vyperInterpreter vyperState vyperContext exprSimConvert

Theorem convert_dynamic_source_bind:
  eval_expr cx (TypeBuiltin dst Convert dst [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (sum_CASE (convert_result cx (expr_type e) dst v)
         (\w. INL (Value w)) INR, ee))
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac `st` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
    assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `_ = (raw,ee)` >>
  Cases_on `raw` >> simp[] >> rename1 `_ = (INL tv,ee)` >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res,fin)` >>
  Cases_on `res` >> simp[] >> rename1 `_ = (INL val,fin)` >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
    convert_result_def, evaluate_type_builtin_def] >>
  Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e) val dst` >>
  simp[return_def, raise_def]
QED
