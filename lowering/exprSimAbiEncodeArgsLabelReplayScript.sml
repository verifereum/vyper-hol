Theory exprSimAbiEncodeArgsLabelReplay
Ancestors
  abiArgsCompilerImage exprSimMemorySource vyperInterpreter vyperContext
  vyperState vyperValue vyperAST vyperStatePreservation

Theorem abi_args_name_replay:
  bind (eval_expr cx (Name ann id)) (read_result cx) es = (INL v,ee) ==>
  !gs. bind (eval_expr cx (Name ann id)) (read_result cx)
    (es with gas_obs := gs) = (INL v,ee with gas_obs := gs)
Proof
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def] >>
  Cases_on `IS_SOME (lookup_scopes id es.scopes)` >>
  simp[raise_def, bind_def, return_def] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule read_result_gas_obs >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def]
QED

Theorem abi_args_singleton_source[local]:
  eval_exprs cx [e] = bind (bind (eval_expr cx e) (read_result cx))
    (\v. return [v])
Proof
  simp[FUN_EQ_THM, Once evaluate_def, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[bind_def] >>
  rename1 `read_result cx a r` >> Cases_on `read_result cx a r` >>
  Cases_on `q` >> simp[Once evaluate_def, bind_def, return_def]
QED

Theorem abi_args_convert_replay:
  (!v ee. bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
    !gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,ee with gas_obs := gs)) /\
  bind (eval_expr cx (TypeBuiltin ann Convert ty [e])) (read_result cx) es =
    (INL v,ee) ==>
  !gs. bind (eval_expr cx (TypeBuiltin ann Convert ty [e])) (read_result cx)
    (es with gas_obs := gs) = (INL v,ee with gas_obs := gs)
Proof
  strip_tac >>
  qpat_x_assum `bind (eval_expr cx (TypeBuiltin _ _ _ _)) _ _ = _` mp_tac >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, abi_args_singleton_source] >>
  Cases_on `bind (eval_expr cx e) (read_result cx) es` >>
  Cases_on `q` >>
  fs[vyperStateTheory.assert_def, bind_def, return_def] >>
  rename1 `evaluate_type_builtin cx Convert ty [expr_type e] [a]` >>
  Cases_on `evaluate_type_builtin cx Convert ty [expr_type e] [a]` >>
  simp[lift_sum_def, bind_def, return_def, raise_def, read_result_def] >>
  strip_tac >> gvs[] >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def,
       type_check_def, assert_def, ignore_bind_def, abi_args_singleton_source,
       bind_def, return_def, lift_sum_def, read_result_def]
QED
