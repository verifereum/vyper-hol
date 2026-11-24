Theory boolChainSource
Ancestors
  exprSimIfExp exprSimSource exprBodyPreProps exprSimHash exprSimWordArgs
  vyperTypeSystem vyperTypeValues vyperValue vyperInterpreter vyperContext vyperState

(* The wrapper forces its argument even when raw evaluation returns a place. *)
Theorem bool_chain_wrapper_action:
  expr_body_pre cenv cx env (Builtin ann (BoolChain d n) [e]) es ==>
  ann = BaseT BoolT /\ expr_type e = BaseT BoolT /\
  expr_body_pre cenv cx env e es /\
  !gs. eval_expr cx (Builtin ann (BoolChain d n) [e]) (es with gas_obs := gs) =
       bind (bind (eval_expr cx e) (read_result cx)) (\v. return (Value v))
         (es with gas_obs := gs)
Proof
  strip_tac >> drule expr_body_pre_static_facts >> strip_tac >>
  `ann = BaseT BoolT /\ expr_type e = BaseT BoolT` by
    fs[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`ann`, `[e]`, `BoolChain d n`, `es`] >> simp[]) >>
  simp[] >> gen_tac >>
  simp[eval_expr_unary_builtin_action, precompile_builtin_def,
       is_self_codesize_def, builtin_args_length_ok_def] >>
  Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)` >>
  rename1 `bind (eval_expr cx e) _ _ = (arg_res,arg_state)` >>
  reverse (Cases_on `arg_res`) >- simp[bind_def] >>
  rename1 `bind (eval_expr cx e) _ _ = (INL v,arg_state)` >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `is_word_type (expr_type e)` by simp[compileEnvTheory.is_word_type_def] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_word_value) >>
  simp[evaluate_type_def] >>
  disch_then (strip_assume_tac o MATCH_MP value_has_type_BoolTV) >>
  gvs[bind_def, return_def, builtin_result_def, evaluate_builtin_def]
QED

(* Keep the selected arm's entire outcome, including the remaining gas list. *)
Theorem bool_chain_forced_select:
  expr_body_pre cenv cx env (IfExp (BaseT BoolT) c a b) es ==>
  !gs. bind (eval_expr cx (IfExp (BaseT BoolT) c a b)) (read_result cx)
         (es with gas_obs := gs) =
       bind (bind (eval_expr cx c) (read_result cx))
         (\v. if v = BoolV T then bind (eval_expr cx a) (read_result cx)
              else if v = BoolV F then bind (eval_expr cx b) (read_result cx)
              else raise (Error (TypeError "not BoolV"))) (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  `expr_body_pre cenv cx env (IfExp (BaseT BoolT) c a b)
     (es with gas_obs := gs)` by simp[] >>
  Cases_on `bind (eval_expr cx (IfExp (BaseT BoolT) c a b)) (read_result cx)
    (es with gas_obs := gs)` >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_res_ok) >> strip_tac >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_ifexp_cases) >>
  strip_tac >> gvs[exprSimDefsTheory.expr_res_ok_def] >>
  simp[bind_def] >> rename1 `if bv then a else b` >> Cases_on `bv` >> gvs[bind_def]
QED
