(* Source and compiler boundaries. Narrow operand hypotheses are explicit:
   the current typing rule also allows fixed bytes and signed offsets. *)
Theory exprSimExtract32Source
Ancestors
  exprSimSource exprSimHyps exprSimHypsDefs exprSimDefs exprSimHash vyperTyping
  exprLowering exprCallBounds compileEnv builtinBytes
  vyperTypeSystem vyperTypeCallGraph vyperAST vyperInterpreter vyperState vyperContext
  supportedExprTraverse allocLimits gasContext gasSummary list
Libs
  monadsyntax

Theorem expr_body_pre_type_builtin_arg:
  expr_body_pre cenv cx env (TypeBuiltin ann bi ty args) es /\ MEM e args /\
  expr_sim_inv cenv cx env es' ==>
  expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def,
     vyperTypeCallGraphTheory.int_calls_expr_def,
     byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
     supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Theorem extract32_body_pre_shape:
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 t args) es ==>
  ?src off bd bt.
    args = [src; off] /\ expr_type src = BaseT (BytesT bd) /\
    is_int_type (expr_type off) /\ t = BaseT bt /\
    extract32_result_base_ok bt /\ ann = t
Proof
  simp[expr_body_pre_def, well_typed_expr_def,
       well_typed_type_builtin_args_def, type_builtin_result_ok_def] >>
  strip_tac >>
  Cases_on `args` >> gvs[] >>
  rename1 `LENGTH rest = 1` >>
  Cases_on `rest` >> gvs[] >>
  Cases_on `t'` >> gvs[] >> metis_tac[]
QED

Theorem compile_extract32_stages:
  compile_expr cenv ty (TypeBuiltin ann Extract32 t [src; off]) st =
    (let (src_mem, st1) = lower_value compile_expr cenv (expr_type src) src st in
     let ((src_len, src_data), st2) = compile_bytestring_src src_mem st1 in
     let (off_op, st3) = lower_value compile_expr cenv ty off st2 in
     let (raw, st4) = compile_extract32_load src_len src_data off_op st3 in
     as_stack_val ann (compile_clamp_basetype raw t st4))
Proof
  rewrite_tac[compile_expr_type_builtin_dispatch] >>
  simp[Once compile_type_builtin_dispatch_component_eq,
       lower_value_def, comp_bind_def,
       exprCallBoundsTheory.expr_child_callback_def, listTheory.list_size_def,
       vyperASTTheory.expr_size_def]
QED

Theorem extract32_off_case:
  exprs_case nocalls ctx func cenv cx [src;off] /\
  (do r <- eval_expr cx src; read_result cx r od) es = (INL v,es1) ==>
  expr_sim_case nocalls ctx func cenv cx off
Proof
  simp[exprs_case_def] >> strip_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum mp_tac >> simp[] >> metis_tac[]
QED

Theorem eval_expr_extract32_bind:
  (do result <- eval_expr cx (TypeBuiltin ann Extract32 ty [src; off]);
      read_result cx result od) =
  (do v1 <- (do result <- eval_expr cx src; read_result cx result od);
      v2 <- (do result <- eval_expr cx off; read_result cx result od);
      lift_sum (evaluate_type_builtin cx Extract32 ty
        [expr_type src; expr_type off] [v1; v2]) od)
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx src x` >> rename1 `_ = (raw1, st1)` >>
  reverse (Cases_on `raw1`) >- simp[] >>
  rename1 `eval_expr cx src x = (INL r1, st1)` >>
  Cases_on `read_result cx r1 st1` >> rename1 `_ = (res1, es1)` >>
  reverse (Cases_on `res1`) >- simp[] >>
  rename1 `read_result cx r1 st1 = (INL v1, es1)` >>
  simp[] >> simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx off es1` >> rename1 `_ = (raw2, st2)` >>
  reverse (Cases_on `raw2`) >- simp[] >>
  rename1 `eval_expr cx off es1 = (INL r2, st2)` >>
  Cases_on `read_result cx r2 st2` >> rename1 `_ = (res2, es2)` >>
  reverse (Cases_on `res2`) >- simp[] >>
  rename1 `read_result cx r2 st2 = (INL v2, es2)` >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def] >>
  Cases_on `evaluate_type_builtin cx Extract32 ty
              [expr_type src; expr_type off] [v1; v2]` >>
  simp[read_result_def, return_def, raise_def]
QED

Theorem extract32_first_admissible:
  gas_admissible
    (do r <- eval_expr cx (TypeBuiltin ann Extract32 ty [src; off]);
        read_result cx r od) expr_res_ok es ==>
  gas_admissible
    (do r <- eval_expr cx src; read_result cx r od) expr_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  pure_once_rewrite_tac[eval_expr_extract32_bind] >>
  simp[bind_def] >>
  disch_then (qspecl_then [`INR y`, `ee`] mp_tac) >> gvs[bind_def]
QED

Theorem extract32_second_admissible:
  gas_admissible
    (do r <- eval_expr cx (TypeBuiltin ann Extract32 ty [src; off]);
        read_result cx r od) expr_res_ok es /\
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx src; read_result cx r od)
    (es, s0) marks (INL v1) mid (OK t) ==>
  gas_admissible
    (do r <- eval_expr cx off; read_result cx r od)
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  pure_once_rewrite_tac[eval_expr_extract32_bind] >>
  simp[bind_def] >>
  disch_then (qspecl_then [`INR y`, `ee`] mp_tac) >> gvs[bind_def]
QED

Theorem extract32_source_value:
  expr_body_pre cenv cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic m)) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
  ?bs. v = BytesV bs /\ LENGTH bs <= m
Proof
  strip_tac >> drule_all expr_body_pre_base_result >> strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem extract32_offset_value:
  expr_body_pre cenv cx env e es /\ is_uint_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
  ?i. v = IntV i /\ 0 <= i
Proof
  simp[is_uint_type_def] >> strip_tac >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem extract32_typed_operands:
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 t [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\ is_uint_type (expr_type off) /\
  (do r <- eval_expr cx src; read_result cx r od) es = (INL v1,es1) /\
  (do r <- eval_expr cx off; read_result cx r od) es1 = (r2,es2) ==>
  expr_sim_inv cenv cx env es1 /\ expr_sim_inv cenv cx env es2 /\
  expr_res_ok r2 /\
  (?bs. v1 = BytesV bs /\ LENGTH bs <= m) /\
  (!v2. r2 = INL v2 ==> ?i. v2 = IntV i /\ 0 <= i)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env src es` by
    (drule expr_body_pre_type_builtin_arg >> disch_then irule >> simp[]) >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  `expr_body_pre cenv cx env off es1` by
    (drule expr_body_pre_type_builtin_arg >> disch_then irule >> simp[]) >>
  drule_all extract32_source_value >> strip_tac >>
  `?k. expr_type off = BaseT (UintT k)` by gvs[is_uint_type_def] >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  simp[] >> rpt strip_tac >> irule extract32_offset_value >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Source observations are replaced by the marked operand witnesses. *)
Theorem extract32_marked_source_typed:
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 ty [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  gas_marked_exec memory (ctx, func)
    (do r <- eval_expr cx src; read_result cx r od)
    (es, s0) marks (INL v) mid (OK t) ==>
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  expr_body_pre cenv cx env off (mid with gas_obs := []) /\
  (?bs. v = BytesV bs /\ LENGTH bs <= m)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env src
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    (simp[] >> irule expr_body_pre_type_builtin_arg >>
     conj_tac >- gvs[expr_body_pre_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  ` (do r <- eval_expr cx src; read_result cx r od)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v, mid with gas_obs := [])` by
    (fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  drule_all extract32_source_value >> strip_tac >> simp[] >>
  irule expr_body_pre_type_builtin_arg >>
  conj_tac >- fs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem eval_expr_extract32_vv_bind:
  eval_expr cx (TypeBuiltin ann Extract32 ty [src;off]) =
  (do v1 <- (do r <- eval_expr cx src; read_result cx r od);
      v2 <- (do r <- eval_expr cx off; read_result cx r od);
      v <- lift_sum (evaluate_type_builtin cx Extract32 ty
              [expr_type src;expr_type off] [v1;v2]);
      return (Value v) od)
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx src x` >> rename1 `_ = (raw1, st1)` >>
  reverse (Cases_on `raw1`) >- simp[] >>
  rename1 `eval_expr cx src x = (INL r1, st1)` >>
  Cases_on `read_result cx r1 st1` >> rename1 `_ = (res1, es1)` >>
  reverse (Cases_on `res1`) >- simp[] >>
  rename1 `read_result cx r1 st1 = (INL v1, es1)` >>
  simp[] >> simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx off es1` >> rename1 `_ = (raw2, st2)` >>
  reverse (Cases_on `raw2`) >- simp[] >>
  rename1 `eval_expr cx off es1 = (INL r2, st2)` >>
  Cases_on `read_result cx r2 st2` >> rename1 `_ = (res2, es2)` >>
  reverse (Cases_on `res2`) >- simp[] >>
  rename1 `read_result cx r2 st2 = (INL v2, es2)` >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def] >>
  Cases_on `evaluate_type_builtin cx Extract32 ty
              [expr_type src; expr_type off] [v1; v2]` >>
  simp[return_def, raise_def]
QED

Theorem extract32_vv_first_admissible:
  gas_admissible (eval_expr cx (TypeBuiltin ann Extract32 ty [src;off]))
    expr_vv_res_ok es ==>
  gas_admissible
    (do r <- eval_expr cx src; read_result cx r od) expr_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  pure_once_rewrite_tac[eval_expr_extract32_vv_bind] >>
  simp[bind_def] >>
  gvs[bind_def, expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem extract32_vv_second_admissible:
  gas_admissible (eval_expr cx (TypeBuiltin ann Extract32 ty [src;off]))
    expr_vv_res_ok es /\
  gas_marked_exec memory (ctx,func)
    (do r <- eval_expr cx src; read_result cx r od)
    (es,s0) marks (INL v1) mid (OK t) ==>
  gas_admissible
    (do r <- eval_expr cx off; read_result cx r od)
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  pure_once_rewrite_tac[eval_expr_extract32_vv_bind] >>
  simp[bind_def] >>
  gvs[bind_def, expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem extract32_marked_off_case:
  exprs_case nocalls ctx func cenv cx [src;off] /\
  gas_marked_exec memory (ctx,func)
    (do r <- eval_expr cx src; read_result cx r od)
    (es,s0) marks (INL v) mid (OK t) ==>
  expr_sim_case nocalls ctx func cenv cx off
Proof
  strip_tac >> irule extract32_off_case >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                `mid with gas_obs := []`, `v`] >>
  fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED
