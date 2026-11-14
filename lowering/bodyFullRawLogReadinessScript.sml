(* RawLog's literal topics expose children without allocating a target array.
   Successful source topic evaluation unlocks the conditional data child. *)
Theory bodyFullRawLogReadiness
Ancestors
  bodyFullPreds bodyRawLogArgPre exprSimSource exprSimHypsDefs vyperInterpreter vyperContext vyperValue
  vyperState vyperAST list

Theorem raw_log_full_children_ready:
  body_exprs_full_ok cx
    [Builtin ann (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
     data] /\ LENGTH topics <= n ==>
  body_exprs_full_ok cx topics /\
  (!es vs es'. eval_exprs cx topics es = (INL vs, es') ==>
    body_expr_full_ok cx data)
Proof
  strip_tac >>
  `body_expr_full_ok cx
     (Builtin ann (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics)`
    by gvs[body_exprs_full_ok_def] >>
  conj_tac
  >- (irule body_make_array_children_full_ok >>
      goal_assum (drule_at Any) >>
      simp[builtin_args_length_ok_def, compatible_bound_def]) >>
  rpt strip_tac >>
  `eval_expr cx
     (Builtin ann (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics)
     es = (INL (Value (ArrayV (DynArrayV vs))), es')` by
    (simp[Once evaluate_def, builtin_args_length_ok_def, compatible_bound_def,
          type_check_def, assert_def, ignore_bind_def, bind_def, return_def,
          get_accounts_def, lift_sum_def, evaluate_builtin_def,
          evaluate_type_def, make_array_value_def]) >>
  qpat_x_assum `body_exprs_full_ok _ [_; _]` mp_tac >>
  simp[body_exprs_full_ok_def] >> strip_tac >>
  first_x_assum irule >>
  qexistsl_tac [`es`, `Value (ArrayV (DynArrayV vs))`, `es'`, `es'`,
                  `ArrayV (DynArrayV vs)`, `es'`] >>
  simp[read_result_def, return_def]
QED

Theorem raw_log_full_data_reached_ready:
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
       data] dflt) es /\
  body_exprs_full_ok cx
    [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
     data] /\ LENGTH topics <= n /\
  eval_exprs cx topics es = (INL vs, es') ==>
  expr_sim_inv cenv cx env es' /\
  expr_body_pre cenv cx env data es' /\ body_expr_full_ok cx data
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env
     (Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics) es` by
    (drule expr_body_pre_raw_log_arg >> disch_then irule >> simp[]) >>
  `eval_expr cx
     (Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics)
     es = (INL (Value (ArrayV (DynArrayV vs))), es')` by
    (simp[Once evaluate_def, builtin_args_length_ok_def, compatible_bound_def,
          type_check_def, assert_def, ignore_bind_def, bind_def, return_def,
          get_accounts_def, lift_sum_def, evaluate_builtin_def,
          evaluate_type_def, make_array_value_def]) >>
  `expr_sim_inv cenv cx env es'` by
    (drule_all expr_body_pre_eval_result >> simp[]) >>
  simp[] >> conj_tac
  >- (drule expr_body_pre_raw_log_arg >> disch_then irule >> simp[]) >>
  drule_all raw_log_full_children_ready >> strip_tac >>
  first_x_assum drule >> simp[]
QED
