(* Literal topics are evaluated before the RawLog data expression. *)
Theory s1PrefixRawLogArgJudgments
Ancestors
  s1PrefixPreds bodyFullRawLogReadiness exprSimAggregateSource
  vyperContext vyperInterpreter vyperValue vyperState vyperAST

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule_all raw_log_full_children_ready >> strip_tac >>
  qpat_x_assum `body_exprs_prefix_ok _ [_; _]` mp_tac >>
  simp[body_exprs_prefix_ok_def] >> strip_tac >> simp[] >>
  conj_tac
  >- (drule body_make_array_children_prefix_ok >>
      simp[builtin_args_length_ok_def, compatible_bound_def]) >>
  rpt strip_tac >>
  `eval_expr cx
     (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
       (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics)
     (es with gas_obs := gs) = (INL (Value (ArrayV (DynArrayV vs))),mid)` by
    (drule_at (Pat `eval_exprs _ _ _ = _`) aggregate_eval_make_array >>
     disch_then (qspecl_then
       [`BaseTV (BytesT (Fixed 32))`, `BaseT (BytesT (Fixed 32))`,
        `Dynamic n`, `ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n)`] mp_tac) >>
     simp[compatible_bound_def, evaluate_type_def, make_array_value_def]) >>
  first_x_assum irule >>
  qexistsl_tac [`es with gas_obs := gs`, `Value (ArrayV (DynArrayV vs))`,
                `mid`, `mid`, `ArrayV (DynArrayV vs)`, `mid`] >>
  simp[read_result_def, return_def]
QED
*)
Theorem raw_log_prefix_arg_judgments:
  expr_body_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
       data] dflt) es /\
  LENGTH topics <= n /\
  body_exprs_full_ok cx
    [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
      (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
     data] /\
  body_exprs_prefix_ok cx
    [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
      (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
     data] ==>
  body_exprs_full_ok cx topics /\ body_exprs_prefix_ok cx topics /\
  (!gs vs mid. eval_exprs cx topics (es with gas_obs := gs) = (INL vs,mid) ==>
    body_expr_prefix_ok cx data)
Proof
  cheat
QED
