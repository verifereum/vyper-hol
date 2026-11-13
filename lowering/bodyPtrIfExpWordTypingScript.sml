Theory bodyPtrIfExpWordTyping
Ancestors
  bodyPtrDefs exprSimSource exprSimIfExp exprSimOperators
  gasSummaryComposePtr vyperInterpreter vyperState

(* The suffix uses expr_type e, not lowered_value_type cenv e. Runtime
   source typing and the representation therefore evaluate exactly the
   same annotation; no layout or call-return conversion is involved. *)
Theorem ifexp_marked_arm_read_typed:
  expr_body_pre cenv cx env e es /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx e) (es,s0,G0,tn0)
    marks (INL raw) ee G tn r /\
  read_result cx raw (ee with gas_obs := []) =
    (INL v,ee with gas_obs := []) ==>
  ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
        value_has_type tvt v
Proof
  strip_tac >>
  `eval_expr cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

(* The real selected-arm precondition is available after a successful
   forced condition, at the same cleared-observation state used by the
   marked continuation. No extra source typing premise is postulated. *)
Theorem ifexp_marked_condition_arm_pre:
  expr_body_pre cenv cx env (IfExp ty c a b) es /\
  gas_marked_exec_ptr D (ctx,fn) PG
    (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) ee G tn r ==>
  expr_body_pre cenv cx env a (ee with gas_obs := []) /\
  expr_body_pre cenv cx env b (ee with gas_obs := [])
Proof
  strip_tac >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule expr_body_pre_ifexp >> strip_tac >>
  `expr_body_pre cenv cx env c
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >>
  strip_tac >> first_x_assum drule >> simp[]
QED
