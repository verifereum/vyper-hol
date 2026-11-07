Theory bodyPtrBopInSourceOrigin
Ancestors bodyPtrBopInSourceTyping bodyPtrBopInMixed
  exprSimSource exprSimHypsDefs exprSimHyps exprBopSimDefs exprBopSimProps
  exprSimBopRestWordBasics vyperContext vyperState vyperValueOperation
  vyperValue vyperAST compileEnv loweringPosts exprSimWordArgs

(* Typing fixes the array type used by evaluate_builtin.  The error mapping
   in bop_result is precisely lift_sum's source exception mapping. *)
Theorem membership_typed_result_action:
  evaluate_type (get_tenv cx) t2 = SOME tv ==>
  (\st. (bop_result cx (BaseT BoolT) bop [t1;t2] v1 v2 st,st)) =
  lift_sum (evaluate_binop (Unsigned 0) tv bop v1 v2)
Proof
  strip_tac >> simp[FUN_EQ_THM, bop_result_def, evaluate_builtin_def,
    type_to_int_bound_def, lift_sum_def, return_def, raise_def] >>
  Cases_on `evaluate_binop (Unsigned 0) tv bop v1 v2` >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem membership_typed_read_continuation:
  evaluate_type (get_tenv cx) t2 = SOME tv ==>
  bind (read_result cx tvv)
    (\v2 st. (bop_result cx (BaseT BoolT) bop [t1;t2] v1 v2 st,st)) =
  bind (read_result cx tvv)
    (\a. lift_sum (evaluate_binop (Unsigned 0) tv bop v1 a))
Proof
  strip_tac >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> gen_tac >>
  drule membership_typed_result_action >> simp[FUN_EQ_THM]
QED

Theorem membership_needle_origin_success:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  (?gs. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,ee)) ==>
  expr_sim_inv cenv cx env ee /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
       value_has_type tv v
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  conj_tac >- metis_tac[expr_body_pre_eval] >>
  conj_tac
  >- (drule (CONV_RULE (DEPTH_CONV ETA_CONV)
        forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_value) >> simp[]
QED

Theorem membership_array_origin_success:
  expr_body_pre cenv cx env e es /\ expr_type e = ArrayT et bd /\
  (?gs. eval_expr cx e (es with gas_obs := gs) = (INL tvv,ee)) /\
  vv_holds cenv cx (expr_type e) tvv vv ee s ==>
  ?tv av. evaluate_type (get_tenv cx) et = SOME tv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
    read_result cx tvv ee = (INL (ArrayV av),ee) /\
    value_has_type (ArrayTV tv bd) (ArrayV av)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  drule rest_word_vv_read_suffix >> strip_tac >>
  first_x_assum (qspec_then `ee.gas_obs` assume_tac) >>
  `ee with gas_obs := ee.gas_obs = ee` by
    simp[evaluation_state_component_equality] >>
  gvs[] >>
  `value_has_type tvt v` by metis_tac[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> fs[Once vyperTypingTheory.value_has_type_def] >>
  metis_tac[]
QED

Theorem membership_mixed_origin_success:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT et bd /\
  (?gs. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gs) = (INL v,es1)) /\
  (?gs. eval_expr cx e2 (es1 with gas_obs := gs) = (INL tvv,ee)) /\
  vv_holds cenv cx (expr_type e2) tvv vv ee s ==>
  ann = BaseT BoolT /\ expr_type e1 = et /\ is_word_type et /\
  expr_sim_inv cenv cx env es1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  ?tv av. evaluate_type (get_tenv cx) et = SOME tv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
    value_has_type tv v /\
    read_result cx tvv ee = (INL (ArrayV av),ee) /\
    value_has_type (ArrayTV tv bd) (ArrayV av)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all membership_source_array_type >> strip_tac >>
  drule exprSimOperatorsTheory.expr_body_pre_bop >> strip_tac >>
  drule_all membership_needle_origin_success >> strip_tac >>
  `expr_body_pre cenv cx env e2 es1` by metis_tac[] >>
  drule_all membership_array_origin_success >> strip_tac >> gvs[] >>
  metis_tac[]
QED
