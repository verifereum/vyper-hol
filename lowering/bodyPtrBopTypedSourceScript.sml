Theory bodyPtrBopTypedSource
Ancestors
  bodyPtrBopSource bodyPtrBopOperandContract exprSimSource exprBopSimProps
  exprSimHypsDefs exprSimDefs loweringPosts vyperTypeSystem vyperTyping
  vyperContext vyperState vyperInterpreter exprSimHyps vyperTypeInvariants
  vyperTypeExprResult vyperTypeExprSoundness

Theorem bop_typed_source_witness:
  expr_body_pre cenv cx env e es /\
  (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
        (INL v,ee)) ==>
  expr_sim_inv cenv cx env ee /\
  (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!n. expr_int_literal e = SOME n ==> v = IntV n) /\
  (shift_amount_ok e ==> ?i. v = IntV i /\ 0 <= i)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v` by
    gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  simp[] >>
  conj_tac >- (drule (REWRITE_RULE [ETA_AX] bop_value_scopes_dom) >> simp[]) >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  conj_tac >- metis_tac[eval_expr_int_literal_agrees] >>
  strip_tac >> drule_all eval_expr_shift_amount >> simp[]
QED

Theorem bop_operand_post_typed_word:
  bop_operand_post d ctx func cenv cx e es sa sb op s G tn v ee t H un /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  eval_operand op t = SOME (typed_val_to_w256 tv v)
Proof
  simp[bop_operand_post_def, expr_post_def] >> rpt strip_tac >>
  fs[post_value_type_word] >>
  drule_all expr_val_rel_typed >> simp[]
QED
