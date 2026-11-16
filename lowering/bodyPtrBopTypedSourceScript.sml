Theory bodyPtrBopTypedSource
Ancestors
  exprSimOperators compileEnv
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
  bop_operand_post H d ctx func cenv cx e es sa sb op s G tn v ee t HG un /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  eval_operand op t = SOME (typed_val_to_w256 tv v)
Proof
  simp[bop_operand_post_def, expr_post_def] >> rpt strip_tac >>
  fs[post_value_type_word] >>
  drule_all expr_val_rel_typed >> simp[]
QED

Theorem bop_pair_source_facts:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) =
        (INL v1,es1)) /\
  (?gs. bind (eval_expr cx e2) (read_result cx) (es1 with gas_obs := gs) =
        (INL v2,es2)) ==>
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  type_bits (expr_type e1) MOD 8 = 0 /\
  (bop = Exp ==> IS_SOME (expr_int_literal e1) \/
    ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
  (!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
  (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n) /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
  (?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
         value_has_type tv1 v1) /\
  (?tv2. evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
         value_has_type tv2 v2) /\
  expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2) /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes
Proof
  strip_tac >> drule expr_body_pre_bop >> strip_tac >>
  drule bop_typed_source_witness >>
  disch_then (qspecl_then [`v1`, `es1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `expr_body_pre cenv cx env e2 es1` by metis_tac[] >>
  drule bop_typed_source_witness >>
  disch_then (qspecl_then [`v2`, `es2`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `is_word_type ann` by
    (Cases_on `bop` >> gvs[well_typed_binop_def, is_word_type_def]) >>
  `type_bits (expr_type e1) MOD 8 = 0` by
    (irule byte_widths_expr_type >> gvs[expr_body_pre_def]) >>
  `IS_SOME (evaluate_type (get_tenv cx) ann)` by
    metis_tac[expr_body_pre_type_evaluates, vyperASTTheory.expr_type_def] >>
  `expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2)` by
    (irule bop_typed_source_result_ok >> simp[] >> metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  drule expr_body_pre_bop_operands >> strip_tac >>
  simp[] >> metis_tac[]
QED
