Theory bodyPtrBopSource
Ancestors
  exprSimSource exprSimHyps exprSimHypsDefs exprBopSimProps exprSimOperators
  gasExemptCert vyperState vyperInterpreter vyperTypeBuiltins exprBopSimDefs
  exprSimDefs vyperValueOperation vyperContext

(* The internal CPS predicate is an actual source witness, not an assumed
   preservation property.  This boundary is shared by either word child. *)
Theorem bop_word_source_witness:
  expr_body_pre cenv cx env e es /\ word_value_type (expr_type e) /\
  (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
        (INL v,ee)) ==>
  expr_sim_inv cenv cx env ee /\ word_value v /\
  (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!n. expr_int_literal e = SOME n ==> v = IntV n) /\
  (shift_amount_ok e ==> ?i. v = IntV i /\ 0 <= i)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  reverse conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
      conj_tac >- metis_tac[eval_expr_int_literal_agrees] >>
      strip_tac >> drule_all eval_expr_shift_amount >> simp[]) >>
  drule (REWRITE_RULE [ETA_AX] bop_value_scopes_dom) >> simp[]
QED

Theorem bop_typed_source_result_ok:
  well_typed_binop ann bop t1 t2 /\
  evaluate_type (get_tenv cx) ann = SOME tvr /\
  evaluate_type (get_tenv cx) t1 = SOME tv1 /\
  evaluate_type (get_tenv cx) t2 = SOME tv2 /\
  value_has_type tv1 v1 /\ value_has_type tv2 v2 ==>
  expr_res_ok (bop_result cx ann bop [t1;t2] v1 v2 es)
Proof
  strip_tac >>
  `!msg. evaluate_builtin cx es.accounts ann (Bop bop) [t1;t2] [v1;v2] <>
    INR (TypeError msg)` by
    (simp[evaluate_builtin_def] >>
     metis_tac[well_typed_binop_no_type_error]) >>
  simp[bop_result_def] >>
  Cases_on `evaluate_builtin cx es.accounts ann (Bop bop) [t1;t2] [v1;v2]` >>
  simp[expr_res_ok_def] >> Cases_on `y` >> gvs[]
QED
