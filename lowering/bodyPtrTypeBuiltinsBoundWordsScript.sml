Theory bodyPtrTypeBuiltinsBoundWords
Ancestors
  bodyPtrTypeBuiltinsOperands exprSimAggregates gasContext bodyPtrDefs
  exprPtrUnwrap exprSimSource exprLoweringProps vyperState
Libs monadsyntax


(* Raw structural inspection (m1313_t001): imported and explicit heads
   are both vyperState$bind at the same evaluation_state monad type.
   Imported continuation is ABS result (vyperState$read_result cx result);
   explicit continuation is vyperState$read_result cx. There are no other
   wrappers. Explicit DEPTH_CONV ETA_CONV, applied to the whole implication
   below, normalizes both propositions; simp[ETA_THM] did not do so. *)

Theorem bound_builtin_explicit_bind:
  !cx ann tb typ args es res ee.
    vyperState$bind (eval_expr cx (TypeBuiltin ann tb typ args)) (read_result cx) es = (res,ee) /\
    expr_res_ok res /\ MEM tb [MaxValue;MinValue;Epsilon] ==>
    ee = es /\ args = [] /\
    ?v. res = INL v /\ evaluate_type_builtin cx tb typ [] [] = INL v
Proof
  mp_tac eval_expr_bound_builtin >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[]
QED

Theorem bound_builtin_source_gas:
  !cx ann tb typ args es.
    MEM tb [MaxValue;MinValue;Epsilon] /\
    gas_admissible
      (vyperState$bind (eval_expr cx (TypeBuiltin ann tb typ args)) (read_result cx))
      expr_res_ok es ==>
    ?v. evaluate_type_builtin cx tb typ [] [] = INL v /\ args = [] /\
      !gs. vyperState$bind (eval_expr cx (TypeBuiltin ann tb typ args)) (read_result cx)
        (es with gas_obs := gs) = (INL v,es with gas_obs := gs)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `vyperState$bind (eval_expr cx (TypeBuiltin ann tb typ args)) (read_result cx) es` >>
  rename1 `_ = (res,ee)` >>
  `expr_res_ok res` by
    (qpat_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all bound_builtin_explicit_bind >> strip_tac >>
  qpat_x_assum `args = []` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >> gen_tac >>
  rename1 `vyperState$bind (eval_expr cx (TypeBuiltin ann bi typ [])) (read_result cx)
    (st with gas_obs := gs) = _` >>
  Cases_on `vyperState$bind (eval_expr cx (TypeBuiltin ann bi typ [])) (read_result cx)
    (st with gas_obs := gs)` >>
  rename1 `_ (st with gas_obs := gs) = (r2,ee2)` >>
  `expr_res_ok r2` by (drule_all gas_admissible_result >> simp[]) >>
  drule_all bound_builtin_explicit_bind >> strip_tac >> gvs[]
QED
