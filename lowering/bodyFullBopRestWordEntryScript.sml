Theory bodyFullBopRestWordEntry
Ancestors
  bodyFullPreds exprSimSource exprSimHypsDefs exprBopSimProps
  gasSummary vyperState vyperInterpreter exprSimHyps exprSimBopRestWordBasics
  exprSimBopRestWordCompose exprSimBopRestWordFacts vyperTypeSystem vyperValue vyperTyping
  allocLimits

Theorem rest_word_full_second_entry:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  body_exprs_full_ok cx [e1;e2] /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL needle,mid with gas_obs := tail)) ==>
  body_expr_full_ok cx e2 /\
  expr_body_pre cenv cx env e2 (mid with gas_obs := []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!tail. _` (qspec_then `[]` assume_tac) >>
  fs[] >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- fs[expr_body_pre_def] >>
     qexistsl [`ann`, `[e1;e2]`, `Bop bop`, `es`] >> simp[]) >>
  `expr_body_pre cenv cx env e1
      (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[expr_body_pre_eval] >>
  conj_tac
  >- (fs[body_exprs_full_ok_def] >>
      drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >>
      strip_tac >> metis_tac[]) >>
  conj_tac
  >- (irule expr_body_pre_builtin_arg >>
      conj_tac >- gvs[] >>
      qexistsl [`ann`, `[e1;e2]`, `Bop bop`, `es`] >> simp[]) >>
  drule (REWRITE_RULE [ETA_AX] bop_value_scopes_dom) >> simp[]
QED

Theorem rest_word_full_array_read:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  expr_body_pre cenv cx env e1 es /\
  expr_body_pre cenv cx env e2 (mid with gas_obs := []) /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := obs1 ++ tail) = (INL needle,mid with gas_obs := tail)) /\
  (!tail. eval_expr cx e2 (mid with gas_obs := obs2 ++ tail) =
     (INL tv,fin with gas_obs := tail)) /\
  vv_holds cenv cx (post_value_type cenv e2) tv vv (fin with gas_obs := []) u ==>
  ?et pbd av.
    post_value_type cenv e2 = ArrayT (expr_type e1) pbd /\
    (case bd of Fixed n => pbd = Fixed n | Dynamic n => ?m. pbd = Dynamic m) /\
    (case bd of Fixed n => n | Dynamic n => n) < dimword (:256) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME et /\
    evaluate_type (get_tenv cx) (post_value_type cenv e2) = SOME (ArrayTV et pbd) /\
    value_has_type (ArrayTV et bd) (ArrayV av) /\ value_has_type et needle /\
    (!tail. read_result cx tv (fin with gas_obs := tail) =
       (INL (ArrayV av),fin with gas_obs := tail))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  fs[] >>
  `expr_body_pre cenv cx env e2 (mid with gas_obs := obs2)` by gvs[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `type_widens_to env.type_defs (post_value_type cenv e2) (ArrayT (expr_type e1) bd)` by
    (qpat_assum `expr_type e2 = _` (SUBST1_TAC o SYM) >>
     irule post_value_type_widens >> conj_tac
     >- fs[expr_body_pre_def] >>
     qexistsl [`cx`, `mid`] >> fs[expr_body_pre_def]) >>
  `?pbd. post_value_type cenv e2 = ArrayT (expr_type e1) pbd /\
         case bd of Fixed n => pbd = Fixed n | Dynamic n => ?m. pbd = Dynamic m` by
    (qpat_x_assum `type_widens_to _ _ _`
       (strip_assume_tac o REWRITE_RULE [type_widens_to_def])
     >- (Cases_on `bd` >> gvs[]) >>
     Cases_on `post_value_type cenv e2` >>
     gvs[arg_type_fits_def, AllCaseEqs()] >>
     `arg_type_fits t (expr_type e1)` by
       (Cases_on `b` >> Cases_on `bd` >> gvs[arg_type_fits_def]) >>
     `t = expr_type e1` by
       (Cases_on `t` >> Cases_on `expr_type e1` >>
        gvs[arg_type_fits_def, compileEnvTheory.is_word_type_def] >>
        rename1 `arg_type_fits (BaseT b1) (BaseT b2)` >>
        Cases_on `b1` >> Cases_on `b2` >>
        gvs[arg_type_fits_def, compileEnvTheory.is_word_type_def] >>
        rename1 `arg_type_fits (BaseT (BytesT d1)) (BaseT (BytesT d2))` >>
        Cases_on `d1` >> Cases_on `d2` >>
        gvs[arg_type_fits_def, compileEnvTheory.is_word_type_def]) >>
     gvs[] >>
     Cases_on `b` >> Cases_on `bd` >> gvs[arg_type_fits_def]) >>
  drule rest_word_vv_read_suffix >>
  disch_then (qx_choose_then `v2` assume_tac) >>
  qpat_assum `!tail. read_result _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `value_has_type tvt v2` by gvs[] >>
  `?et. tvt = ArrayTV et bd /\
         evaluate_type (get_tenv cx) (expr_type e1) = SOME et` by
    (qpat_x_assum `evaluate_type _ (expr_type e2) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  gnvs[] >>
  `evaluate_type (get_tenv cx) (post_value_type cenv e2) = SOME (ArrayTV et pbd)` by
    (qpat_assum `expr_body_pre _ _ _ e2 _`
       (strip_assume_tac o MATCH_MP post_type_evaluates) >>
     pop_assum mp_tac >> simp[evaluate_type_def, AllCaseEqs()]) >>
  `?av. v2 = ArrayV av` by (Cases_on `v2` >> fs[value_has_type_def]) >>
  gnvs[] >>
  `expr_body_pre cenv cx env e1 (es with gas_obs := obs1)` by simp[] >>
  `value_has_type et needle` by
    (drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_value) >> strip_tac >> gvs[]) >>
  `type_alloc_ok cenv (ArrayT (expr_type e1) bd)` by
    (`alloc_limits_expr cenv e2` by fs[expr_body_pre_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[]) >>
  ` (case bd of Fixed n => n | Dynamic n => n) < dimword (:256)` by
    metis_tac[rest_word_array_alloc_bound] >>
  simp[]
QED
