Theory whitelistIteratorProps
Ancestors
  constSubst vyperAST vyperTypeSystem supportedStmts supportedExprs option
  whitelistCheckerDecls

Theorem lit_pair_case_other[local]:
  (!ta s tb e. ~(x = Literal ta (IntL s) /\ y = Literal tb (IntL e))) ==>
  (case (x, y) of (Literal _ (IntL s), Literal _ (IntL e)) => P s e | _ => d) = d
Proof
  Cases_on `x` >> Cases_on `y` >> simp[] >>
  BasicProvers.every_case_tac >> fs[]
QED

Theorem typed_array_iterator_supported:
  type_stmt env ret (For x ty (Array e) n lbody) = SOME out /\
  (well_typed_expr env e ==> supported_pure_expr tops e) ==>
  supported_iterator tops ty (Array e) n
Proof
  strip_tac >> drule type_stmt_for_array_bound >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp[Once type_stmt_def, AllCaseEqs(), well_typed_iterator_def] >>
  rpt strip_tac >>
  Cases_on `e` >>
  gvs[supported_iterator_def, expr_type_def, call_result_expr_def,
      supported_expr_def, bound_length_def, supported_pure_expr_def,
      optionTheory.IS_SOME_EXISTS] >>
  Cases_on `c` >> gvs[call_result_expr_def]
QED

Theorem typed_range_iterator_supported:
  type_stmt env ret (For x ty (Range a b) n lbody) = SOME out /\
  (well_typed_expr env a ==> supported_pure_expr tops a) /\
  (well_typed_expr env b ==> supported_pure_expr tops b) /\
  (!ta i tb j.
    subst_consts_expr (module_consts_env tops []) a = Literal ta (IntL i) /\
    subst_consts_expr (module_consts_env tops []) b = Literal tb (IntL j) ==>
    i <= j /\ n = Num (j - i)) ==>
  supported_iterator tops ty (Range a b) n
Proof
  strip_tac >> drule type_stmt_for_range_integer_type >> strip_tac >>
  Cases_on `?ta i tb j. a = Literal ta (IntL i) /\ b = Literal tb (IntL j)`
  >- (gvs[supported_iterator_def] >> drule type_stmt_for_range_literal_bounds >>
      rw[] >> intLib.ARITH_TAC) >>
  `0 < n` by
    (drule type_stmt_for_range_bound_pos >>
     gvs[lit_pair_case_other] >> metis_tac[]) >>
  `well_typed_expr env a /\ well_typed_expr env b` by
    (qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
     simp[Once type_stmt_def, AllCaseEqs(), well_typed_iterator_def]) >>
  Cases_on `?ta i tb j.
    subst_consts_expr (module_consts_env tops []) a = Literal ta (IntL i) /\
    subst_consts_expr (module_consts_env tops []) b = Literal tb (IntL j)` >>
  gvs[supported_iterator_def, lit_pair_case_other] >> metis_tac[]
QED
