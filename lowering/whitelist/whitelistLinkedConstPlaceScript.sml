(* Closed constant replacements can have qualified, but not local, roots. *)
Theory whitelistLinkedConstPlace
Ancestors
  constSubstCorrect vyperTypeContract supportedExprs supportedExprForms
  exprLowering vyperAST list pair

Triviality closed_const_descriptor:
  !e. constant_expr mods e /\ const_local_refs e = [] ==>
    qualified_place_root e \/ supported_place_info tops e = ValPT (expr_type e)
Proof
  measureInduct_on `expr_size e` >> strip_tac >> Cases_on `e` >>
  gvs[constant_expr_def, const_local_refs_def, qualified_place_root_def,
      supported_place_info_def, place_type_def, expr_type_def]
  >- (rename1 `constant_expr mods (TopLevelName _ ns)` >>
      PairCases_on `ns` >> Cases_on `ns0` >>
      gvs[constant_expr_def, const_local_refs_def]) >>
  qmatch_goalsub_rename_tac `qualified_place_root sub_base` >>
  first_x_assum (qspec_then `sub_base` mp_tac) >> simp[expr_size_def] >>
  disch_then strip_assume_tac >> simp[]
QED

Theorem closed_const_place_facts:
  !e. constant_expr mods e /\ const_local_refs e = [] ==>
    (qualified_place_root e \/ supported_place_info tops e = ValPT (expr_type e)) /\
    (supported_pure_expr tops e ==> supported_place_expr tops e)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule closed_const_descriptor >> simp[]) >>
  Cases_on `e` >> gvs[constant_expr_def, const_local_refs_def, supported_pure_expr_def] >>
  rename1 `constant_expr mods (TopLevelName _ ns)` >>
  PairCases_on `ns` >> Cases_on `ns0` >>
  gvs[constant_expr_def, const_local_refs_def, supported_place_root_def]
QED
