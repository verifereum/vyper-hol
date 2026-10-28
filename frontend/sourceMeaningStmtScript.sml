Theory sourceMeaningStmt
Ancestors
  sourceMeaningStmtDefs sourceMeaningRuntime sourceMeaningElaborate
  sourceModuleStmt sourceModuleDefs sourceExprElaborate sourceExprProps sourceExprDefs sourceSyntax
  sourceResolve sourceMeaningDefs vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperAST vyperValue alist list

(* Concrete environment/store relation: source declaration identities denote
   runtime scoped cells, not arbitrary computations chosen to match output. *)
Definition source_meaning_locals_def:
  source_meaning_locals types ctx <=>
    (!path ty. ALOOKUP types path = SOME ty ==>
      ALOOKUP ctx.sm_bindings path = SOME (SE_Runtime (Name ty (LAST path))))
End

Theorem source_meaning_locals_types:
  source_meaning_locals types ctx ==>
  source_meaning_binding_types types ctx.sm_bindings
Proof
  rw[source_meaning_locals_def, source_meaning_binding_types_def] >>
  first_x_assum drule >> strip_tac >> simp[expr_type_def]
QED

Theorem source_meaning_locals_agree:
  source_meaning_locals types ctx ==>
  !path code ty. ALOOKUP types path = SOME ty /\
    ALOOKUP ctx.sm_bindings path = SOME (SE_Runtime code) ==>
    eval_expr cx code = source_meaning_local (LAST path)
Proof
  rw[source_meaning_locals_def] >> res_tac >> gvs[source_meaning_local_agreement]
QED

Theorem source_meaning_locals_extend:
  source_meaning_locals types ctx ==>
  source_meaning_locals ((ctx.sm_owner ++ [name],ty)::types)
    (source_module_local ctx name ty T)
Proof
  rw[source_meaning_locals_def, source_module_local_def, AllCaseEqs()] >>
  gvs[] >> metis_tac[]
QED

Theorem source_meaning_local_tenv:
  (source_module_local ctx name ty assignable).sm_env.type_defs = ctx.sm_env.type_defs
Proof
  simp[source_module_local_def, extend_local_def]
QED

Theorem source_meaning_expression_transport:
  source_meaning_source types ctx.sm_scopes ctx.sm_table ctx.sm_constants ty original m /\
  source_meaning_locals types ctx /\
  source_module_expression fuel ctx ty original = SM_Ok e /\
  get_tenv cx = ctx.sm_env.type_defs ==>
  eval_expr cx e = source_meaning_eval cx (\path. source_meaning_local (LAST path)) m
Proof
  simp[source_module_expression_def] >> strip_tac >>
  Cases_on `source_expr_elaborate fuel ctx.sm_env ctx.sm_scopes ctx.sm_table
    ctx.sm_constants ctx.sm_bindings ty original` >>
  gvs[source_module_expr_result_def] >>
  drule source_meaning_locals_types >> strip_tac >>
  irule source_meaning_elaboration_sound_on >>
  qexistsl_tac [`ctx.sm_bindings`, `ctx.sm_constants`, `ctx.sm_env`, `fuel`, `original`,
    `ctx.sm_scopes`, `ctx.sm_table`, `ty`, `types`] >> simp[] >>
  rpt strip_tac >> drule_all source_meaning_source_names >> strip_tac >>
  Cases_on `ALOOKUP types path` >> gvs[] >>
  drule_all source_meaning_locals_agree >> simp[]
QED

Theorem source_meaning_name_binding:
  source_meaning_locals types ctx /\
  source_resolve_name ctx.sm_scopes ctx.sm_table [name] = SOME (path,SR_Dynamic) /\
  ALOOKUP types path = SOME ty ==>
  source_expr_variable ctx.sm_scopes ctx.sm_table ctx.sm_bindings (SX_Name name) =
    SOME (Name ty (LAST path))
Proof
  rw[source_meaning_locals_def, source_expr_variable_def, source_expr_path_def] >>
  res_tac >> simp[]
QED

Theorem source_meaning_name_hint:
  source_meaning_locals types ctx /\
  source_resolve_name ctx.sm_scopes ctx.sm_table [name] = SOME (path,SR_Dynamic) /\
  ALOOKUP types path = SOME ty ==>
  source_expr_hint ctx.sm_scopes ctx.sm_table ctx.sm_constants ctx.sm_bindings
    (SX_Name name) = SOME ty
Proof
  strip_tac >> drule_all source_meaning_name_binding >> strip_tac >>
  simp[source_expr_hint_def, expr_type_def]
QED

Theorem source_meaning_expression_type:
  source_module_expression fuel ctx ty original = SM_Ok e ==> expr_type e = ty
Proof
  simp[source_module_expression_def] >>
  Cases_on `source_expr_elaborate fuel ctx.sm_env ctx.sm_scopes ctx.sm_table
    ctx.sm_constants ctx.sm_bindings ty original` >>
  simp[source_module_expr_result_def] >> strip_tac >> gvs[] >>
  drule source_expr_elaborate_typed >> simp[]
QED

Theorem source_meaning_bind_success:
  source_module_bind r f = SM_Ok z <=> ?x. r = SM_Ok x /\ f x = SM_Ok z
Proof
  Cases_on `r` >> simp[source_module_bind_def]
QED

Theorem source_meaning_bind_pair_success:
  source_module_bind r (\(a,b). f a b) = SM_Ok z <=>
    ?a b. r = SM_Ok (a,b) /\ f a b = SM_Ok z
Proof
  simp[source_meaning_bind_success, pairTheory.EXISTS_PROD]
QED

(* Successful elaboration now transports a recursively derived ORIGINAL body,
   including context extension, not just a pair of related runtime ASTs. *)
Theorem source_meaning_body_transport:
  (!types ctx ret s m next_types next.
    source_meaning_body types ctx ret s m next_types next ==>
    !fuel code final cx.
      source_meaning_locals types ctx /\ get_tenv cx = ctx.sm_env.type_defs /\
      source_module_statement fuel ctx ret s = SM_Ok (code,final) ==>
      final = next /\ source_meaning_locals next_types next /\
      get_tenv cx = next.sm_env.type_defs /\
      eval_stmt cx code = source_meaning_run cx (\p. source_meaning_local (LAST p)) m) /\
  (!types ctx ret ss ms next_types next.
    source_meaning_bodies types ctx ret ss ms next_types next ==>
    !fuel code final cx.
      source_meaning_locals types ctx /\ get_tenv cx = ctx.sm_env.type_defs /\
      source_module_statements fuel ctx ret ss = SM_Ok (code,final) ==>
      final = next /\ source_meaning_locals next_types next /\
      get_tenv cx = next.sm_env.type_defs /\
      eval_stmts cx code = source_meaning_runs cx (\p. source_meaning_local (LAST p)) ms)
Proof
  CONV_TAC (REWR_CONV CONJ_COMM) >>
  ho_match_mp_tac source_meaning_body_ind >> rpt conj_tac >>
  rpt (gen_tac ORELSE (disch_then strip_assume_tac))
  >- (Cases_on `fuel` >> gvs[Once source_module_statements_def] >>
      simp[Once evaluate_def, source_meaning_run_def])
  >- (Cases_on `fuel` >> gvs[Once source_module_statements_def,
        source_meaning_bind_pair_success, AllCaseEqs()] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      simp[Once evaluate_def, source_meaning_run_def])
  >- (Cases_on `fuel` >> gvs[Once source_module_statements_def] >>
      simp[Once evaluate_def, source_meaning_run_def])
  >- (Cases_on `fuel` >> gvs[Once source_module_statements_def] >>
      simp[Once evaluate_def, source_meaning_run_def])
  >- (Cases_on `fuel` >> gvs[Once source_module_statements_def,
        source_meaning_bind_success, AllCaseEqs()] >>
      drule_all source_meaning_expression_transport >> strip_tac >>
      simp[Once evaluate_def, source_meaning_run_def])
  >- (Cases_on `fuel` >> gvs[Once source_module_statements_def,
        source_meaning_bind_success, AllCaseEqs()] >>
      drule_all source_meaning_expression_transport >> strip_tac >>
      simp[source_module_annotated_local_def] >>
      simp[source_meaning_locals_extend, source_meaning_local_tenv] >>
      simp[Once evaluate_def, source_meaning_run_def])
  >- (drule_all source_meaning_name_binding >> strip_tac >>
      drule_all source_meaning_name_hint >> strip_tac >>
      Cases_on `fuel` >> gvs[Once source_module_statements_def,
        source_module_infer_def, source_meaning_bind_success, AllCaseEqs()] >>
      qpat_x_assum `source_expr_infer _ _ _ _ _ _ _ = _`
        (fn th => mp_tac th) >>
      rename1 `source_module_target remaining ctx _ = _` >>
      Cases_on `remaining` >> simp[source_expr_infer_def] >> strip_tac >> gvs[] >>
      imp_res_tac source_meaning_expression_type >>
      gvs[source_module_target_def, source_module_bind_def, expr_type_def, AllCaseEqs()] >>
      drule_all source_meaning_expression_transport >> strip_tac >>
      simp[evaluate_def, source_meaning_run_def, FUN_EQ_THM,
        bind_def, ignore_bind_def, return_def, get_scopes_def,
        type_check_def, assert_def, raise_def] >>
      rpt gen_tac >> rpt (pop_assum kall_tac) >>
      Cases_on `IS_SOME (lookup_scopes (LAST path) x.scopes)` >> simp[return_def])
  >> qpat_x_assum `source_module_statement _ _ _ _ = _` mp_tac >>
  Cases_on `fuel` >> simp_tac (srw_ss()) [Once source_module_statements_def,
    source_meaning_bind_pair_success, source_meaning_bind_success] >>
  strip_tac >> gvs[] >>
  drule_all source_meaning_expression_transport >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once evaluate_def, source_meaning_run_def]
QED
