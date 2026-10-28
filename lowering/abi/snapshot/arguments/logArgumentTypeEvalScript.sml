(* TOP-LEVEL: checked expressions have evaluable result types in a
   consistent source environment, independently of their execution. *)
Theory logArgumentTypeEval
Ancestors
  vyperTypeSystem vyperTypeInvariants vyperTypeEnv vyperTypeBuiltins
  vyperAST vyperValue vyperState vyperContext list option finite_map

Theorem consistent_variable_type_well_formed:
  !env cx st id ty.
    env_consistent env cx st /\ FLOOKUP env.var_types id = SOME ty ==>
    well_formed_type env.type_defs ty
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  fs[env_consistent_def, env_scopes_consistent_def] >>
  `?entry. lookup_scopes id st.scopes = SOME entry` by
    (qpat_x_assum `!id ty. FLOOKUP _ _ = SOME _ ==> IS_SOME _`
       (qspecl_then [`id`, `ty`] mp_tac) >> simp[IS_SOME_EXISTS]) >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    (first_x_assum irule >> qexists_tac `id` >> simp[]) >>
  simp[well_formed_type_def]
QED

Theorem well_formed_array_element:
  !tenv ty bd. well_formed_type tenv (ArrayT ty bd) ==> well_formed_type tenv ty
Proof
  rpt gen_tac >> Cases_on `evaluate_type tenv ty` >>
  simp[well_formed_type_def, Once evaluate_type_def]
QED

Theorem checked_pop_type_well_formed:
  !env ty target.
    well_typed_expr env (Pop ty target) ==> well_formed_type env.type_defs ty
Proof
  rpt gen_tac >> simp_tac bool_ss [Once well_typed_expr_def] >> strip_tac >>
  drule_all assignable_type_well_formed >> DISCH_TAC >>
  drule_all well_formed_array_element >> simp[]
QED

Theorem checked_call_type_well_formed:
  !env ty target args drv.
    well_typed_expr env (Call ty target args drv) ==> well_formed_type env.type_defs ty
Proof
  rpt gen_tac >> Cases_on `target` >|
   [rename1 `IntCall nsid` >> PairCases_on `nsid` >> simp[Once well_typed_expr_def],
    rename1 `ExtCall static_flag skip_flag signature` >> PairCases_on `signature` >>
      simp[Once well_typed_expr_def],
    simp[Once well_typed_expr_def, well_formed_type_def, Once evaluate_type_def],
    simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >>
      irule raw_call_return_type_well_formed >> first_assum MATCH_ACCEPT_TAC,
    simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >>
      irule raw_call_return_type_well_formed >> first_assum MATCH_ACCEPT_TAC,
    simp[Once well_typed_expr_def, well_formed_type_def, Once evaluate_type_def],
    simp[Once well_typed_expr_def, well_formed_type_def, Once evaluate_type_def],
    simp[Once well_typed_expr_def, well_formed_type_def, Once evaluate_type_def],
    simp[Once well_typed_expr_def, well_formed_type_def, Once evaluate_type_def]]
QED

Theorem checked_expr_type_well_formed:
  !env cx st e.
    env_consistent env cx st /\ well_typed_expr env e ==>
    well_formed_type env.type_defs (expr_type e)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `e` >> simp_tac bool_ss [expr_type_def] >>
  FIRST
   [drule_all checked_pop_type_well_formed >> simp[],
    drule_all checked_call_type_well_formed >> simp[],
    drule_all TopLevelName_well_formed_type >> simp[],
    qpat_x_assum `well_typed_expr env _` mp_tac >>
      simp_tac bool_ss [Once well_typed_expr_def] >> strip_tac >>
      FIRST [first_assum MATCH_ACCEPT_TAC,
        drule_all consistent_variable_type_well_formed >> simp[]]]
QED

Theorem checked_exprs_type_evaluations:
  !args env cx st.
    env_consistent env cx st /\ well_typed_exprs env args ==>
    ?tvs. LIST_REL (\e tv. evaluate_type env.type_defs (expr_type e) = SOME tv) args tvs
Proof
  Induct_on `args` >- simp[] >> rpt gen_tac >>
  rename1 `well_typed_exprs env (e::rest)` >>
  simp_tac bool_ss [Once well_typed_expr_def] >> strip_tac >>
  `well_formed_type env.type_defs (expr_type e)` by
    (drule_all checked_expr_type_well_formed >> simp[]) >>
  qpat_x_assum `well_formed_type _ _`
    (mp_tac o REWRITE_RULE [well_formed_type_def, IS_SOME_EXISTS]) >>
  disch_then (qx_choose_then `tv` ASSUME_TAC) >>
  first_x_assum drule_all >> disch_then (qx_choose_then `tvs` ASSUME_TAC) >>
  qexists_tac `tv::tvs` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked Log argument type evaluation: " ^ name)
  end) (DB.thms "logArgumentTypeEval")
