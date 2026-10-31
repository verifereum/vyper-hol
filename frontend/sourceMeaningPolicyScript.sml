Theory sourceMeaningPolicy
Ancestors
  sourceMeaningProgram sourceMeaningProgramDefs sourceMeaningRuntime sourceMeaningDefs
  sourceMeaningConst sourceMeaningValue sourceMeaningStmt sourceMeaningStmtDefs
  sourceModuleContext sourceModuleStmt sourceModuleElaborate
  sourceModuleDecl sourceModuleDefs sourceResolveModules sourceResolve sourceSyntax
  sourceConstEnv sourceExprDefs vyperInterpreter vyperState vyperContext vyperAST alist list pair

Theorem source_meaning_retained_modules:
  SourceRetained program modules = retained ==> retained_executable retained = modules
Proof
  strip_tac >> gvs[retained_executable_def]
QED

(* Public, policy-aware phase. Constants have a finite ORIGINAL-source
   dependency derivation even when modules have interfaces/export overrides.
   Nothing assumes the policy-free helper was the phase actually executed. *)
Theorem source_meaning_policy_elaborate_member:
  source_module_elaborate fuel trust policies keys program = SM_Ok retained ==>
  retained_source retained = program /\
  ?registry constants exports links signatures.
    source_resolve_program_registry program keys = SOME registry /\
    source_meaning_constants registry constants /\
    source_module_link trust registry constants = SOME exports /\
    source_module_policy_overrides trust policies registry constants = SOME links /\
    source_module_policy_link_ok trust policies exports /\
    source_module_policy_signature_modules fuel trust policies registry constants = SM_Ok signatures /\
    !owner syntax. MEM (owner,syntax) registry ==>
    ?bindings src tops.
      source_module_override_bindings trust links
        (source_module_policy_signature_context trust policies registry constants signatures owner syntax).sm_bindings =
          SOME bindings /\
      source_module_policy_bodies fuel
        ((source_module_policy_signature_context trust policies registry constants signatures owner syntax)
          with sm_bindings := bindings) trust.smt_slots
        (source_module_policy_for policies owner) syntax = SM_Ok tops /\
      MEM (src,tops) (retained_executable retained)
Proof
  strip_tac >> drule source_module_elaborate_retains_source >> strip_tac >> simp[] >>
  qpat_x_assum `source_module_elaborate _ _ _ _ _ = _` mp_tac >>
  simp[source_module_elaborate_def, source_meaning_bind_success,
    pairTheory.EXISTS_PROD] >> strip_tac >>
  drule source_module_link_program_equations >> strip_tac >>
  drule source_meaning_program_constants_transport >> strip_tac >>
  gvs[source_module_policy_elaborate_registry_def, source_meaning_bind_success, AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `source_module_policy_signature_modules _ _ _ module_registry constant_env = SM_Ok sigs` >>
  qmatch_asmsub_rename_tac `source_module_policy_overrides _ _ _ _ = SOME overrides` >>
  qmatch_asmsub_rename_tac `source_module_link _ _ _ = SOME exps` >>
  qexistsl_tac [`constant_env`,`exps`,`overrides`,`sigs`] >>
  simp[retained_executable_def] >> rpt strip_tac >>
  drule_all source_meaning_collect_member >> strip_tac >>
  gvs[source_meaning_bind_success, AllCaseEqs()] >>
  drule source_meaning_retained_modules >> simp[] >> metis_tac[]
QED

Theorem source_meaning_simple_constants_exist:
  source_module_elaborate_simple fuel trust keys program = SM_Ok retained ==>
  ?registry constants.
    source_resolve_program_registry program keys = SOME registry /\
    source_meaning_constants registry constants
Proof
  strip_tac >> drule source_meaning_elaborate_member >> metis_tac[]
QED

(* Exact staged subdomain, not a readiness premise: every original constant
   initializer (including imported dependencies) has a mathematical value.
   Whenever the expression phase accepts that initializer at a requested type,
   a source meaning and its all-state denotation EXIST; no derivation is supplied
   by the caller. This is not a whole-function or dispatch completeness claim. *)
Theorem source_meaning_initializer_exists:
  source_meaning_constants registry constants /\
  MEM (owner,syntax) registry /\
  MEM (path,original) (source_resolve_initializers owner syntax) /\
  source_expr_elaborate fuel env
    [source_resolve_module_scope owner syntax; source_resolve_prelude_scope]
    (source_resolve_table registry) constants bindings ty original = SC_Value e ==>
  ?sv m v.
    ALOOKUP constants path = SOME (SC_Constant sv) /\
    source_meaning_source types
      [source_resolve_module_scope owner syntax; source_resolve_prelude_scope]
      (source_resolve_table registry) constants ty original m /\
    source_meaning_value env.type_defs ty sv = SOME v /\
    (!cx meanings st. get_tenv cx = env.type_defs ==>
      source_meaning_eval cx meanings m st = (INL (Value v),st) /\
      eval_expr cx e st = (INL (Value v),st))
Proof
  simp[source_meaning_constants_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `source_meaning_stage
    [source_resolve_module_scope owner syntax; source_resolve_prelude_scope]
    (source_resolve_table registry) constants original (SC_Value value)` by
      (simp[source_meaning_stage_def] >> metis_tac[]) >>
  drule_all source_meaning_constant_exists >> metis_tac[]
QED

Theorem source_meaning_return_transport:
  source_meaning_source types ctx.sm_scopes ctx.sm_table ctx.sm_constants ty original m /\
  source_meaning_locals types ctx /\
  source_module_expression fuel ctx ty original = SM_Ok e ==>
  !cx. get_tenv cx = ctx.sm_env.type_defs ==>
    eval_stmts cx [Return (SOME e)] =
      source_meaning_execute cx [SBM_Return (SOME m)]
Proof
  rpt strip_tac >> drule_all source_meaning_expression_transport >> strip_tac >>
  simp[source_meaning_execute_def, source_meaning_run_def, Once evaluate_def] >>
  simp[Once evaluate_def] >> simp[Once evaluate_def]
QED

(* A genuine executable staged subdomain with no supplied source derivation:
   a successful return of a mathematically constant original expression.
   The child may be an aggregate or a resolved imported dependency. *)
Theorem source_meaning_constant_return_exists:
  source_meaning_stage ctx.sm_scopes ctx.sm_table ctx.sm_constants original (SC_Value sv) /\
  source_module_expression fuel ctx ty original = SM_Ok e ==>
  ?m v. source_meaning_bodies [] ctx ty [SS_Return (SOME original)]
      [SBM_Return (SOME m)] [] ctx /\
    source_meaning_value ctx.sm_env.type_defs ty sv = SOME v /\
    (!cx st. get_tenv cx = ctx.sm_env.type_defs ==>
      eval_stmts cx [Return (SOME e)] st =
        (INR (ReturnException v),st) /\
      source_meaning_execute cx [SBM_Return (SOME m)] st =
        (INR (ReturnException v),st))
Proof
  simp[source_module_expression_def] >> strip_tac >>
  Cases_on `source_expr_elaborate fuel ctx.sm_env ctx.sm_scopes ctx.sm_table
    ctx.sm_constants ctx.sm_bindings ty original` >>
  gvs[source_module_expr_result_def] >>
  drule_all source_meaning_constant_exists >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  qexistsl_tac [`m`,`v`] >> simp[] >> conj_tac
  >- (irule sourceMeaningStmtDefsTheory.cons >> qexistsl_tac [`ctx`,`[]`] >>
      simp[sourceMeaningStmtDefsTheory.empty] >>
      irule sourceMeaningStmtDefsTheory.return_value >> simp[]) >>
  rpt strip_tac >>
  simp[source_meaning_execute_def, source_meaning_run_def, Once evaluate_def,
    bind_def, ignore_bind_def, return_def, raise_def, read_result_def] >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, read_result_def]
QED
