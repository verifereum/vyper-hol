Theory sourceMeaningRuntime
Ancestors
  sourceMeaningEffects sourceMeaningElaborate sourceMeaningCode sourceMeaningDefs
  sourceMeaningConst sourceMeaningValue sourceExprProps sourceExprDefs sourceConstEnvProps sourceConstEnv
  sourceConstValue sourceConstValueProps sourceConstValueStructured
  sourceConstValueStructuredProps sourceConstEval sourceResolve sourceSyntax
  vyperInterpreter vyperState vyperContext vyperValueOperation vyperAST vyperValue alist

(* Independent local-name denotation, without constructing/evaluating a runtime
   AST. Capture the cell now; consumers choose when to read its value. *)
Definition source_meaning_local_def:
  source_meaning_local id = do
    scopes <- get_scopes;
    type_check (IS_SOME (lookup_scopes id scopes)) "Name not in scope";
    return (PlaceR (MemoryPlace id []))
  od
End

Theorem source_meaning_local_agreement:
  eval_expr cx (Name ty id) = source_meaning_local id
Proof
  simp[Once evaluate_def, source_meaning_local_def]
QED

Theorem source_meaning_name_substitution:
  source_resolve_name scopes table [name] = SOME (path,SR_Constant) /\
  ALOOKUP constants path = SOME (SC_Constant value) /\ source_const_value_ok value ==>
  source_meaning_stage scopes table constants (SX_Name name) (SC_Value value)
Proof
  simp[source_meaning_stage_def, source_resolve_candidate_def,
    source_constant_candidate_def, source_resolve_expr_def, source_resolve_atom_def,
    source_meaning_const_def, source_const_lookup_def]
QED

Theorem source_meaning_eval_environment_transport:
  !m. (!path. meanings path = other path) ==>
    source_meaning_eval cx meanings m = source_meaning_eval cx other m
Proof
  Induct >> simp[source_meaning_eval_def]
QED

(* Module/declaration transport available without pretending to prove statements
   or module execution: resolved constant initializers retain their independent
   mathematical denotations in the successfully constructed environment. *)
Theorem source_meaning_initializer_transport:
  source_const_resolve seed declarations = SCEnv_Resolved constants ==>
  !path original. MEM (path,original) declarations ==>
    ?v. ALOOKUP constants path = SOME (SC_Constant v) /\
        source_meaning_const constants original = SC_Value v
Proof
  simp[GSYM source_meaning_const_correct] >>
  strip_tac >> drule source_const_resolve_initializer_values >> simp[]
QED

(* A deliberately small arithmetic compatibility bridge. The mathematical
   source stage does NOT have this width bound; the runtime stage DOES. No
   Decimal/context or power equivalence is inferred from integer addition. *)
Theorem source_meaning_add_runtime:
  type_to_int_bound ty = SOME bound /\ within_int_bound bound (a + b) ==>
  !cx meanings st.
    source_meaning_eval cx meanings
      (SM_Binary ty SCB_Add (SM_Literal ty (IntL a)) (SM_Literal ty (IntL b))) st =
    (INL (Value (IntV (a + b))),st)
Proof
  simp[source_meaning_eval_def, source_meaning_type_def, source_meaning_apply_def,
       source_meaning_args_def, source_expr_binary_def,
       builtin_args_length_ok_def, evaluate_literal_def, read_result_def,
       evaluate_builtin_def, evaluate_binop_def, bounded_int_op_def,
       bind_def, ignore_bind_def, return_def, get_accounts_def, lift_sum_def,
       type_check_def, assert_def]
QED

Theorem source_meaning_add_replacement:
  type_to_int_bound ty = SOME bound /\ within_int_bound bound (a + b) /\
  source_expr_reify env ty (SCV_Int (a + b)) = SC_Value after /\
  get_tenv cx = env.type_defs ==>
  !st. eval_expr cx (Builtin ty (Bop Add) [Literal ty (IntL a);Literal ty (IntL b)]) st =
       eval_expr cx after st
Proof
  strip_tac >> drule source_expr_reify_value >> strip_tac >>
  `source_const_value_literal (SCV_Int (a + b)) = SOME (IntL (a + b))` by
    simp[source_const_value_literal_def] >>
  drule_all source_meaning_reify_evaluates >> strip_tac >>
  simp[evaluate_def, expr_type_def, builtin_args_length_ok_def,
       evaluate_literal_def, read_result_def, evaluate_builtin_def,
       evaluate_binop_def, bounded_int_op_def, bind_def, ignore_bind_def,
       return_def, get_accounts_def, lift_sum_def, type_check_def, assert_def]
QED

(* Direct scalar staging/reification: the semantic term is obtained from the
   original source rule, not extracted from the elaborator's result. *)
Theorem source_meaning_constant_evaluation:
  source_meaning_stage scopes table constants original (SC_Value sv) /\
  source_const_value_literal sv = SOME lit /\
  source_expr_elaborate fuel env scopes table constants bindings ty original = SC_Value e /\
  get_tenv cx = env.type_defs ==>
  source_meaning_source types scopes table constants ty original (SM_Literal ty lit) /\
  (!st. eval_expr cx e st = (INL (Value (evaluate_literal lit)),st))
Proof
  strip_tac >> conj_tac
  >- (irule sourceMeaningDefsTheory.constant >> metis_tac[]) >>
  drule source_expr_elaborate_build >> strip_tac >>
  drule_all source_meaning_build_constant >> strip_tac >>
  irule source_meaning_reify_evaluates >> metis_tac[]
QED

(* No independent-derivation premise: successful constant elaboration constructs
   a source meaning, including nested tuple/array results and imported names. *)
Theorem source_meaning_constant_exists:
  source_meaning_stage scopes table constants original (SC_Value sv) /\
  source_expr_elaborate fuel env scopes table constants bindings ty original = SC_Value e ==>
  ?m v. source_meaning_source types scopes table constants ty original m /\
    source_meaning_value env.type_defs ty sv = SOME v /\
    (!cx meanings st. get_tenv cx = env.type_defs ==>
      source_meaning_eval cx meanings m st = (INL (Value v),st) /\
      eval_expr cx e st = (INL (Value v),st))
Proof
  strip_tac >> drule source_expr_elaborate_build >> strip_tac >>
  drule_all source_meaning_build_constant >> strip_tac >>
  drule source_meaning_value_reify >> strip_tac >>
  Cases_on `source_const_value_literal sv`
  >- (qexistsl_tac [`SM_Constant ty sv`,`v`] >>
      simp[source_meaning_eval_def, lift_option_type_def, lift_option_def,
        bind_def, return_def] >> irule sourceMeaningDefsTheory.aggregate >> metis_tac[]) >>
  rename1 `source_const_value_literal sv = SOME lit` >>
  `source_meaning_value env.type_defs ty sv = SOME (evaluate_literal lit)` by
    (Cases_on `sv` >> gvs[source_const_value_literal_def, source_meaning_value_def]) >>
  gvs[] >> qexists_tac `SM_Literal (expr_type e) lit` >>
  simp[source_meaning_eval_def, return_def] >>
  irule sourceMeaningDefsTheory.constant >> metis_tac[]
QED
