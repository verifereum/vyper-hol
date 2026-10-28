Theory sourceExprProps
Ancestors
  sourceExprElaborate sourceExprDefs sourceConstValueProps sourceConstValue
  sourceConstValueStructured sourceConstValueStructuredProps finite_map
  sourceResolve sourceSyntax sourceConstEval sourceTypeResolve vyperTypeSystem
  vyperInterpreter vyperState vyperAST vyperValue vyperTyping alist

(* The last Boolean operand is returned unchanged: no synthetic test/rebuild
   of its value, and no duplicate evaluation even when it has effects. *)
Theorem source_expr_boolean_runtime_singleton:
  source_expr_boolean_runtime op [e] = e
Proof
  simp[source_expr_boolean_runtime_def]
QED

Theorem source_expr_boolean_runtime_pair:
  source_expr_boolean_runtime SCB_And [left;right] =
    IfExp (BaseT BoolT) left right (Literal (BaseT BoolT) (BoolL F)) /\
  source_expr_boolean_runtime SCB_Or [left;right] =
    IfExp (BaseT BoolT) left (Literal (BaseT BoolT) (BoolL T)) right
Proof
  simp[source_expr_boolean_runtime_def]
QED

Theorem source_expr_checked_value:
  source_expr_checked env ty before = SC_Value after <=>
  before = after /\ expr_type after = ty /\ well_typed_expr env after
Proof
  rw[source_expr_checked_def] >> metis_tac[]
QED

(* No readiness or successful-runtime-check premise: it is a consequence of
   executing the API, including when the result contains runtime names. *)
Theorem source_expr_elaborate_typed:
  source_expr_elaborate fuel env scopes table constants variables ty original = SC_Value e ==>
  expr_type e = ty /\ well_typed_expr env e
Proof
  simp[source_expr_elaborate_def] >>
  Cases_on `source_expr_build fuel env scopes table constants variables ty original` >>
  simp[source_const_then_def, source_expr_checked_value]
QED

Theorem source_expr_elaborate_build:
  source_expr_elaborate fuel env scopes table constants variables ty original = SC_Value e ==>
  source_expr_build fuel env scopes table constants variables ty original = SC_Value e
Proof
  simp[source_expr_elaborate_def] >>
  Cases_on `source_expr_build fuel env scopes table constants variables ty original` >>
  simp[source_const_then_def, source_expr_checked_value]
QED

(* These domain facts are derived from the original source constructor even
   when the emitted runtime expression is just a literal. *)
Theorem source_expr_original_binary_validated:
  source_expr_elaborate fuel env scopes table constants variables ty
    (SX_Binary op left right) = SC_Value e ==>
  source_expr_binary_domain op ty
Proof
  strip_tac >> drule source_expr_elaborate_build >> strip_tac >>
  Cases_on `source_expr_binary_domain op ty` >> gvs[] >>
  Cases_on `fuel` >> gvs[Once source_expr_build_def, AllCaseEqs(),
    source_resolve_candidate_def, source_constant_candidate_def,
    source_resolve_expr_def, source_resolve_two_def, source_const_then_def,
    Once source_expr_original_def]
QED

Theorem source_expr_original_unary_validated:
  source_expr_elaborate fuel env scopes table constants variables ty
    (SX_Unary op child) = SC_Value e ==>
  source_expr_unary_domain op ty \/
  (op = SCU_Neg /\ is_int_type ty /\ ?resolved.
    source_resolve_candidate scopes table (SX_Unary op child) = SOME resolved /\
    source_const_eval constants resolved = SC_Value (SCV_Int 0))
Proof
  strip_tac >> drule source_expr_elaborate_build >> strip_tac >>
  Cases_on `source_expr_unary_domain op ty` >> gvs[] >>
  Cases_on `fuel` >> gvs[Once source_expr_build_def, AllCaseEqs(),
    source_resolve_candidate_def, source_constant_candidate_def,
    source_resolve_expr_def, optionTheory.OPTION_MAP_EQ_SOME, source_const_then_def,
    Once source_expr_original_def] >> metis_tac[]
QED

Theorem source_expr_reify_value:
  source_expr_reify env ty sv = SC_Value e ==>
  sourceConstValueStructured$source_const_reify FEMPTY env.type_defs ty sv = SOME e
Proof
  simp[source_expr_reify_def, AllCaseEqs(), source_expr_checked_value] >>
  rpt strip_tac >> gvs[]
QED

(* Every constant erased by the public entry has original-tree evidence,
   independently of the emitted literal/aggregate and its runtime checker. *)
Theorem source_expr_constant_replacement_validated:
  source_expr_elaborate fuel env scopes table constants bindings ty original = SC_Value e /\
  source_resolve_candidate scopes table original = SOME resolved /\
  source_const_eval constants resolved = SC_Value sv ==>
  source_expr_original fuel env.type_defs constants T ty resolved /\
  sourceConstValueStructured$source_const_reify FEMPTY env.type_defs ty sv = SOME e
Proof
  strip_tac >> drule source_expr_elaborate_build >> strip_tac >>
  Cases_on `fuel` >> gvs[Once source_expr_build_def, AllCaseEqs()] >>
  drule source_expr_reify_value >> simp[]
QED

Theorem source_expr_elaborate_constant_evaluates:
  source_expr_elaborate fuel env scopes table constants bindings ty original = SC_Value e /\
  source_resolve_candidate scopes table original = SOME resolved /\
  source_const_eval constants resolved = SC_Value sv ==>
  ?tv v. evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v /\
    source_const_structured_represents FEMPTY sv v /\
    (!cx st. get_tenv cx = env.type_defs ==> eval_expr cx e st = (INL (Value v),st))
Proof
  strip_tac >> drule_all source_expr_constant_replacement_validated >> strip_tac >>
  drule sourceConstValueStructuredPropsTheory.source_const_reify_sound >> simp[]
QED

(* Local replacement theorem. Validating the ORIGINAL application is logically
   prior to folding, and its evidence is retained in this conclusion. *)
Theorem source_expr_finish_cases:
  source_expr_finish env constants ty resolved before = SC_Value after ==>
  expr_type before = ty /\ well_typed_expr env before /\
  ((source_const_eval constants resolved = SC_NotConstant /\ after = before) \/
   ?sv. source_const_eval constants resolved = SC_Value sv /\
        sourceConstValueStructured$source_const_reify FEMPTY env.type_defs ty sv = SOME after)
Proof
  simp[source_expr_finish_def] >>
  Cases_on `source_expr_checked env ty before` >>
  simp[source_const_then_def] >>
  Cases_on `source_const_eval constants resolved` >>
  simp[source_expr_checked_value] >> rpt strip_tac >>
  gvs[source_expr_checked_value] >>
  drule source_expr_reify_value >> simp[]
QED

Theorem source_expr_finish_constant_evaluates:
  source_expr_finish env constants ty resolved before = SC_Value after /\
  source_const_eval constants resolved = SC_Value sv ==>
  ?tv v. evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v /\
         source_const_structured_represents FEMPTY sv v /\
         (!cx st. get_tenv cx = env.type_defs ==>
            eval_expr cx after st = (INL (Value v),st))
Proof
  strip_tac >> drule source_expr_finish_cases >> strip_tac >> gvs[] >>
  drule sourceConstValueStructuredPropsTheory.source_const_reify_sound >> simp[]
QED

Theorem source_expr_finish_dynamic_identity:
  source_expr_finish env constants ty resolved before = SC_Value after /\
  source_const_eval constants resolved = SC_NotConstant ==>
  after = before /\ (!cx st. eval_expr cx after st = eval_expr cx before st)
Proof
  strip_tac >> drule source_expr_finish_cases >> simp[]
QED

Theorem source_expr_required_from_original:
  source_expr_required fuel tenv scopes table constants ty original = SC_Value sv ==>
  ?resolved.
    source_resolve_candidate scopes table original = SOME resolved /\
    source_const_eval constants resolved = SC_Value sv /\
    source_expr_original fuel tenv constants T ty resolved /\
    source_expr_fits tenv ty sv
Proof
  simp[source_expr_required_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem source_expr_keyword_bool_present_from_original:
  source_expr_keyword_bool fuel tenv scopes table constants keywords key default = SC_Value flag /\
  ALOOKUP keywords key = SOME original ==>
  ?resolved. source_resolve_candidate scopes table original = SOME resolved /\
    source_const_eval constants resolved = SC_Value (SCV_Bool flag) /\
    source_expr_original fuel tenv constants T (BaseT BoolT) resolved
Proof
  strip_tac >>
  gvs[source_expr_keyword_bool_def, source_const_then_def, AllCaseEqs()] >>
  drule source_expr_required_from_original >> strip_tac >> gvs[]
QED

Theorem source_expr_constant_from_original:
  source_expr_constant fuel env scopes table constants variables ty original = SC_Value sv ==>
  ?resolved.
    source_resolve_candidate scopes table original = SOME resolved /\
    source_const_eval constants resolved = SC_Value sv /\
    source_expr_original fuel env.type_defs constants T ty resolved /\
    source_expr_fits env.type_defs ty sv
Proof
  simp[source_expr_constant_def, source_expr_required_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem source_expr_flag_from_original:
  source_expr_flag fuel env scopes table constants variables original = SC_Value flag ==>
  ?resolved. source_resolve_candidate scopes table original = SOME resolved /\
    source_const_eval constants resolved = SC_Value (SCV_Bool flag)
Proof
  simp[source_expr_flag_def] >>
  Cases_on `source_expr_constant fuel env scopes table constants variables (BaseT BoolT) original` >>
  simp[source_const_then_def] >>
  rename1 `source_expr_constant fuel env scopes table constants variables (BaseT BoolT) original = SC_Value sv` >>
  Cases_on `sv` >> simp[] >> strip_tac >>
  drule source_expr_constant_from_original >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem source_expr_index_from_original:
  source_expr_index fuel env scopes table constants variables length_limit original = SC_Value index ==>
  index < length_limit /\ ?resolved i.
    source_resolve_candidate scopes table original = SOME resolved /\
    source_const_eval constants resolved = SC_Value (SCV_Int i) /\
    0 <= i /\ index = Num i
Proof
  simp[source_expr_index_def] >>
  Cases_on `source_expr_constant fuel env scopes table constants variables (BaseT (UintT 256)) original` >>
  simp[source_const_then_def] >>
  rename1 `source_expr_constant fuel env scopes table constants variables (BaseT (UintT 256)) original = SC_Value sv` >>
  Cases_on `sv` >> simp[] >> strip_tac >>
  drule source_expr_constant_from_original >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem source_expr_range_bound_from_original:
  source_expr_range_bound fuel env scopes table constants variables original = SC_Value bound ==>
  ?resolved i. source_resolve_candidate scopes table original = SOME resolved /\
    source_const_eval constants resolved = SC_Value (SCV_Int i) /\
    0 < i /\ i < &(2 ** 256) /\ bound = Num i
Proof
  simp[source_expr_range_bound_def] >>
  Cases_on `source_expr_constant fuel env scopes table constants variables (BaseT (UintT 256)) original` >>
  simp[source_const_then_def] >>
  rename1 `source_expr_constant fuel env scopes table constants variables (BaseT (UintT 256)) original = SC_Value sv` >>
  Cases_on `sv` >> simp[] >> strip_tac >>
  drule source_expr_constant_from_original >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED
