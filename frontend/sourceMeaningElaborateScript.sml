Theory sourceMeaningElaborate
Ancestors
  sourceMeaningCode sourceMeaningDefs sourceMeaningConst sourceExprProps
  sourceExprElaborate sourceExprDefs sourceResolve sourceSyntax sourceConstEval
  sourceConstEvalProps sourceConstValueStructured sourceConstValue
  vyperInterpreter vyperAST vyperState vyperContext alist finite_map list

(* A genuine declaration/type contract, independent of successful elaboration.
   There must be runtime code for each source dynamic declaration, of its
   independently supplied type. Denotation agreement is a separate hypothesis. *)
Definition source_meaning_binding_types_def:
  source_meaning_binding_types types bindings <=>
    !path ty. ALOOKUP types path = SOME ty ==>
      ?e. ALOOKUP bindings path = SOME (SE_Runtime e) /\ expr_type e = ty
End

Theorem source_meaning_stage_eval:
  source_meaning_stage scopes table constants original result <=>
    ?resolved. source_resolve_candidate scopes table original = SOME resolved /\
      source_const_eval constants resolved = result
Proof
  simp[source_meaning_stage_def, source_meaning_const_correct]
QED

Theorem source_meaning_build_constant:
  source_meaning_stage scopes table constants original (SC_Value sv) /\
  source_expr_build fuel env scopes table constants bindings ty original = SC_Value e ==>
  sourceConstValueStructured$source_const_reify FEMPTY env.type_defs ty sv = SOME e /\
  expr_type e = ty
Proof
  simp[source_meaning_stage_eval] >> strip_tac >> Cases_on `fuel` >>
  gvs[Once source_expr_build_def, AllCaseEqs()] >>
  gvs[source_expr_reify_def, AllCaseEqs(), source_expr_checked_value]
QED

Theorem source_meaning_build_name:
  source_meaning_binding_types types bindings /\
  source_expr_path original = SOME names /\
  source_resolve_name scopes table names = SOME (path,SR_Dynamic) /\
  ALOOKUP types path = SOME ty /\
  source_meaning_stage scopes table constants original SC_NotConstant /\
  source_expr_build fuel env scopes table constants bindings ty original = SC_Value e ==>
  ALOOKUP bindings path = SOME (SE_Runtime e) /\ expr_type e = ty
Proof
  simp[source_meaning_binding_types_def, source_meaning_stage_eval] >> strip_tac >>
  `?code. ALOOKUP bindings path = SOME (SE_Runtime code) /\ expr_type code = ty` by
    metis_tac[] >>
  Cases_on `original` >> gvs[source_expr_path_def] >>
  Cases_on `fuel` >> gvs[Once source_expr_build_def, source_expr_variable_def,
    source_expr_finish_def, source_const_then_def, source_expr_checked_def, AllCaseEqs()] >>
  gvs[source_expr_path_def]
QED

Theorem source_meaning_build_unary:
  source_meaning_stage scopes table constants (SX_Unary op child) SC_NotConstant /\
  source_expr_build fuel env scopes table constants bindings ty (SX_Unary op child) = SC_Value e ==>
  ?n ce. fuel = SUC n /\
    source_expr_build n env scopes table constants bindings ty child = SC_Value ce /\
    e = Builtin ty (source_expr_unary op) [ce]
Proof
  simp[source_meaning_stage_eval] >> strip_tac >> Cases_on `fuel` >>
  gvs[Once source_expr_build_def, source_const_then_success,
      source_expr_finish_def, source_expr_checked_value, AllCaseEqs()]
QED

Theorem source_meaning_build_binary:
  op <> SCB_LShift /\ op <> SCB_RShift /\
  source_meaning_stage scopes table constants (SX_Binary op left right) SC_NotConstant /\
  source_expr_build fuel env scopes table constants bindings ty (SX_Binary op left right) = SC_Value e ==>
  ?n le re. fuel = SUC n /\
    source_expr_build n env scopes table constants bindings ty left = SC_Value le /\
    source_expr_build n env scopes table constants bindings ty right = SC_Value re /\
    e = Builtin ty (Bop (source_expr_binary op)) [le;re]
Proof
  simp[source_meaning_stage_eval] >> strip_tac >> Cases_on `fuel` >>
  gvs[Once source_expr_build_def, source_const_combine_success,
      source_const_then_success, source_expr_finish_def,
      source_expr_checked_value, AllCaseEqs()]
QED

Theorem source_meaning_resolve_conditional:
  source_resolve_candidate scopes table (SX_IfExp condition left right) = SOME resolved ==>
  ?es. resolved = SCE_Unsupported "ifexp" es
Proof
  simp[source_resolve_candidate_def, Once source_constant_candidate_def,
    Once source_resolve_expr_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem source_meaning_build_conditional:
  source_expr_build fuel env scopes table constants bindings ty
    (SX_IfExp condition left right) = SC_Value e ==>
  ?n ce le re. fuel = SUC n /\
    source_expr_build n env scopes table constants bindings (BaseT BoolT) condition = SC_Value ce /\
    source_expr_build n env scopes table constants bindings ty left = SC_Value le /\
    source_expr_build n env scopes table constants bindings ty right = SC_Value re /\
    e = IfExp ty ce le re
Proof
  Cases_on `fuel` >> simp[Once source_expr_build_def, AllCaseEqs()] >>
  rpt strip_tac >> drule source_meaning_resolve_conditional >> strip_tac >>
  gvs[Once source_const_eval_def, source_const_unimplemented_def, AllCaseEqs(),
      source_const_combine_success, source_expr_checked_value]
QED

Theorem source_meaning_build_boolean:
  source_meaning_stage scopes table constants (SX_Boolean op children) SC_NotConstant /\
  source_expr_build fuel env scopes table constants bindings (BaseT BoolT)
    (SX_Boolean op children) = SC_Value e ==>
  ?n es. fuel = SUC n /\
    source_const_collect (MAP
      (source_expr_build n env scopes table constants bindings (BaseT BoolT)) children) =
      SC_Value es /\ e = source_expr_boolean_runtime op es
Proof
  simp[source_meaning_stage_eval] >> strip_tac >> Cases_on `fuel` >>
  gvs[Once source_expr_build_def, source_const_then_success,
    source_expr_finish_def, source_expr_checked_value, AllCaseEqs()]
QED

Theorem source_meaning_collect_code:
  !children ms. LIST_REL (\original m.
    !fuel env bindings e.
      source_meaning_binding_types types bindings /\
      source_expr_build fuel env scopes table constants (bindings)
        (BaseT BoolT) original = SC_Value e ==>
      source_meaning_code env.type_defs bindings m e) children ms ==>
  !fuel env bindings es.
    source_meaning_binding_types types bindings /\
    source_const_collect (MAP
      (source_expr_build fuel env scopes table constants bindings (BaseT BoolT)) children) =
      SC_Value es ==>
    LIST_REL (source_meaning_code env.type_defs bindings) ms es
Proof
  Induct >> Cases_on `ms` >> simp[source_const_collect_def] >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac) >> Cases_on `es` >>
  gvs[source_const_collect_def, source_const_combine_success] >> res_tac >> simp[]
QED

(* Frozen structural elaboration contract. The semantic derivation is entirely
   source-directed; successful elaboration is used only in this theorem. *)
Theorem source_meaning_build_code:
  !types scopes table constants ty original m.
    source_meaning_source types scopes table constants ty original m ==>
    !fuel env bindings e.
      source_meaning_binding_types types bindings /\
      source_expr_build fuel env scopes table constants bindings ty original = SC_Value e ==>
      source_meaning_code env.type_defs bindings m e
Proof
  ntac 4 gen_tac >> ho_match_mp_tac source_meaning_source_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >- (drule_all source_meaning_build_constant >> strip_tac >>
      irule sourceMeaningCodeTheory.literal >> metis_tac[])
  >- (drule_all source_meaning_build_name >> strip_tac >>
      irule sourceMeaningCodeTheory.name >> simp[])
  >- (drule_all source_meaning_build_unary >> strip_tac >> gvs[] >>
      irule sourceMeaningCodeTheory.unary >> metis_tac[])
  >- (drule_all source_meaning_build_binary >> strip_tac >> gvs[] >>
      irule sourceMeaningCodeTheory.binary >> metis_tac[])
  >- (drule_all source_meaning_build_conditional >> strip_tac >> gvs[] >>
      irule sourceMeaningCodeTheory.conditional >> metis_tac[])
  >- (drule_all source_meaning_build_constant >> strip_tac >>
      irule sourceMeaningCodeTheory.aggregate >> metis_tac[]) >>
  drule_all source_meaning_build_boolean >> strip_tac >> gvs[] >>
  irule source_meaning_boolean_code >>
  irule source_meaning_collect_code >> metis_tac[]
QED

Theorem source_meaning_source_names:
  !types scopes table constants ty original m.
    source_meaning_source types scopes table constants ty original m ==>
    !path. MEM path (source_meaning_names m) ==> IS_SOME (ALOOKUP types path)
Proof
  ntac 4 gen_tac >> ho_match_mp_tac source_meaning_source_ind >>
  rw[source_meaning_names_def] >>
  TRY (drule source_meaning_boolean_names >> strip_tac >>
    gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >> metis_tac[]
QED

Theorem source_meaning_elaboration_sound_on:
  source_meaning_source types scopes table constants ty original m /\
  source_meaning_binding_types types bindings /\
  source_expr_elaborate fuel env scopes table constants bindings ty original = SC_Value e /\
  get_tenv cx = env.type_defs /\
  (!path code. MEM path (source_meaning_names m) /\
    ALOOKUP bindings path = SOME (SE_Runtime code) ==>
    eval_expr cx code = meanings path) ==>
  eval_expr cx e = source_meaning_eval cx meanings m
Proof
  strip_tac >> drule source_expr_elaborate_build >> strip_tac >>
  drule_all source_meaning_build_code >> strip_tac >>
  drule_all source_meaning_code_evaluates_on >> simp[]
QED

(* Equal results AND complete final states, including exceptions/effects.
   No source arithmetic/runtime arithmetic identification is assumed. *)
Theorem source_meaning_elaboration_sound:
  source_meaning_source types scopes table constants ty original m /\
  source_meaning_binding_types types bindings /\
  source_expr_elaborate fuel env scopes table constants bindings ty original = SC_Value e /\
  get_tenv cx = env.type_defs /\
  (!path code. ALOOKUP bindings path = SOME (SE_Runtime code) ==>
    eval_expr cx code = meanings path) ==>
  !st. eval_expr cx e st = source_meaning_eval cx meanings m st
Proof
  strip_tac >> drule source_expr_elaborate_build >> strip_tac >>
  drule_all source_meaning_build_code >> strip_tac >>
  drule_all source_meaning_code_evaluates >> simp[]
QED

Theorem source_meaning_replacement_equal:
  source_meaning_source types scopes table constants ty original m /\
  source_meaning_binding_types types bindings /\
  source_expr_elaborate fuel env scopes table constants bindings ty original = SC_Value e /\
  source_meaning_code env.type_defs bindings m before /\
  get_tenv cx = env.type_defs /\
  (!path code. ALOOKUP bindings path = SOME (SE_Runtime code) ==>
    eval_expr cx code = meanings path) ==>
  !st. eval_expr cx e st = eval_expr cx before st
Proof
  strip_tac >> drule_all source_meaning_elaboration_sound >> strip_tac >>
  drule_all source_meaning_code_evaluates >> simp[]
QED
