Theory sourceMeaningEffects
Ancestors
  sourceMeaningElaborate sourceMeaningCode sourceMeaningDefs sourceExprElaborate
  sourceExprDefs sourceExprProps sourceSyntax sourceResolve sourceConstEval
  sourceConstEvalProps vyperAST vyperInterpreter vyperState vyperContext alist

(* Independent declaration-kind agreement for effectful intrinsics. *)
Definition source_meaning_intrinsics_agree_def:
  source_meaning_intrinsics_agree intrinsics bindings <=>
    !path b. ALOOKUP intrinsics path = SOME b ==>
      ALOOKUP bindings path = SOME (SE_Intrinsic b)
End

(* Direct source rule, separate from ordinary expression derivations so the
   additional inference contract is visible, rather than silently assumed. *)
Definition source_meaning_revert_source_def:
  source_meaning_revert_source types scopes table constants intrinsics callee data data_ty m <=>
    (?names path. source_expr_path callee = SOME names /\
      source_resolve_name scopes table names = SOME (path,SR_Function) /\
      ALOOKUP intrinsics path = SOME SE_RawRevert) /\
    source_meaning_source types scopes table constants data_ty data m
End

Theorem source_meaning_path_candidate:
  !original. !names. source_expr_path original = SOME names ==>
    source_constant_candidate original = SCE_Name names
Proof
  ho_match_mp_tac source_expr_path_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once source_expr_path_def, Once source_constant_candidate_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem source_meaning_function_call_not_constant:
  source_expr_path callee = SOME names /\
  source_resolve_name scopes table names = SOME (path,SR_Function) /\
  source_resolve_candidate scopes table (SX_Call callee args keywords) = SOME resolved ==>
  source_const_eval constants resolved <> SC_Value sv
Proof
  strip_tac >> drule source_meaning_path_candidate >> strip_tac >>
  gvs[source_resolve_candidate_def, Once source_constant_candidate_def,
      Once source_resolve_expr_def, source_resolve_callee_def,
      source_resolve_atom_def, AllCaseEqs(), Once source_const_eval_def,
      source_const_unimplemented_not_value]
QED

Theorem source_meaning_build_revert:
  source_expr_path callee = SOME names /\
  source_resolve_name scopes table names = SOME (path,SR_Function) /\
  ALOOKUP bindings path = SOME (SE_Intrinsic SE_RawRevert) /\
  source_expr_infer n env scopes table constants bindings data = SOME data_ty /\
  source_expr_build (SUC n) env scopes table constants bindings ty
    (SX_Call callee [data] []) = SC_Value e ==>
  ?de. source_expr_build n env scopes table constants bindings data_ty data = SC_Value de /\
       e = Call ty RawRevert [de] NONE
Proof
  strip_tac >>
  gvs[Once source_expr_build_def, AllCaseEqs()]
  >- (drule_all source_meaning_function_call_not_constant >> metis_tac[]) >>
  gvs[source_expr_callable_def, source_expr_intrinsic_def,
      source_const_then_success, source_expr_checked_value]
QED

(* Complete result/state equality for the existing raw_revert implementation.
   The data inference equality is an explicit remaining source-type transport
   obligation, not a hypothesis identifying source meaning with emitted code. *)
Theorem source_meaning_revert_sound:
  source_meaning_revert_source types scopes table constants intrinsics callee data data_ty m /\
  source_meaning_binding_types types bindings /\
  source_meaning_intrinsics_agree intrinsics bindings /\
  source_expr_infer n env scopes table constants bindings data = SOME data_ty /\
  source_expr_elaborate (SUC n) env scopes table constants bindings ty
    (SX_Call callee [data] []) = SC_Value e /\
  get_tenv cx = env.type_defs /\
  (!path code. ALOOKUP bindings path = SOME (SE_Runtime code) ==>
    eval_expr cx code = meanings path) ==>
  !st. eval_expr cx e st = source_meaning_eval cx meanings (SM_Revert ty m) st
Proof
  simp[source_meaning_revert_source_def, source_meaning_intrinsics_agree_def] >>
  strip_tac >> drule source_expr_elaborate_build >> strip_tac >>
  `ALOOKUP bindings path = SOME (SE_Intrinsic SE_RawRevert)` by metis_tac[] >>
  drule_all source_meaning_build_revert >> strip_tac >> gvs[] >>
  drule_all source_meaning_build_code >> strip_tac >>
  `source_meaning_code env.type_defs bindings (SM_Revert ty m)
    (Call ty RawRevert [de] NONE)` by
    (irule sourceMeaningCodeTheory.revert >> simp[]) >>
  drule_all source_meaning_code_evaluates >> simp[]
QED
