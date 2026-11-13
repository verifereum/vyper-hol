Theory notMutateExprScopes
Ancestors
  exprLowering vyperInterpreter vyperLocalAccessFrame
  vyperState vyperContext vyperMisc pair sum
  vyperScopePreservation vyperStatePreservation vyperPlaceFrames
  vyperCallFrame vyperCallOutcomeFrame vyperCreateFrame rich_list abiEncodeArgsScopes

Theorem nonmutating_exprs_every[local]:
  !es cenv. ~exprs_can_mutate cenv es <=>
    EVERY (\e. ~expr_can_mutate cenv e) es
Proof
  Induct >> simp[expr_can_mutate_def]
QED

Theorem nonmutating_named_map[local]:
  !kes cenv. named_exprs_can_mutate cenv kes =
    exprs_can_mutate cenv (MAP SND kes)
Proof
  Induct >> simp[expr_can_mutate_def, pairTheory.FORALL_PROD]
QED

Theorem nonmutating_scopes_mutual[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tv:type_value) (id:string)
    (body:stmt list) (vs:eval_result list). T) /\
  (!cx e cenv s v s'. ~expr_can_mutate cenv e /\
    eval_expr cx e s = (INL v,s') ==> s'.scopes = s.scopes) /\
  (!cx es cenv s v s'. ~exprs_can_mutate cenv es /\
    eval_exprs cx es s = (INL v,s') ==> s'.scopes = s.scopes) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!cx es cenv s v s'. ~exprs_can_mutate cenv es /\
    eval_expr_results cx es s = (INL v,s') ==> s'.scopes = s.scopes)
Proof
  simp[] >> rpt conj_tac >>
  metis_tac[eval_expr_no_mutation_scopes, eval_exprs_no_mutation_scopes,
            eval_expr_results_no_mutation_scopes]
QED

Theorem not_mutate_expr_scopes:
  !cenv cx e s v s'.
    ~expr_can_mutate cenv e /\ eval_expr cx e s = (INL v, s') ==>
    s'.scopes = s.scopes
Proof
  metis_tac[nonmutating_scopes_mutual]
QED
