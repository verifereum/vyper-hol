Theory s1PrefixIntCallStageReplay
Ancestors
  s1PrefixPreds bodyFullPreds bodyFullExprsListFacts exprBodyPreProps exprSimWordArgs
  exprSimSource vyperInterpreter vyperState list

Theorem intcall_stage_replay_head_read:
  expr_body_pre cenv cx tenv e esi /\
  body_const_cells_agree [(NONE,tops)] cx tenv esi /\
  (!tail. eval_exprs cx [e] (esi with gas_obs := obs ++ tail) =
    (INL hs,mid with gas_obs := tail)) ==>
  (?v. bind (eval_expr cx e) (read_result cx)
        (esi with gas_obs := obs) = (INL v,mid with gas_obs := [])) /\
  body_const_cells_agree [(NONE,tops)] cx tenv mid
Proof
  strip_tac >>
  `?v. vyperState$bind (eval_expr cx e) (read_result cx)
      (esi with gas_obs := obs) = (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_exprs cx [e] _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE[APPEND_NIL])) >>
     disch_then (mp_tac o MATCH_MP eval_exprs_cons_cases) >>
     simp[eval_exprs_nil] >> metis_tac[]) >>
  conj_tac >- (qexists_tac `v` >> first_assum ACCEPT_TAC) >>
  `body_const_cells_agree [(NONE,tops)] cx tenv (mid with gas_obs := [])`
    suffices_by simp[] >>
  irule body_const_cells_agree_expr_read >>
  qpat_assum `vyperState$bind (eval_expr cx e) _ _ = (INL _,mid with gas_obs := [])`
    (irule_at Any) >> simp[] >>
  drule expr_body_pre_static_facts >> simp[]
QED

Theorem intcall_stage_replay_tail_facts:
  body_exprs_full_ok cx (e::es) /\ body_exprs_prefix_ok cx (e::es) /\
  expr_body_pre cenv cx tenv e esi /\
  body_const_cells_agree [(NONE,tops)] cx tenv esi /\
  (!tail. eval_exprs cx [e] (esi with gas_obs := obs ++ tail) =
    (INL hs,mid with gas_obs := tail)) ==>
  body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es /\
  body_const_cells_agree [(NONE,tops)] cx tenv mid
Proof
  strip_tac >> drule_all intcall_stage_replay_head_read >> strip_tac >>
  drule (REWRITE_RULE[ETA_AX] eval_expr_read_INL) >> strip_tac >>
  fs[body_exprs_full_ok_cons,Once body_exprs_prefix_ok_def] >> metis_tac[]
QED
