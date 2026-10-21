Theory vyperEvalPreservesNameTarget
Ancestors
  vyperMisc vyperContext vyperState vyperInterpreter vyperLookup
  vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes vyperEvalMisc

(* ========================================================================
   Preservation of lookup_name_target through eval_expr / eval_stmts.

   After the Name/BareGlobalName split, lookup_name_target (which uses
   NameTarget) can only return ScopedVar. The immutable case is handled
   separately via BareGlobalNameTarget.

   TOP-LEVEL:
     eval_expr_preserves_lookup_name_target
     eval_stmts_preserves_lookup_name_target
   ======================================================================== *)

(* ===== Helper: extract facts from a successful NameTarget lookup ===== *)

Theorem lookup_name_target_facts[local]:
  ∀cx st n av.
    lookup_name_target cx st n = SOME av ⇒
    var_in_scope st n ∧ av = BaseTargetV (ScopedVar n) []
Proof
  rpt strip_tac >>
  gvs[lookup_name_target_def, lookup_base_target_def,
      var_in_scope_iff_lookup_name_typed, lookup_name_typed_def] >>
  qpat_x_assum `_ = SOME _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def, raise_def] >>
  Cases_on `IS_SOME (lookup_scopes n st.scopes)` >>
  gvs[return_def, raise_def]
QED

(* ===== Helper: reconstruct lookup_name_target in st' ===== *)

Theorem reconstruct_scoped_lookup[local]:
  ∀cx st' n.
    var_in_scope st' n ⇒
    lookup_name_target cx st' n = SOME (BaseTargetV (ScopedVar n) [])
Proof
  rpt strip_tac >>
  gvs[lookup_name_target_def, lookup_base_target_def,
      var_in_scope_iff_lookup_name_typed, lookup_name_typed_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def]
QED

Theorem lookup_name_target_scopes_dom[local]:
  MAP FDOM st.scopes = MAP FDOM st'.scopes /\
  lookup_name_target cx st n = SOME av ==>
  lookup_name_target cx st' n = SOME av
Proof
  rpt strip_tac >> drule lookup_name_target_facts >> strip_tac >> gvs[] >>
  irule reconstruct_scoped_lookup >>
  irule preserves_scopes_dom_var_in_scope >> qexists_tac `st` >> simp[] >>
  Cases_on `st.scopes` >> Cases_on `st'.scopes` >>
  gvs[preserves_scopes_dom_def]
QED

Theorem ExtCall_outcome_preserves_lookup_name_target:
  lookup_name_target cx st n = SOME av /\
  (!bs s res t. k bs s = (res,t) ==> MAP FDOM s.scopes = MAP FDOM t.scopes) /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
       check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==> lookup_name_target cx st' n = SOME av
Proof
  rpt strip_tac >> drule_all ExtCall_outcome_preserves_scopes_dom >> strip_tac >>
  drule_all lookup_name_target_scopes_dom >> simp[]
QED

Theorem Send_outcome_preserves_lookup_name_target:
  lookup_name_target cx st n = SOME av /\
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==> lookup_name_target cx st' n = SOME av
Proof
  rpt strip_tac >> drule Send_outcome_preserves_locals >> strip_tac >>
  irule lookup_name_target_scopes_dom >> qexists_tac `st` >> simp[]
QED

(* ===== Main theorems ===== *)

Theorem eval_expr_preserves_lookup_name_target:
  ∀cx e st res st' n av.
    eval_expr cx e st = (res, st') ∧
    lookup_name_target cx st n = SOME av ⇒
    lookup_name_target cx st' n = SOME av
Proof
  rpt strip_tac >> drule lookup_name_target_facts >> strip_tac >> gvs[] >>
  irule reconstruct_scoped_lookup >>
  metis_tac[eval_expr_preserves_var_in_scope]
QED

Theorem eval_stmts_preserves_lookup_name_target:
  ∀cx ss st res st' n av.
    eval_stmts cx ss st = (res, st') ∧
    lookup_name_target cx st n = SOME av ⇒
    lookup_name_target cx st' n = SOME av
Proof
  rpt strip_tac >> drule lookup_name_target_facts >> strip_tac >> gvs[] >>
  irule reconstruct_scoped_lookup >>
  metis_tac[eval_stmts_preserves_var_in_scope]
QED
