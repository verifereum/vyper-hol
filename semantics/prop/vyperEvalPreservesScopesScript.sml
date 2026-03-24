Theory vyperEvalPreservesScopes
Ancestors
  vyperState vyperInterpreter vyperLookup
  vyperEvalExprPreservesScopesDom vyperScopePreservation
  vyperMisc vyperImmutablesPreservation vyperStatePreservation

Definition preserves_scopes_dom_def:
  preserves_scopes_dom st st' ⇔
    (st.scopes = [] ∧ st'.scopes = []) ∨
    (st.scopes ≠ [] ∧ st'.scopes ≠ [] ∧
     FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
     MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes))
End

Theorem preserves_scopes_dom_var_in_scope:
  ∀st st' n.
    var_in_scope st n ∧
    preserves_scopes_dom st st' ⇒
    var_in_scope st' n
Proof
  simp[preserves_scopes_dom_def] >> rpt strip_tac >-
  (* Empty scopes case: contradicts var_in_scope *)
  gvs[var_in_scope_iff_lookup_name_typed, lookup_name_typed_def, lookup_scopes_def] >>
  (* Non-empty scopes case *)
  irule var_in_scope_scopes_subset >> metis_tac[]
QED

Theorem preserves_scopes_dom_length:
  ∀st st'. preserves_scopes_dom st st' ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[preserves_scopes_dom_def] >> rpt strip_tac >>
  Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[] >>
  metis_tac[listTheory.LENGTH_MAP]
QED

(* ------------------------------------------------------------------------
   Helper Lemmas for Individual Statement Cases
   ------------------------------------------------------------------------ *)

Theorem case_Pass_dom[local]:
  ∀cx st res st'.
    eval_stmt cx Pass st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, return_def, preserves_scopes_dom_def]
QED

Theorem case_Continue_dom[local]:
  ∀cx st res st'.
    eval_stmt cx Continue st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, raise_def, preserves_scopes_dom_def]
QED

Theorem case_Break_dom[local]:
  ∀cx st res st'.
    eval_stmt cx Break st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, raise_def, preserves_scopes_dom_def]
QED

Theorem case_Return_NONE_dom[local]:
  ∀cx st res st'.
    eval_stmt cx (Return NONE) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, raise_def, preserves_scopes_dom_def]
QED

Theorem map_fdom_eq_preserves_dom[local]:
  ∀st st'. MAP FDOM st.scopes = MAP FDOM st'.scopes ⇒ preserves_scopes_dom st st'
Proof
  simp[preserves_scopes_dom_def] >> rpt strip_tac >>
  Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[]
QED

Theorem case_Return_SOME_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Return (SOME e)) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac raise_scopes >>
  imp_res_tac materialise_scopes >> gvs[]
QED

Theorem case_Raise_dom[local]:
  ∀cx reason.
    (∀e. reason = RaiseReason e ⇒
       ∀st res st'. eval_expr cx e st = (res, st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Raise reason) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `reason` >>
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac get_Value_scopes >>
  imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >> imp_res_tac lift_option_type_scopes >>
  imp_res_tac raise_scopes >> gvs[]
QED

Theorem case_Assert_dom[local]:
  ∀cx e reason.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀se. reason = AssertReason se ⇒
       ∀st res st'. eval_expr cx se st = (res, st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Assert e reason) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `reason` >>
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  (* All cases: eval_expr produces the first state change *)
  imp_res_tac get_Value_scopes >> gvs[] >>
  qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
  simp[switch_BoolV_def] >>
  rpt IF_CASES_TAC >> simp[return_def, raise_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >> gvs[]) >>
  (* AssertReason: chain eval_expr IH for e then e' *)
  rpt (first_x_assum drule >> strip_tac >> gvs[])
QED

Theorem case_Log_dom[local]:
  ∀cx id es.
    (∀st res st'. eval_exprs cx es st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Log id es) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac push_log_scopes >> gvs[]
QED

Theorem case_Append_dom[local]:
  ∀cx bt e.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Append bt e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >>
  imp_res_tac materialise_scopes >>
  imp_res_tac assign_target_preserves_scopes_dom >> gvs[] >>
  Cases_on `x` >> gvs[bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >>
  imp_res_tac materialise_scopes >>
  imp_res_tac assign_target_preserves_scopes_dom >> gvs[] >>
  rpt (first_x_assum (drule_then assume_tac) >> gvs[])
QED

Theorem case_AugAssign_dom[local]:
  ∀cx ty bt bop e.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (AugAssign ty bt bop e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >>
  imp_res_tac assign_target_preserves_scopes_dom >> gvs[] >>
  Cases_on `x` >> gvs[bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >>
  imp_res_tac assign_target_preserves_scopes_dom >> gvs[] >>
  rpt (first_x_assum (drule_then assume_tac) >> gvs[])
QED

Theorem case_Expr_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Expr e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >>
  imp_res_tac check_scopes >> imp_res_tac type_check_scopes >> imp_res_tac type_check_scopes >> gvs[]
QED

Theorem case_AnnAssign_dom[local]:
  ∀cx id typ e st res st'.
    eval_stmt cx (AnnAssign id typ e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* All cases: lift_option_type preserves state *)
  imp_res_tac lift_option_type_scopes >> gvs[] >~
  (* Main case with new_variable *)
  [`new_variable _ _ _ _ = _`]
  >- (
    imp_res_tac eval_expr_preserves_scopes_dom >>
    imp_res_tac get_Value_scopes >>
    imp_res_tac materialise_scopes >> gvs[] >>
    Cases_on `s'³'.scopes` >> gvs[] >-
    gvs[new_variable_def, bind_def, get_scopes_def, return_def, check_def, type_check_def, assert_def, lookup_scopes_def, ignore_bind_def, raise_def] >>
    `s'⁴'.scopes ≠ []` by simp[] >>
    drule_all new_variable_scope_property >> strip_tac >> gvs[] >>
    Cases_on `st.scopes` >> gvs[]
  ) >~
  (* get_Value/materialise error case *)
  [`materialise _ _ _ = (INR _, _)`]
  >- (
    imp_res_tac materialise_scopes >> gvs[] >>
    imp_res_tac eval_expr_preserves_scopes_dom >>
    Cases_on `st.scopes` >> Cases_on `s'³'.scopes` >> gvs[]
  ) >>
  (* eval_expr error case *)
  imp_res_tac eval_expr_preserves_scopes_dom >>
  Cases_on `st.scopes` >> Cases_on `s'³'.scopes` >> gvs[]
QED

Theorem case_If_dom[local]:
  ∀cx e ss1 ss2.
    (* IH for ss1: conditional on eval_expr succeeding *)
    (∀s'' tv t s3 x t'.
       eval_expr cx e s'' = (INL tv, t) ∧ push_scope s3 = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss1 st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (* IH for ss2: conditional on eval_expr succeeding *)
    (∀s'' tv t s3 x t'.
       eval_expr cx e s'' = (INL tv, t) ∧ push_scope s3 = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss2 st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (* IH for expr *)
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (If e ss1 ss2) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), push_scope_def, return_def] >>
  strip_tac >> gvs[] >>
  (* Name the IH assumptions for clarity *)
  rename1 `eval_expr cx e st = (INL tv, s_expr)` >>
  (* eval_expr preserves scopes *)
  `MAP FDOM st.scopes = MAP FDOM s_expr.scopes` by
    (qpat_x_assum `∀st res st'. eval_expr _ _ _ = _ ⇒ _` drule >> simp[]) >>
  `MAP FDOM st'.scopes = MAP FDOM s_expr.scopes` suffices_by simp[] >>
  (* Get IH for ss1 and ss2 into usable form.
     The IH has 5 quantified variables: s'', tv, t, s3, t'.
     The x in (INL x, t') has been simplified to () since push_scope always returns ().
     We need to instantiate: s'' = st, tv = tv, t = s_expr, s3 = s_expr, t' = s_expr with scopes updated_by CONS FEMPTY *)
  `∀st res st'. eval_stmts cx ss1 st = (res, st') ⇒ preserves_scopes_dom st st'` by
    (rpt strip_tac >>
     qpat_x_assum `∀s'' tv t s3 t'. _ ⇒ ∀st res st'. eval_stmts _ ss1 _ = _ ⇒ _`
       (qspecl_then [`st`, `tv`, `s_expr`, `s_expr`, `s_expr with scopes updated_by CONS FEMPTY`] mp_tac) >>
     simp[push_scope_def, return_def]) >>
  `∀st res st'. eval_stmts cx ss2 st = (res, st') ⇒ preserves_scopes_dom st st'` by
    (rpt strip_tac >>
     qpat_x_assum `∀s'' tv t s3 t'. _ ⇒ ∀st res st'. eval_stmts _ ss2 _ = _ ⇒ _`
       (qspecl_then [`st`, `tv`, `s_expr`, `s_expr`, `s_expr with scopes updated_by CONS FEMPTY`] mp_tac) >>
     simp[push_scope_def, return_def]) >>
  (* The finally block restores scopes *)
  `TL (s_expr with scopes updated_by CONS FEMPTY).scopes = s_expr.scopes` by simp[] >>
  drule finally_pop_scope_preserves_tl_dom >> simp[] >> strip_tac >>
  first_x_assum irule >> rpt strip_tac >>
  gvs[switch_BoolV_def, raise_def] >>
  Cases_on `tv = Value (BoolV T)` >> gvs[]
  >- (qpat_x_assum `∀st res st'. eval_stmts _ ss1 _ = _ ⇒ _` drule >>
      gvs[preserves_scopes_dom_def] >> strip_tac >> gvs[]) >>
  Cases_on `tv = Value (BoolV F)` >> gvs[raise_def] >>
  qpat_x_assum `∀st res st'. eval_stmts _ ss2 _ = _ ⇒ _` drule >>
  gvs[preserves_scopes_dom_def] >> strip_tac >> gvs[]
QED

Theorem case_If_map_fdom[local]:
  ∀cx e ss1 ss2.
    (∀s'' tv t s3 x t'.
       eval_expr cx e s'' = (INL tv, t) ∧ push_scope s3 = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss1 st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (∀s'' tv t s3 x t'.
       eval_expr cx e s'' = (INL tv, t) ∧ push_scope s3 = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss2 st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (If e ss1 ss2) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), push_scope_def, return_def] >>
  strip_tac >> gvs[] >>
  rename1 `eval_expr cx e st = (INL tv, s_expr)` >>
  `MAP FDOM st.scopes = MAP FDOM s_expr.scopes` by
    (qpat_x_assum `∀st res st'. eval_expr _ _ _ = _ ⇒ _` drule >> simp[]) >>
  `MAP FDOM st'.scopes = MAP FDOM s_expr.scopes` suffices_by simp[] >>
  `∀st res st'. eval_stmts cx ss1 st = (res, st') ⇒ preserves_scopes_dom st st'` by
    (rpt strip_tac >>
     qpat_x_assum `∀s'' tv t s3 t'. _ ⇒ ∀st res st'. eval_stmts _ ss1 _ = _ ⇒ _`
       (qspecl_then [`st`, `tv`, `s_expr`, `s_expr`, `s_expr with scopes updated_by CONS FEMPTY`] mp_tac) >>
     simp[push_scope_def, return_def]) >>
  `∀st res st'. eval_stmts cx ss2 st = (res, st') ⇒ preserves_scopes_dom st st'` by
    (rpt strip_tac >>
     qpat_x_assum `∀s'' tv t s3 t'. _ ⇒ ∀st res st'. eval_stmts _ ss2 _ = _ ⇒ _`
       (qspecl_then [`st`, `tv`, `s_expr`, `s_expr`, `s_expr with scopes updated_by CONS FEMPTY`] mp_tac) >>
     simp[push_scope_def, return_def]) >>
  `TL (s_expr with scopes updated_by CONS FEMPTY).scopes = s_expr.scopes` by simp[] >>
  drule finally_pop_scope_preserves_tl_dom >> simp[] >> strip_tac >>
  first_x_assum irule >> rpt strip_tac >>
  gvs[switch_BoolV_def, raise_def] >>
  Cases_on `tv = Value (BoolV T)` >> gvs[]
  >- (rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      gvs[preserves_scopes_dom_def]) >>
  Cases_on `tv = Value (BoolV F)` >> gvs[raise_def]
  >- (rpt strip_tac >>
      qpat_x_assum `∀st res st'. eval_stmts _ ss2 _ = _ ⇒ _` drule >>
      strip_tac >> gvs[preserves_scopes_dom_def]) >>
  gvs[raise_def]
QED

Theorem case_For_dom[local]:
  ∀cx id typ it n body.
    (* IH for eval_for: conditional on lift_option_type, eval_iterator and check succeeding *)
    (∀tenv s'' tyv t s'³' vs t' s'⁴' x t''.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv, t) ∧
       eval_iterator cx it s'³' = (INL vs, t') ∧
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'⁴' = (INL x, t'') ⇒
       ∀st res st'. eval_for cx tyv (string_to_num id) body vs st = (res, st') ⇒
         preserves_scopes_dom st st') ∧
    (* IH for iterator: guarded by lift_option_type *)
    (∀tenv s'' tyv t.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv, t) ⇒
       ∀st res st'. eval_iterator cx it st = (res, st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* Case: lift_option_type failed *)
  TRY (imp_res_tac lift_option_type_scopes >> gvs[preserves_scopes_dom_def] >> NO_TAC) >>
  (* Discharge iterator IH guard *)
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac lift_option_type_scopes >> gvs[] >>
  (* Case: eval_iterator failed *)
  TRY (irule map_fdom_eq_preserves_dom >> first_x_assum drule >> simp[] >> NO_TAC) >>
  (* Case: check failed *)
  imp_res_tac check_scopes >> imp_res_tac type_check_scopes >> gvs[] >>
  TRY (irule map_fdom_eq_preserves_dom >> first_x_assum drule >> gvs[] >> NO_TAC) >>
  (* Case: both succeeded, use eval_for IH *)
  first_x_assum drule_all >> strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  Cases_on `st.scopes` >> Cases_on `s'⁴'.scopes` >> gvs[] >>
  Cases_on `st'.scopes` >> gvs[] >>
  Cases_on `s'³'.scopes` >> gvs[]
QED

Theorem case_eval_stmts_nil_dom[local]:
  ∀cx st res st'.
    eval_stmts cx [] st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, return_def, preserves_scopes_dom_def]
QED

Theorem case_eval_stmts_cons_dom[local]:
  ∀cx s ss.
    (* IH for ss: conditional on eval_stmt succeeding *)
    (∀s'' x t.
       eval_stmt cx s s'' = (INL x, t) ⇒
       ∀st res st'. eval_stmts cx ss st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (* IH for s: unconditional *)
    (∀st res st'. eval_stmt cx s st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_stmts cx (s::ss) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* eval_stmt s preserves *)
  qpat_x_assum `∀st'' res' st'''. eval_stmt _ _ _ = _ ⇒ _` (qspec_then `st` mp_tac) >> simp[] >>
  strip_tac >>
  (* IH for ss applies since eval_stmt succeeded (result is INL ()) *)
  first_x_assum (qspecl_then [`st`, `s''`] mp_tac) >> simp[] >-
  (* First: case where st.scopes = [] *)
  (strip_tac >> first_x_assum drule >> simp[]) >>
  (* Second: case where st.scopes ≠ [] *)
  strip_tac >> first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
  irule pred_setTheory.SUBSET_TRANS >>
  qexists_tac `FDOM (HD s''.scopes)` >> simp[]
QED

(* === Category 6: eval_for (iteration) === *)

Theorem case_eval_for_nil_dom[local]:
  ∀cx tyv nm body st res st'.
    eval_for cx tyv nm body [] st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, return_def, preserves_scopes_dom_def]
QED

Theorem try_body_preserves_tl_dom[local]:
  ∀cx body nm tyv v st0.
    (* IH for eval_stmts: conditional on push_scope_with_var succeeding *)
    (∀s'' x t. push_scope_with_var nm tyv v s'' = (INL x, t) ⇒
       ∀st res st'. eval_stmts cx body st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st1 res1 st1'.
      push_scope_with_var nm tyv v st0 = (INL (), st1) ⇒
      (try (do x <- eval_stmts cx body; return F od) handle_loop_exception) st1 = (res1, st1') ⇒
      MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)
Proof
  rpt strip_tac >>
  gvs[try_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def] >>
  (* Use IH - push_scope_with_var succeeded *)
  TRY (first_x_assum (qspecl_then [`st0`, `st1`] mp_tac) >> simp[] >> strip_tac >>
       first_x_assum drule >> simp[preserves_scopes_dom_def] >> NO_TAC) >>
  gvs[handle_loop_exception_def, return_def, raise_def] >>
  first_x_assum (qspecl_then [`st0`, `st1`] mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[preserves_scopes_dom_def] >> strip_tac >>
  TRY (simp[] >> NO_TAC) >>  (* handles empty scopes case *)
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt IF_CASES_TAC >> simp[return_def, raise_def] >> rpt strip_tac >> gvs[]
QED

Theorem try_body_preserves_tl_dom'[local]:
  ∀cx body.
    (∀st res st'. eval_stmts cx body st = (res, st') ⇒
       preserves_scopes_dom st st') ⇒
    ∀st1 res1 st1'.
      (try (do x <- eval_stmts cx body; return F od) handle_loop_exception)
        st1 = (res1, st1') ⇒
      MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)
Proof
  rpt strip_tac >>
  gvs[try_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def] >>
  TRY (first_x_assum drule >> simp[preserves_scopes_dom_def] >> NO_TAC) >>
  gvs[handle_loop_exception_def, return_def, raise_def] >>
  first_x_assum drule >> simp[preserves_scopes_dom_def] >> strip_tac >>
  TRY (simp[] >> NO_TAC) >>
  gvs[] >>
  TRY (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
       rpt IF_CASES_TAC >> simp[return_def, raise_def] >>
       rpt strip_tac >> gvs[] >> NO_TAC) >>
  TRY (gvs[return_def] >> NO_TAC) >>
  rpt strip_tac >> gvs[]
QED

Theorem case_eval_for_cons_dom[local]:
  ∀cx nm tyv body v vs.
    (* IH for eval_for: conditional on push_scope_with_var succeeding and finally succeeding with broke=F *)
    (∀s'' x t s'³' broke t'.
       push_scope_with_var nm tyv v s'' = (INL x, t) ∧
       finally (try (do eval_stmts cx body; return F od) handle_loop_exception) pop_scope s'³' = (INL broke, t') ∧
       ¬broke ⇒
       ∀st res st'. eval_for cx tyv nm body vs st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (* IH for eval_stmts: conditional on push_scope_with_var succeeding *)
    (∀s'' x t. push_scope_with_var nm tyv v s'' = (INL x, t) ⇒
       ∀st res st'. eval_stmts cx body st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_for cx tyv nm body (v::vs) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, push_scope_with_var_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* Handle error case from finally: unfold and use try_body_preserves_tl_dom *)
  TRY (
    gvs[finally_def, AllCaseEqs(), bind_def, ignore_bind_def, pop_scope_def, return_def, raise_def] >>
    qspecl_then [`cx`, `body`, `nm`, `tyv`, `v`, `st`] mp_tac try_body_preserves_tl_dom >>
    impl_tac >- (rpt strip_tac >> gvs[push_scope_with_var_def, return_def] >> first_x_assum drule >> simp[]) >>
    simp[push_scope_with_var_def, return_def] >> strip_tac >>
    gvs[preserves_scopes_dom_def] >>
    Cases_on `st.scopes` >> Cases_on `tl` >> gvs[] >> NO_TAC
  ) >>
  (* Success case: finally with pop_scope *)
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs()] >>
  strip_tac >> gvs[bind_def, ignore_bind_def, pop_scope_def, return_def, raise_def, AllCaseEqs()] >>
  (* Use try_body_preserves_tl_dom to establish MAP FDOM preservation *)
  sg `MAP FDOM (TL (st with scopes updated_by CONS (FEMPTY |+ (nm,(tyv,v)))).scopes) = MAP FDOM (TL s'³'.scopes)` >-
  (qspecl_then [`cx`, `body`, `nm`, `tyv`, `v`, `st`] mp_tac try_body_preserves_tl_dom >>
   impl_tac >- (rpt strip_tac >> gvs[push_scope_with_var_def, return_def] >> first_x_assum drule >> simp[]) >>
   simp[push_scope_with_var_def, return_def] >> strip_tac >>
   first_x_assum drule >> simp[]) >> gvs[] >>
  (* Case split on broke *)
  Cases_on `broke` >> gvs[return_def, preserves_scopes_dom_def] >-
  (* broke = T: return () *)
  (Cases_on `st.scopes` >> Cases_on `tl` >> gvs[]) >>
  (* broke = F: use recursive IH *)
  qpat_x_assum `∀s'⁴' t s'⁵' t'. _ ⇒ _` (qspecl_then [`st`, `st with scopes updated_by CONS (FEMPTY |+ (nm,(tyv,v)))`,
                                                       `st with scopes updated_by CONS (FEMPTY |+ (nm,(tyv,v)))`,
                                                       `s'³' with scopes := tl`] mp_tac) >>
  simp[push_scope_with_var_def, return_def] >>
  simp[finally_def, AllCaseEqs(), bind_def, ignore_bind_def, pop_scope_def, return_def, raise_def] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  Cases_on `st.scopes` >> Cases_on `tl` >> gvs[]
QED

Theorem eval_for_map_fdom[local]:
  ∀cx tyv nm body vs.
    (∀st res st'. eval_stmts cx body st = (res, st') ⇒
       preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_for cx tyv nm body vs st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  Induct
  (* [] case *)
  >- (rpt strip_tac >> gvs[evaluate_def, return_def]) >>
  rpt strip_tac >>
  (* v::vs case *)
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_with_var_def,
       return_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
  (* common: establish try_body preserves TL *)
  >> (
    `MAP FDOM s''.scopes = MAP FDOM st.scopes` by (
      drule finally_pop_scope_preserves_tl_dom >> simp[] >>
      disch_then irule >> rpt strip_tac >>
      drule_all try_body_preserves_tl_dom' >> simp[]) >>
    (* Goal 2 (error): trivial since st' not involved *)
    TRY (gvs[] >> NO_TAC) >>
    (* Goal 1 (success): case split on broke *)
    Cases_on `broke` >> gvs[return_def] >>
    first_x_assum drule >> simp[])
QED

Theorem case_Array_iterator_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_iterator cx (Array e) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac get_Value_scopes >> imp_res_tac materialise_scopes >>
  imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >>
  imp_res_tac return_scopes >> first_x_assum drule >> gvs[]
QED

Theorem case_Range_iterator_dom[local]:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e2 st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_iterator cx (Range e1 e2) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >>
  imp_res_tac return_scopes >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[])
QED

Theorem case_BaseTarget_dom[local]:
  ∀cx bt.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_target cx (BaseTarget bt) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `x` >> gvs[return_def]
QED

Theorem case_TupleTarget_dom[local]:
  ∀cx gs.
    (∀st res st'. eval_targets cx gs st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_target cx (TupleTarget gs) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac return_scopes >> gvs[]
QED

Theorem case_eval_targets_nil_dom[local]:
  ∀cx st res st'.
    eval_targets cx [] st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_targets_cons_dom[local]:
  ∀cx g gs.
    (∀st res st'. eval_target cx g st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀s'' gv t.
       eval_target cx g s'' = (INL gv,t) ⇒
       ∀st res st'.
         eval_targets cx gs st = (res, st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_targets cx (g::gs) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac return_scopes >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[])
QED

(* ------------------------------------------------------------------------
   Main Mutual Induction Theorem

   Combines all cases via ho_match_mp_tac evaluate_ind.
   ------------------------------------------------------------------------ *)
Theorem scopes_dom_mutual[local]:
  (∀cx s st res st'. eval_stmt cx s st = (res, st') ⇒ preserves_scopes_dom st st') ∧
  (∀cx ss st res st'. eval_stmts cx ss st = (res, st') ⇒ preserves_scopes_dom st st') ∧
  (∀cx it st res st'. eval_iterator cx it st = (res, st') ⇒
     MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx g st res st'. eval_target cx g st = (res, st') ⇒
     MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx gs st res st'. eval_targets cx gs st = (res, st') ⇒
     MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒
     MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ⇒
     preserves_scopes_dom st st') ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒
     MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒
     MAP FDOM st.scopes = MAP FDOM st'.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt strip_tac
  (* === Statement cases === *)
  (* Pass *) >- gvs[evaluate_def, return_def, preserves_scopes_dom_def]
  (* Continue *) >- gvs[evaluate_def, raise_def, preserves_scopes_dom_def]
  (* Break *) >- gvs[evaluate_def, raise_def, preserves_scopes_dom_def]
  (* Return NONE *) >- gvs[evaluate_def, raise_def, preserves_scopes_dom_def]
  (* Return (SOME e) *) >- (drule_all case_Return_SOME_dom >> gvs[])
  (* Raise RaiseBare *) >- gvs[evaluate_def, raise_def, preserves_scopes_dom_def]
  (* Raise RaiseUnreachable *) >- gvs[evaluate_def, raise_def, preserves_scopes_dom_def]
  (* Raise (RaiseReason e) *) >- (irule case_Raise_dom >> first_assum $ irule_at (Pos last) >> simp[])
  (* Assert AssertBare *) >- (irule case_Assert_dom >> first_assum $ irule_at (Pos last) >> simp[])
  (* Assert AssertUnreachable *) >- (irule case_Assert_dom >> first_assum $ irule_at (Pos last) >> simp[])
  (* Assert (AssertReason se) *) >-
    (irule map_fdom_eq_preserves_dom >>
     qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     imp_res_tac get_Value_scopes >> gvs[] >>
     qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
     simp[switch_BoolV_def] >>
     rpt IF_CASES_TAC >> simp[return_def, raise_def, bind_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     TRY (imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >>
          imp_res_tac lift_option_type_scopes >> gvs[]) >>
     rpt (first_x_assum drule >> strip_tac >> gvs[]))
  (* Log *) >- (drule_all case_Log_dom >> gvs[])
  (* AnnAssign *) >- (drule case_AnnAssign_dom >> simp[])
  (* Append *) >- (drule case_Append_dom >> rpt strip_tac >> metis_tac[eval_expr_preserves_scopes_dom])
  (* Assign *) >-
    (irule map_fdom_eq_preserves_dom >>
     qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >>
     imp_res_tac materialise_scopes >>
     imp_res_tac assign_target_preserves_scopes_dom >> gvs[] >>
     rpt (first_x_assum drule_all >> strip_tac >> gvs[]))
  (* AugAssign *) >- (drule case_AugAssign_dom >> rpt strip_tac >> metis_tac[eval_expr_preserves_scopes_dom])
  (* If *) >- (irule case_If_dom >> qexists_tac `cx` >> qexists_tac `e` >> qexists_tac `res` >> qexists_tac `ss` >> qexists_tac `ss'` >> metis_tac[])
  (* For *) >- (drule_all case_For_dom >> simp[])
  (* Expr *) >- (drule_all case_Expr_dom >> gvs[])
  (* === eval_stmts cases === *)
  (* [] *) >- gvs[evaluate_def, return_def, preserves_scopes_dom_def]
  (* s::ss *) >- (drule_all case_eval_stmts_cons_dom >> gvs[])
  (* === Iterator cases === *)
  (* Array *) >- (drule_all case_Array_iterator_dom >> gvs[])
  (* Range *) >- (drule case_Range_iterator_dom >> metis_tac[eval_expr_preserves_scopes_dom])
  (* === Target cases === *)
  (* BaseTarget *) >- (drule_all case_BaseTarget_dom >> gvs[])
  (* TupleTarget *) >- (drule_all case_TupleTarget_dom >> gvs[])
  (* === eval_targets cases === *)
  (* [] *) >- gvs[evaluate_def, return_def]
  (* g::gs *) >- (drule case_eval_targets_cons_dom >> metis_tac[])
  (* === base_target cases === *)
  >- metis_tac[eval_base_target_preserves_scopes_dom]
  >- metis_tac[eval_base_target_preserves_scopes_dom]
  >- metis_tac[eval_base_target_preserves_scopes_dom]
  >- metis_tac[eval_base_target_preserves_scopes_dom]
  >- metis_tac[eval_base_target_preserves_scopes_dom]
  (* === eval_for cases === *)
  (* [] *) >- gvs[evaluate_def, return_def, preserves_scopes_dom_def]
  (* v::vs *) >- (drule case_eval_for_cons_dom >> metis_tac[])
  (* === Expression cases - use eval_expr_preserves_scopes_dom === *)
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_expr_preserves_scopes_dom >> gvs[])
  >- (drule eval_exprs_preserves_scopes_dom >> gvs[])
  >- (drule eval_exprs_preserves_scopes_dom >> gvs[])
QED

(* ------------------------------------------------------------------------
   Main theorems
   ------------------------------------------------------------------------ *)



Theorem eval_stmts_preserves_scopes_dom:
  ∀cx st st' ss res.
    eval_stmts cx ss st = (res, st') ⇒
    preserves_scopes_dom st st'
Proof
  metis_tac[scopes_dom_mutual]
QED

Theorem eval_stmts_preserves_var_in_scope:
  ∀cx st st' n ss res.
    var_in_scope st n ∧
    eval_stmts cx ss st = (res, st') ⇒
    var_in_scope st' n
Proof
  metis_tac[eval_stmts_preserves_scopes_dom, preserves_scopes_dom_var_in_scope]
QED

(* Helper: lookup_scopes NONE is determined by FDOMs *)
Theorem lookup_scopes_none_iff_fdom:
  !id scopes. lookup_scopes id scopes = NONE <=>
              EVERY (\sc. id NOTIN FDOM sc) scopes
Proof
  Induct_on`scopes` >>
  simp[lookup_scopes_def] >>
  rpt gen_tac >>
  Cases_on`FLOOKUP h id` >> simp[] >>
  gvs[finite_mapTheory.FLOOKUP_DEF]
QED

Theorem lookup_scopes_none_map_fdom:
  !id s1 s2. MAP FDOM s1 = MAP FDOM s2 /\
             lookup_scopes id s1 = NONE ==>
             lookup_scopes id s2 = NONE
Proof
  rpt strip_tac >>
  gvs[lookup_scopes_none_iff_fdom, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  `MEM (FDOM sc) (MAP FDOM s2)` by metis_tac[listTheory.MEM_MAP] >>
  `MEM (FDOM sc) (MAP FDOM s1)` by gvs[] >>
  gvs[listTheory.MEM_MAP] >> res_tac >> gvs[]
QED

(* New entries in HEAD scope are not in any TAIL scope.
   The key property: new_variable checks IS_NONE (lookup_scopes id env)
   before adding, and TAIL FDOMs are preserved throughout evaluation. *)

Theorem new_variable_new_not_in_tail:
  ∀name tv v st res st' nm.
  new_variable name tv v st = (res, st') ∧ st.scopes ≠ [] ∧
  nm ∈ FDOM (HD st'.scopes) ∧ nm ∉ FDOM (HD st.scopes) ⇒
  lookup_scopes nm (TL st'.scopes) = NONE
Proof
  rpt strip_tac >>
  fs[new_variable_def, get_scopes_def, bind_apply, type_check_def,
     ignore_bind_apply, vyperStateTheory.assert_def] >>
  Cases_on `st.scopes` >> fs[] >>
  fs[set_scopes_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  fs[lookup_scopes_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem new_in_head_mutual[local]:
  (!cx s st res st'. eval_stmt cx s st = (res, st') ==>
    st.scopes <> [] ==>
    !id. id IN FDOM (HD st'.scopes) /\ id NOTIN FDOM (HD st.scopes) ==>
         lookup_scopes id (TL st'.scopes) = NONE) /\
  (!cx ss st res st'. eval_stmts cx ss st = (res, st') ==>
    st.scopes <> [] ==>
    !id. id IN FDOM (HD st'.scopes) /\ id NOTIN FDOM (HD st.scopes) ==>
         lookup_scopes id (TL st'.scopes) = NONE) /\
  (!cx it st res st'. eval_iterator cx it st = (res, st') ==> T) /\
  (!cx g st res st'. eval_target cx g st = (res, st') ==> T) /\
  (!cx gs st res st'. eval_targets cx gs st = (res, st') ==> T) /\
  (!cx bt st res st'. eval_base_target cx bt st = (res, st') ==> T) /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ==>
    st.scopes <> [] ==>
    !id. id IN FDOM (HD st'.scopes) /\ id NOTIN FDOM (HD st.scopes) ==>
         lookup_scopes id (TL st'.scopes) = NONE) /\
  (!cx e st res st'. eval_expr cx e st = (res, st') ==> T) /\
  (!cx es st res st'. eval_exprs cx es st = (res, st') ==> T)
Proof
  ho_match_mp_tac evaluate_ind
  >> conj_tac >- (rpt strip_tac >> gvs[evaluate_def, return_def]) (* Pass *)
  >> conj_tac >- (rpt strip_tac >> gvs[evaluate_def, raise_def]) (* Continue *)
  >> conj_tac >- (rpt strip_tac >> gvs[evaluate_def, raise_def]) (* Break *)
  >> conj_tac >- (rpt strip_tac >> gvs[evaluate_def, raise_def]) (* Return NONE *)
  >> conj_tac >- ( (* Return SOME *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      qpat_x_assum`eval_stmt _ _ _ = _`mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac materialise_scopes >>
      imp_res_tac get_Value_scopes >>
      imp_res_tac raise_scopes >> gvs[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- ( (* Raise *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      qpat_x_assum`eval_stmt _ _ _ = _`mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac get_Value_scopes >>
      imp_res_tac lift_option_scopes >>
      imp_res_tac lift_option_type_scopes >>
      imp_res_tac raise_scopes >> gvs[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- ( (* Assert *)
    rpt strip_tac >>
    sg `MAP FDOM st.scopes = MAP FDOM st'.scopes`
    >- (
      qpat_x_assum`eval_stmt _ _ _ = _`mp_tac >>
      simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
           return_def, raise_def] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac get_Value_scopes >>
      imp_res_tac lift_option_scopes >>
      imp_res_tac lift_option_type_scopes >> gvs[] >>
      gvs[return_def, raise_def, bind_def, AllCaseEqs(), COND_RATOR] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac get_Value_scopes >>
      imp_res_tac lift_option_type_scopes >>
      imp_res_tac raise_scopes >> gvs[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- (
    rw[evaluate_def, bind_apply] >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      gvs[AllCaseEqs(),raise_def] >>
      imp_res_tac get_Value_state >>
      imp_res_tac lift_option_type_state >> gvs[] >>
      drule eval_expr_preserves_scopes_dom >> rw[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- (
    rw[evaluate_def, bind_apply] >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      gvs[AllCaseEqs(),switch_BoolV_def, raise_def, COND_RATOR, return_def] >>
      drule eval_expr_preserves_scopes_dom >> rw[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- (
    rw[evaluate_def, bind_apply] >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      gvs[AllCaseEqs(),switch_BoolV_def, raise_def, COND_RATOR, return_def] >>
      drule eval_expr_preserves_scopes_dom >> rw[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- (
    rw[evaluate_def, bind_apply] >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      gvs[AllCaseEqs(),raise_def, switch_BoolV_def, COND_RATOR,
          bind_apply, return_def] >>
      imp_res_tac get_Value_state >>
      imp_res_tac lift_option_type_state >> gvs[] >>
      imp_res_tac eval_expr_preserves_scopes_dom >> rw[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- ( (* Log *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      qpat_x_assum`eval_stmt _ _ _ = _`mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >>
      imp_res_tac eval_exprs_preserves_scopes_dom >>
      imp_res_tac push_log_scopes >> gvs[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- ( (* AnnAssign *)
    rpt strip_tac >>
    qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_apply] >>
    simp[AllCaseEqs(), PULL_EXISTS] >>
    rpt strip_tac >> gvs[] >>
    (* error cases: scopes unchanged, contradiction *)
    TRY (imp_res_tac eval_expr_preserves_scopes_dom >>
         imp_res_tac materialise_scopes >> gvs[] >>
         Cases_on `st.scopes` >> Cases_on `s'³'.scopes` >> gvs[] >> NO_TAC) >>
    (* success case: apply new_variable_new_not_in_tail *)
    imp_res_tac eval_expr_preserves_scopes_dom >>
    imp_res_tac materialise_scopes >> gvs[] >>
    imp_res_tac materialise_state >> gvs[] >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    (*
    imp_res_tac new_variable_state >> gvs[] >>
    *)
    TRY (
      irule new_variable_new_not_in_tail >> gvs[] >>
      goal_assum (drule_at(Pat`new_variable`))) >>
    qmatch_assum_rename_tac`MAP FDOM s1.scopes = MAP FDOM s2.scopes` >>
    Cases_on`s1.scopes` \\ Cases_on`s2.scopes` \\ gvs[])
  >> conj_tac >- ( (* Append *)
    rpt strip_tac >>
    sg `MAP FDOM st.scopes = MAP FDOM st'.scopes`
    >- (
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      TRY pairarg_tac >> gvs[bind_apply, return_def, AllCaseEqs(),
                             ignore_bind_apply] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac eval_base_target_preserves_scopes_dom >>
      imp_res_tac materialise_scopes >>
      imp_res_tac get_Value_scopes >>
      imp_res_tac return_scopes >>
      imp_res_tac (cj 1 assign_target_preserves_scopes_dom) >> gvs[]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- ( (* Assign *)
    rpt strip_tac >>
    sg `MAP FDOM st.scopes = MAP FDOM st'.scopes`
    >- (
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_apply, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac (cj 4 scopes_dom_mutual) >>
      imp_res_tac materialise_scopes >>
      imp_res_tac (cj 1 assign_target_preserves_scopes_dom) >>
      gvs[return_def] ) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- ( (* AugAssign *)
    rpt strip_tac >>
    sg `MAP FDOM st.scopes = MAP FDOM st'.scopes`
    >- (
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_apply, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      TRY pairarg_tac >> gvs[bind_apply, return_def, AllCaseEqs(),
                             ignore_bind_apply] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac eval_base_target_preserves_scopes_dom >>
      imp_res_tac materialise_scopes >>
      imp_res_tac get_Value_scopes >>
      imp_res_tac lift_option_type_scopes >>
      imp_res_tac (cj 1 assign_target_preserves_scopes_dom) >>
      gvs[return_def]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- ( (* If *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      irule case_If_map_fdom >>
      qexists_tac `cx` >> qexists_tac `e` >> qexists_tac `res` >>
      qexists_tac `ss` >> qexists_tac `ss'` >>
      metis_tac[scopes_dom_mutual, eval_expr_preserves_scopes_dom]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- ( (* For *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac lift_option_type_scopes >>
      imp_res_tac (cj 3 scopes_dom_mutual) >> (* eval_iterator *)
      imp_res_tac check_scopes >> imp_res_tac type_check_scopes >> gvs[] >>
      gvs[ignore_bind_apply, check_def, AllCaseEqs(), assert_def] >>
      irule eval_for_map_fdom >>
      goal_assum $ drule_at Any >>
      rpt strip_tac >> drule eval_stmts_preserves_scopes_dom >> simp[]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- ( (* Expr *)
    rpt strip_tac >>
    sg `MAP FDOM st.scopes = MAP FDOM st'.scopes`
    >- (
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_apply, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac get_Value_scopes >>
      imp_res_tac return_scopes >>
      imp_res_tac check_scopes >>
      imp_res_tac type_check_scopes >> gvs[]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- (rpt strip_tac >> gvs[evaluate_def, return_def]) (* stmts [] *)
  >> conj_tac >- ( (* stmts s::ss *)
    rpt strip_tac >>
    (* Unfold eval_stmts to get s_mid *)
    qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, ignore_bind_apply, bind_def, AllCaseEqs()] >>
    reverse (rpt strip_tac >> gvs[])
    >- ( first_x_assum (drule_then irule) >> rw[] ) >>
    (* Now: eval_stmt cx s st = (INL x, s_mid), eval_stmts cx ss s_mid = (res, st') *)
    rename1 `eval_stmt cx s st = (INL _, s_mid)` >>
    (* Case split: is id in HD s_mid.scopes? *)
    Cases_on `id ∈ FDOM (HD s_mid.scopes)`
    (* Case 1: id ∈ FDOM (HD s_mid.scopes) — new entry came from s *)
    >- (
      (* IH_s gives: lookup_scopes id (TL s_mid.scopes) = NONE *)
      first_x_assum drule >>
      disch_then(qspec_then `id` mp_tac) >> simp[] >> strip_tac >>
      (* IH_ss: eval_stmts preserves scopes_dom *)
      imp_res_tac (cj 2 scopes_dom_mutual) >>
      gvs[preserves_scopes_dom_def] >>
      (* TL s_mid.scopes = TL st'.scopes (MAP FDOM) *)
      imp_res_tac lookup_scopes_none_map_fdom >> gvs[]) >>
    (* Case 2: id ∉ FDOM (HD s_mid.scopes) — new entry came from ss *)
    last_x_assum $ drule_then (drule_then irule) >> gvs[] >>
    drule (cj 1 scopes_dom_mutual) >>
    rw[preserves_scopes_dom_def])
  >> conj_tac >- simp[] (* Array: T *)
  >> conj_tac >- simp[] (* Range: T *)
  >> conj_tac >- simp[] (* BaseTarget: T *)
  >> conj_tac >- simp[] (* TupleTarget: T *)
  >> conj_tac >- simp[] (* targets []: T *)
  >> conj_tac >- simp[] (* targets g::gs: T *)
  >> conj_tac >- simp[] (* NameTarget: T *)
  >> conj_tac >- simp[] (* BareGlobalNameTarget: T *)
  >> conj_tac >- simp[] (* TopLevelNameTarget: T *)
  >> conj_tac >- simp[] (* AttributeTarget: T *)
  >> conj_tac >- simp[] (* SubscriptTarget: T *)
  >> conj_tac >- (rpt strip_tac >> gvs[evaluate_def, return_def]) (* for [] *)
  >> conj_tac >- ( (* for v::vs *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by
      (irule eval_for_map_fdom >>
       goal_assum $ drule_at Any >> rw[] >>
       metis_tac[scopes_dom_mutual]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- simp[] (* Name: T *)
  >> conj_tac >- simp[] (* BareGlobalName: T *)
  >> conj_tac >- simp[] (* TopLevelName: T *)
  >> conj_tac >- simp[] (* FlagMember: T *)
  >> conj_tac >- simp[] (* IfExp: T *)
  >> conj_tac >- simp[] (* Literal: T *)
  >> conj_tac >- simp[] (* StructLit: T *)
  >> conj_tac >- simp[] (* Subscript: T *)
  >> conj_tac >- simp[] (* Attribute: T *)
  >> conj_tac >- simp[] (* Builtin: T *)
  >> conj_tac >- simp[] (* Pop: T *)
  >> conj_tac >- simp[] (* TypeBuiltin: T *)
  >> conj_tac >- simp[] (* Send: T *)
  >> conj_tac >- simp[] (* ExtCall: T *)
  >> conj_tac >- simp[] (* IntCall: T *)
  >> conj_tac >- simp[] (* exprs []: T *)
  >> simp[] (* exprs e::es: T *)
QED

Theorem eval_stmts_new_in_head_not_in_tail:
  !cx ss st res st' id.
    eval_stmts cx ss st = (res, st') /\
    st.scopes <> [] /\
    id IN FDOM (HD st'.scopes) /\
    id NOTIN FDOM (HD st.scopes) ==>
    lookup_scopes id (TL st'.scopes) = NONE
Proof
  metis_tac[new_in_head_mutual]
QED

Theorem eval_stmts_preserves_scopes_len:
  ∀cx st ss res st'.
    eval_stmts cx ss st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >> strip_tac >-
  (* Empty scopes case *)
  gvs[] >>
  (* Non-empty scopes case *)
  Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[] >>
  metis_tac[listTheory.LENGTH_MAP]
QED

(* ===== Helpers for scope type value preservation ===== *)

(* lookup_scopes through a list with FUPDATE preserves tv *)
Theorem lookup_scopes_fupdate_preserves_tv:
  ∀n sc pre env tv_old v_old rest.
    find_containing_scope n sc = SOME (pre, env, tv_old, v_old, rest) ⇒
    ∀id tv v new_v.
      lookup_scopes id sc = SOME (tv, v) ⇒
      ∃v'. lookup_scopes id (pre ++ [env |+ (n, (tv_old, new_v))] ++ rest) =
           SOME (tv, v')
Proof
  Induct_on `sc` >>
  simp[vyperStateTheory.find_containing_scope_def] >>
  rpt gen_tac >>
  CASE_TAC >> strip_tac
  >- (
    (* FLOOKUP h n = NONE, recurse *)
    gvs[CaseEq"option", PULL_EXISTS] >>
    PairCases_on `z` >> gvs[] >>
    rpt strip_tac >>
    simp[listTheory.APPEND, vyperStateTheory.lookup_scopes_def] >>
    gvs[vyperStateTheory.lookup_scopes_def] >>
    Cases_on `FLOOKUP h id` >> gvs[] >>
    first_x_assum drule >> disch_then drule >> simp[]
  ) >>
  (* FLOOKUP h n = SOME (tv_old, v_old) *)
  Cases_on `x` >> gvs[] >>
  rpt strip_tac >>
  simp[vyperStateTheory.lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[vyperStateTheory.lookup_scopes_def] >>
  Cases_on `n = id` >> gvs[]
QED

(* Evaluation preserves type_values (tv) in both scope entries and
   immutable entries. set_variable and set_immutable reuse the old tv,
   and new_variable only adds at fresh ids. This is needed for
   env_consistent preservation across evaluation steps with different
   contexts (e.g., IntCall default args and function body). *)

Definition preserves_tv_def:
  preserves_tv cx st st' ⇔
    LENGTH st'.scopes = LENGTH st.scopes ∧
    (∀i id tv v. i < LENGTH st.scopes ∧
                 FLOOKUP (EL i st.scopes) id = SOME (tv, v) ⇒
                 ∃v'. FLOOKUP (EL i st'.scopes) id = SOME (tv, v')) ∧
    (∀src id tv v.
       FLOOKUP (get_source_immutables src
         (case ALOOKUP st.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v) ⇒
       ∃v'. FLOOKUP (get_source_immutables src
         (case ALOOKUP st'.immutables cx.txn.target of
            SOME m => m | NONE => [])) id = SOME (tv, v'))
End

Theorem preserves_tv_refl[simp]:
  ∀cx st. preserves_tv cx st st
Proof
  simp[preserves_tv_def]
QED

Theorem preserves_tv_txn_eq:
  ∀cx cx' st st'.
    cx.txn = cx'.txn ⇒
    (preserves_tv cx st st' ⇔ preserves_tv cx' st st')
Proof
  simp[preserves_tv_def]
QED

Theorem preserves_tv_trans:
  ∀cx st1 st2 st3.
    preserves_tv cx st1 st2 ∧
    preserves_tv cx st2 st3 ⇒
    preserves_tv cx st1 st3
Proof
  simp[preserves_tv_def]
QED

Theorem preserves_tv_eq:
  ∀cx st st'.
    st'.scopes = st.scopes ∧
    st'.immutables = st.immutables ⇒
    preserves_tv cx st st'
Proof
  simp[preserves_tv_def]
QED

(* ===== Scope type value preservation ===== *)
(* If id is not in the head scope before eval_stmts, and eval_stmts
   preserves scopes dom, and new head entries aren't in tail,
   then lookup_scopes id skips the head after eval_stmts *)
Theorem lookup_scopes_not_in_new_head:
  ∀cx ss sc rest res s'.
    eval_stmts cx ss (s with scopes := sc :: rest) = (res, s') ⇒
    id ∉ FDOM sc ⇒
    lookup_scopes id rest = SOME entry ⇒
    s'.scopes ≠ [] ⇒
    FLOOKUP (HD s'.scopes) id = NONE
Proof
  rpt strip_tac >>
  SPOSE_NOT_THEN ASSUME_TAC >>
  Cases_on `FLOOKUP (HD s'.scopes) id` >> gvs[] >>
  drule eval_stmts_new_in_head_not_in_tail >>
  disch_then (qspec_then `id` mp_tac) >>
  simp[finite_mapTheory.FLOOKUP_DEF] >>
  conj_tac >- gvs[finite_mapTheory.FLOOKUP_DEF] >>
  drule eval_stmts_preserves_scopes_dom >>
  simp[preserves_scopes_dom_def] >> strip_tac >>
  SPOSE_NOT_THEN ASSUME_TAC >> gvs[] >>
  `MAP FDOM (TL s'.scopes) = MAP FDOM rest` by simp[] >>
  drule_all lookup_scopes_none_map_fdom >> gvs[]
QED

(* Generalized version: after eval_stmts under a pushed scope sc,
   popping preserves tv. For ids not in FDOM sc, uses
   lookup_scopes_not_in_new_head. For ids in FDOM sc, uses
   eval_stmts_preserves_tail_lookup (the body finds them in the head
   first, so the tail entry is unchanged). *)
Theorem eval_stmts_scope_bracket_gen_preserves_tv:
  ∀cx ss sc st res st'.
    eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st') ∧
    preserves_tv cx (st with scopes updated_by CONS sc) st' ⇒
    preserves_tv cx st (st' with scopes := TL st'.scopes)
Proof
  rw[]
  \\ drule eval_stmts_preserves_scopes_len \\ rw[]
  \\ gvs[preserves_tv_def] \\ rw[]
  \\ Cases_on`st'.scopes` \\ gvs[]
  \\ first_x_assum(qspec_then`SUC i`mp_tac)
  \\ rw[]
QED

Theorem new_variable_preserves_tv:
  ∀id tv v cx st res st'.
    new_variable id tv v st = (res, st') ⇒
    preserves_tv cx st st'
Proof
  rw[new_variable_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
     list_CASE_rator, get_scopes_def,return_def, raise_def] >>
  imp_res_tac type_check_state >> gvs[] >>
  gvs[set_scopes_def, return_def] >>
  gvs[preserves_tv_def, lookup_scopes_def, type_check_def,
      assert_def, AllCaseEqs()] >>
  rw[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on`i` \\ gvs[] >>
  rw[finite_mapTheory.FLOOKUP_UPDATE] >> gvs[]
QED

(* assign_target preserves tv *)
Theorem assign_target_preserves_tv:
  (∀cx gv ao st res st'.
     assign_target cx gv ao st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (res, st') ⇒
     preserves_tv cx st st')
Proof
  ho_match_mp_tac assign_target_ind >>
  conj_tac >- (
    (* ScopedVar *)
    rpt strip_tac >>
    gvs[assign_target_def, bind_def, raise_def,
       get_scopes_def, return_def, option_CASE_rator,
       lift_option_def, AllCaseEqs()] >>
    pairarg_tac >> gvs[set_scopes_def, return_def,
      bind_apply, ignore_bind_apply, AllCaseEqs()] >>
    imp_res_tac lift_sum_state >> gvs[] >>
    imp_res_tac assign_result_state >> gvs[] >>
    gvs[preserves_tv_def] >>
    drule find_containing_scope_structure >> rw[] >>
    Cases_on`i < LENGTH pre` \\ gvs[rich_listTheory.EL_APPEND1] >>
    Cases_on`i > LENGTH pre` \\
    gvs[rich_listTheory.EL_APPEND, rich_listTheory.EL_CONS,
        arithmeticTheory.PRE_SUB1] >>
    `i = LENGTH pre` by gvs[] >> gvs[] >>
    gvs[finite_mapTheory.FLOOKUP_UPDATE] >> rw[] >> gvs[]) >>
  conj_tac >- (
    (* TopLevelVar *)
    rpt strip_tac >>
    imp_res_tac assign_target_toplevel_scopes_immutables >>
    gvs[preserves_tv_def] ) >>
  conj_tac >- (
    (* ImmutableVar — scopes unchanged; same as TopLevelVar pattern *)
    rpt strip_tac >>
    qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
    simp[Once vyperStateTheory.assign_target_def, bind_def,
        return_def, vyperStateTheory.raise_def, ignore_bind_def,
        vyperStateTheory.lift_option_def, vyperStateTheory.lift_option_type_def,
        vyperStateTheory.lift_sum_def,
        vyperStateTheory.get_immutables_def,
        vyperStateTheory.get_address_immutables_def,
        vyperStateTheory.set_immutable_def,
        vyperStateTheory.set_address_immutables_def,
        AllCaseEqs()] >>
    rpt strip_tac >> gvs[] >>
    imp_res_tac assign_result_state >> gvs[] >>
    gvs[AllCaseEqs(),raise_def,return_def,preserves_tv_def,
        option_CASE_rator, sum_CASE_rator] >>
    gvs[get_source_immutables_def,set_source_immutables_def] >>
    rw[] >> CASE_TAC >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[] >> gvs[alistTheory.ALOOKUP_ADELKEY]) >>
  (* TupleTargetV Replace + error cases + assign_targets *)
  rpt strip_tac
  >> gvs[vyperStateTheory.assign_target_def, bind_def, return_def,
         vyperStateTheory.raise_def, ignore_bind_def,
         vyperStateTheory.type_check_def, AllCaseEqs()]
  >> TRY (gvs[vyperStateTheory.assert_def] >>
         first_x_assum drule_all >> strip_tac >> gvs[] >> NO_TAC)
  >> first_x_assum drule
  >> first_x_assum drule
  >> metis_tac[preserves_tv_trans]
QED

(* TODO: move *)
Theorem handle_function_state:
  handle_function x y = (a,b) ==> b = y
Proof
  simp[oneline handle_function_def]
  >> CASE_TAC >> rw[raise_def, return_def]
QED

Theorem eval_preserves_tv:
  (∀cx s st res st'. eval_stmt cx s st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx ss st res st'. eval_stmts cx ss st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx it st res st'. eval_iterator cx it st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx g st res st'. eval_target cx g st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx gs st res st'. eval_targets cx gs st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒
     preserves_tv cx st st')
Proof
  ho_match_mp_tac evaluate_ind >>
  conj_tac >- rw[evaluate_def, return_def] >>
  conj_tac >- rw[evaluate_def, raise_def] >>
  conj_tac >- rw[evaluate_def, raise_def] >>
  conj_tac >- rw[evaluate_def, raise_def] >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, AllCaseEqs(), raise_def] >>
    imp_res_tac materialise_state >> gvs[] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, AllCaseEqs(), raise_def] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac get_Value_state >> gvs[] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac get_Value_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac get_Value_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac get_Value_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac get_Value_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac get_Value_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def, bind_apply, AllCaseEqs(), push_log_def, return_def] >>
    first_x_assum drule >>
    gvs[preserves_tv_def] ) >>
  conj_tac >- (
    rw[evaluate_def, bind_apply, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac materialise_state >>
    imp_res_tac new_variable_immutables >>
    imp_res_tac new_variable_preserves_tv >>
    gvs[] >> first_x_assum drule_all >> gvs[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    reverse $ rw[evaluate_def, bind_def, AllCaseEqs()]
    >- (first_x_assum drule \\ rw[]) >>
    pairarg_tac >> gvs[bind_apply, ignore_bind_apply, AllCaseEqs(),
                       return_def] >>
    imp_res_tac materialise_state >>
    imp_res_tac assign_target_preserves_tv >>
    gvs[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def, bind_apply, ignore_bind_apply] >>
    gvs[AllCaseEqs(), return_def] >>
    imp_res_tac materialise_state >>
    imp_res_tac assign_target_preserves_tv >>
    gvs[] >>
    rpt(first_x_assum drule) >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    reverse $ rw[evaluate_def, bind_def, AllCaseEqs()]
    >- (first_x_assum drule \\ rw[]) >>
    pairarg_tac >> gvs[bind_apply, ignore_bind_apply, AllCaseEqs(),
                       return_def] >>
    imp_res_tac get_Value_state >>
    imp_res_tac assign_target_preserves_tv >>
    gvs[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    reverse $ rw[evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs()]
    >- (first_x_assum drule \\ rw[])
    >- (first_x_assum drule_all \\ rw[] >>
        gvs[push_scope_def, return_def]) >>
    first_x_assum drule_all >>
    gvs[push_scope_def, return_def] >>
    first_x_assum drule >>
    first_x_assum drule >> rw[] >>
    reverse $
      gvs[finally_def, switch_BoolV_def, AllCaseEqs(), COND_RATOR,
          raise_def]
    >- (
      gvs[ignore_bind_apply, raise_def, pop_scope_def, return_def] >>
      gvs[preserves_tv_def] ) >>
    rpt(first_x_assum drule) >>
    gvs[ignore_bind_apply, pop_scope_def, raise_def, AllCaseEqs(),
        return_def] >>
    TRY ( drule eval_stmts_preserves_scopes_len \\ rw[] \\ NO_TAC ) >>
    strip_tac >>
    drule eval_stmts_scope_bracket_gen_preserves_tv >>
    rw[] >> metis_tac[preserves_tv_trans]) >>
  (* For *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    pop_assum mp_tac >>
    simp_tac std_ss [evaluate_def, bind_apply, ignore_bind_apply, LET_THM] >>
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >> gvs[] >>
    first_x_assum drule >> strip_tac >>
    BasicProvers.TOP_CASE_TAC >>
    first_x_assum drule >> strip_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    CASE_TAC >>
    imp_res_tac check_state >> gvs[] >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    gvs[] >> strip_tac >>
    first_x_assum drule_all >>
    strip_tac >>
    irule preserves_tv_trans >> goal_assum drule >>
    simp[]) >>
  (* Expr *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs()] >>
    imp_res_tac type_check_state >> gvs[]) >>
  (* eval_stmts [] *)
  conj_tac >- rw[evaluate_def, return_def] >>
  (* eval_stmts s::ss *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs()] >>
    TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
    rpt (first_x_assum drule_all >> strip_tac) >>
    metis_tac[preserves_tv_trans]) >>
  (* Array iterator *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac materialise_state >> gvs[return_def] >>
    first_x_assum drule >> rw[]) >>
  (* Range iterator *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(), return_def] >>
    imp_res_tac get_Value_state >>
    imp_res_tac lift_sum_state >> gvs[] >>
    TRY (first_x_assum drule >> rw[] >> NO_TAC) >>
    first_x_assum drule_all >> strip_tac >>
    first_x_assum drule_all >> strip_tac >>
    irule preserves_tv_trans >> first_assum (irule_at Any) >> simp[]) >>
  (* BaseTarget *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
    TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
    pairarg_tac >> gvs[return_def] >>
    first_x_assum drule_all >> simp[]) >>
  (* TupleTarget *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
    first_x_assum drule_all >> simp[]) >>
  (* eval_targets [] *)
  conj_tac >- rw[evaluate_def, return_def] >>
  (* eval_targets g::gs *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply,
        return_def, AllCaseEqs()] >>
    TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
    rpt (first_x_assum drule_all >> strip_tac) >>
    metis_tac[preserves_tv_trans]) >>
  (* NameTarget *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), get_scopes_def,
       return_def, raise_def, type_check_def, assert_def,
       ignore_bind_def]) >>
  (* BareGlobalNameTarget *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
    imp_res_tac get_immutables_state >>
    imp_res_tac type_check_state >>
    imp_res_tac lift_option_type_state >> gvs[]) >>
  (* TopLevelNameTarget *)
  conj_tac >- rw[Once evaluate_def, return_def] >>
  (* AttributeTarget *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
    TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
    pairarg_tac >> gvs[return_def] >>
    first_x_assum drule_all >> simp[]) >>
  (* SubscriptTarget *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
    imp_res_tac get_Value_state >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
    pairarg_tac >> gvs[bind_apply, AllCaseEqs(), return_def] >>
    imp_res_tac get_Value_state >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans]) >>
  (* eval_for [] *)
  conj_tac >- rw[evaluate_def, return_def] >>
  (* eval_for v::vs *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    pop_assum mp_tac >>
    simp_tac std_ss [evaluate_def, bind_apply, ignore_bind_apply] >>
    (* push_scope_with_var *)
    BasicProvers.TOP_CASE_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      rw[] >> gvs[push_scope_with_var_def, return_def]) >>
    first_x_assum drule >> strip_tac >>
    first_x_assum drule >> strip_tac >>
    CASE_TAC >>
    CASE_TAC >- (
      first_x_assum drule >>
      reverse $ rw[return_def]
      >- (
        first_x_assum drule >>
        gvs[finally_def, try_def, ignore_bind_apply] >>
        gvs[AllCaseEqs(), return_def, raise_def, pop_scope_def,
            push_scope_with_var_def] >>
        first_x_assum drule >> rw[] >>
        irule preserves_tv_trans >>
        goal_assum $ drule_at Any >>
        drule eval_stmts_scope_bracket_gen_preserves_tv >> gvs[] >>
        imp_res_tac handle_loop_exception_state >> gvs[])
      >- (
        gvs[finally_def, try_def, ignore_bind_apply] >>
        gvs[AllCaseEqs(), return_def, raise_def, pop_scope_def,
            push_scope_with_var_def] >>
        first_x_assum drule >> rw[] >>
        imp_res_tac handle_loop_exception_state >> gvs[] >>
        drule eval_stmts_scope_bracket_gen_preserves_tv >> gvs[])) >>
    rw[] >>
    first_x_assum(qspec_then`ARB`kall_tac) >>
    gvs[finally_def, try_def, AllCaseEqs(), ignore_bind_apply,
        return_def, pop_scope_def, raise_def] >>
    imp_res_tac eval_stmts_preserves_scopes_len >>
    gvs[push_scope_with_var_def, return_def] >>
    imp_res_tac handle_loop_exception_state >> gvs[] >>
    first_x_assum drule >> rw[] >>
    drule eval_stmts_scope_bracket_gen_preserves_tv >>
    rw[]) >>
  (* Name *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs(),
         get_scopes_def, return_def, raise_def,
         lift_option_type_def, option_CASE_rator]) >>
  (* BareGlobalName *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
    imp_res_tac get_immutables_state >>
    imp_res_tac lift_option_type_state >> gvs[]) >>
  (* TopLevelName *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def] >>
    imp_res_tac lookup_global_state >> gvs[]) >>
  (* FlagMember *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac lookup_flag_mem_state >> gvs[]) >>
  (* IfExp *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(),
         switch_BoolV_def, COND_RATOR, return_def, raise_def] >>
    TRY (first_x_assum drule >> rw[] >> NO_TAC) >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans]) >>
  (* Literal *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, return_def, bind_apply, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >> gvs[]) >>
  (* StructLit *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, return_def, bind_apply, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    first_x_assum drule >> rw[]) >>
  (* Subscript expr *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, return_def, bind_apply,
        ignore_bind_apply, AllCaseEqs(), sum_CASE_rator,
         prod_CASE_rator] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac check_array_bounds_state >>
    imp_res_tac lift_sum_state >>
    imp_res_tac get_Value_state >>
    imp_res_tac read_storage_slot_state >> gvs[] >>
    rpt (first_x_assum drule) >> rw[] >>
    irule preserves_tv_trans
    >> goal_assum drule
    >> first_x_assum drule
    >> rw[]) >>
  (* Attribute expr *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, return_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    imp_res_tac lift_sum_state >> gvs[] >>
    imp_res_tac get_Value_state >> gvs[] >>
    first_x_assum drule >> rw[]) >>
  (* Builtin *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply,
        AllCaseEqs(), COND_RATOR, return_def] >>
    imp_res_tac type_check_state >>
    imp_res_tac lift_sum_state >>
    imp_res_tac materialise_state >>
    imp_res_tac toplevel_array_length_state >> gvs[] >>
    rpt(first_x_assum drule >> rw[]) >>
    gvs[get_accounts_def, return_def]) >>
  (* Pop *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac assign_target_preserves_tv >> gvs[] >>
    TRY (first_x_assum drule_all >> rw[] >> NO_TAC) >>
    pairarg_tac >> gvs[bind_apply, AllCaseEqs(), return_def] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac assign_target_preserves_tv >> gvs[] >>
    first_x_assum drule_all >> strip_tac >>
    irule preserves_tv_trans >> first_assum (irule_at Any) >> simp[]) >>
  (* TypeBuiltin *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(),
        ignore_bind_apply, return_def] >>
    imp_res_tac type_check_state >>
    imp_res_tac lift_sum_state >> gvs[] >>
    first_x_assum drule_all >> rw[]) >>
  (* Send *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
         return_def] >>
    imp_res_tac type_check_state >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac transfer_value_scopes >> gvs[] >>
    TRY (
      qmatch_assum_rename_tac`ss1.scopes = ss2.scopes` >>
      `ss1.immutables = ss2.immutables` by (
        gvs[transfer_value_def, bind_apply, ignore_bind_apply,
            check_def, assert_def, update_accounts_def,
            get_accounts_def, return_def, AllCaseEqs()] ) ) >>
    gvs[] >> first_x_assum drule_all >> rw[] >>
    gvs[preserves_tv_def] ) >>
  (* ExtCall *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    pop_assum mp_tac >>
    simp_tac std_ss [evaluate_def, bind_apply, ignore_bind_apply] >>
    BasicProvers.TOP_CASE_TAC >> first_x_assum drule >> strip_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    first_x_assum drule >> strip_tac >>
    BasicProvers.TOP_CASE_TAC >> imp_res_tac check_state >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    first_x_assum drule >> strip_tac >>
    BasicProvers.TOP_CASE_TAC >> imp_res_tac lift_option_type_state >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule >> strip_tac >>
    simp[bind_def] >>
    BasicProvers.TOP_CASE_TAC >>
    qmatch_assum_rename_tac`_ r = (_, rrr)` >>
    sg `rrr = r` >- (
      first_x_assum(qspec_then`ARB`kall_tac) >>
      gvs[COND_RATOR, AllCaseEqs(), return_def, ignore_bind_apply,
          bind_apply] >>
      imp_res_tac check_state >>
      imp_res_tac lift_option_type_state >>
      rw[] >> gvs[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    pairarg_tac >>
    BasicProvers.VAR_EQ_TAC >>
    simp_tac std_ss [] >>
    simp[bind_apply] >>
    BasicProvers.TOP_CASE_TAC >>
    first_x_assum drule >>
    simp_tac std_ss [] >>
    strip_tac >>
    imp_res_tac lift_option_state >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- ( rw[] >> rw[] ) >>
    first_x_assum drule >> strip_tac >>
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac get_accounts_state >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- ( rw[] >> rw[] ) >>
    first_x_assum drule >> strip_tac >>
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac get_transient_storage_state >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- ( rw[] >> rw[] ) >>
    first_x_assum drule >> strip_tac >>
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac lift_option_state >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- ( rw[] >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pairarg_tac >>
    BasicProvers.VAR_EQ_TAC >>
    simp_tac std_ss [] >>
    simp[ignore_bind_apply] >>
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac check_state >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- ( rw[] >> rw[] ) >>
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac update_accounts_scopes >>
    imp_res_tac update_accounts_immutables >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      rw[] >> gvs[preserves_tv_def] ) >>
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac update_transient_scopes >>
    imp_res_tac update_transient_immutables >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      rw[] >> gvs[preserves_tv_def] ) >>
    reverse IF_CASES_TAC >- (
      simp[bind_apply, AllCaseEqs(), return_def] >>
      rw[] >> imp_res_tac lift_sum_runtime_state >> gvs[] >>
      irule preserves_tv_trans >>
      goal_assum drule >>
      gvs[preserves_tv_def] ) >>
    strip_tac >> gvs[] >>
    first_x_assum drule_all >>
    rw[] >>
    irule preserves_tv_trans >>
    goal_assum drule >>
    irule preserves_tv_trans >>
    goal_assum $ drule_at Any >>
    gvs[preserves_tv_def]) >>
  (* IntCall *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    pop_assum mp_tac >>
    simp_tac std_ss [evaluate_def, bind_apply, ignore_bind_apply] >>
    (* check recursion *)
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac check_state >> BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    (* lift_option_type get_module_code *)
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    (* lift_option_type lookup_callable_function *)
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    (* LET bindings *)
    BasicProvers.LET_ELIM_TAC >>
    BasicProvers.VAR_EQ_TAC >>
    first_x_assum $ funpow 2 drule_then drule >>
    simp_tac std_ss [] >> strip_tac >>
    first_x_assum $ funpow 2 drule_then drule >>
    simp_tac std_ss [] >> strip_tac >>
    first_x_assum $ funpow 2 drule_then drule >>
    simp_tac std_ss [] >> strip_tac >>
    qpat_x_assum`_ = (_ ,_)`mp_tac >>
    simp_tac std_ss [ignore_bind_apply] >>
    (* type_check *)
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    (* eval_exprs cx es — consume IH *)
    simp_tac std_ss [bind_apply] >>
    BasicProvers.TOP_CASE_TAC >>
    rev_full_simp_tac std_ss [] >>
    first_x_assum drule >> strip_tac >>
    first_x_assum drule >> strip_tac >>
    first_x_assum drule_all >> strip_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (rw[] >> rw[]) >>
    BasicProvers.LET_ELIM_TAC >>
    qpat_x_assum`_ = (_ ,_)`mp_tac >>
    simp_tac std_ss [bind_apply] >>
    (* eval_exprs cxd needed_dflts — consume IH *)
    BasicProvers.TOP_CASE_TAC >>
    first_x_assum drule_all >> strip_tac >>
    sg `preserves_tv cx r r'` >- (
      irule preserves_tv_trans >>
      goal_assum drule >>
      irule (iffRL preserves_tv_txn_eq) >>
      goal_assum $ drule_at Any >>
      simp[Abbr`cxd`]) >>
    reverse BasicProvers.TOP_CASE_TAC >- ( rw[] >> rw[] ) >>
    BasicProvers.LET_ELIM_TAC >>
    first_x_assum $ drule_then drule >> strip_tac >>
    qpat_x_assum`_ = (_ ,_)`mp_tac >>
    simp_tac std_ss [bind_apply] >>
    (* lift_option_type bind_arguments *)
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
    BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- ( rw[] >> rw[] ) >>
    (* get_scopes *)
    simp_tac (srw_ss()) [get_scopes_def, return_def] >>
    (* lift_option_type evaluate_type *)
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac lift_option_type_state >> rpt BasicProvers.VAR_EQ_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- ( rw[] >> rw[] ) >>
    (* push_function *)
    BasicProvers.TOP_CASE_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      rw[] >> gvs[push_function_def, return_def] ) >>
    first_x_assum drule >>
    simp_tac (srw_ss()) [get_scopes_def, return_def] >>
    disch_then $ drule_then drule >>
    strip_tac >>
    (* finally (try eval_stmts handle_function) (pop_function prev) *)
    simp[finally_def, try_def, ignore_bind_apply] >>
    CASE_TAC >>
    first_x_assum drule >> strip_tac >>
    CASE_TAC >> gvs[return_def]
    >- (
      rw[pop_function_def, set_scopes_def, return_def,
         lift_option_type_def] >>
      gvs[AllCaseEqs(), option_CASE_rator, raise_def, return_def] >>
      irule preserves_tv_trans >>
      goal_assum drule >>
      gvs[push_function_def, return_def] >>
      drule_at Any (iffRL preserves_tv_txn_eq) >>
      disch_then(qspec_then`cx`mp_tac) >>
      simp[Abbr`cxd`] >>
      rw[preserves_tv_def] ) >>
    CASE_TAC >>
    imp_res_tac handle_function_state >> gvs[] >>
    CASE_TAC >>
    gvs[pop_function_def, set_scopes_def, return_def, raise_def] >>
    CASE_TAC >> gvs[] >> TRY CASE_TAC >> imp_res_tac lift_option_type_state >>
    gvs[] >> TRY CASE_TAC >> gvs[] >> rw[] >>
    irule preserves_tv_trans >>
    goal_assum drule >>
    gvs[push_function_def, return_def] >>
    drule_at Any (iffRL preserves_tv_txn_eq) >>
    disch_then(qspec_then`cx`mp_tac) >>
    simp[Abbr`cxd`] >>
    rw[preserves_tv_def]) >>
  (* eval_exprs [] *)
  conj_tac >- rw[evaluate_def, return_def] >>
  (* eval_exprs e::es *)
  (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
   gvs[Once evaluate_def, bind_apply, AllCaseEqs()] >>
   imp_res_tac materialise_state >> gvs[] >>
   TRY (first_x_assum drule >> rw[] >> NO_TAC) >>
   first_x_assum drule_all >> strip_tac >>
   first_x_assum drule_all >> strip_tac >>
   irule preserves_tv_trans >> first_assum (irule_at Any) >>
   gvs[return_def])
QED
