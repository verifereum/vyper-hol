Theory vyperEvalPreservesScopes
Ancestors
  pair vyperCallFrame vyperCallOutcomeFrame vyperCallOutcome[ignore_grammar]
  vyperTypeInvariants
  vyperState vyperCreate vyperInterpreter vyperLookup
  vyperEvalExprPreservesScopesDom vyperScopePreservation
  vyperMisc vyperImmutablesPreservation vyperStatePreservation vyperPlaceFrames

(* Preserve the existing statement-list free variables against crypto's body. *)
val _ = hide "body";

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
  imp_res_tac read_result_scopes >> imp_res_tac raise_scopes >>
  imp_res_tac read_result_scopes >> gvs[]
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
  imp_res_tac read_result_scopes >>
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
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  gvs[switch_BoolV_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_scopes >>
  gvs[COND_RATOR, AllCaseEqs(), return_def, raise_def] >>
  gvs[bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_scopes >>
  gvs[] >> metis_tac[]
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
  imp_res_tac lift_option_scopes >>
  imp_res_tac push_log_scopes >> gvs[]
QED

Theorem case_Append_dom[local]:
  ∀cx bt e st res st'.
    eval_stmt cx (Append bt e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac eval_target_place_preserves_scopes_dom >>
  imp_res_tac eval_expr_preserves_scopes_dom >>
  imp_res_tac read_result_state >> imp_res_tac append_place_scopes_dom >>
  gvs[] >> metis_tac[]
QED

Theorem place_evaluators_scopes_dom[local]:
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==>
     MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==>
     MAP FDOM st.scopes = MAP FDOM st'.scopes)
Proof
  `(!(cx:evaluation_context) (s:stmt). T) /\
   (!(cx:evaluation_context) (ss:stmt list). T) /\
   (!(cx:evaluation_context) (it:iterator). T) /\
   (!(cx:evaluation_context) (ty:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
   (!(cx:evaluation_context) (e:expr). T) /\
   (!(cx:evaluation_context) (es:expr list). T) /\
   (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
   (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
   (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==>
      MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
   (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==>
      MAP FDOM st.scopes = MAP FDOM st'.scopes)` suffices_by metis_tac[] >>
  ho_match_mp_tac evaluate_ind >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `assign_tuple_targets _ (BaseTarget _) _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac eval_target_place_preserves_scopes_dom >>
      imp_res_tac write_place_scopes_dom >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> Cases_on `v` >>
      simp[Once evaluate_def, raise_def] >>
      Cases_on `a` >> simp[Once evaluate_def, raise_def])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def, raise_def, AllCaseEqs()])
  >> rpt strip_tac >>
  qpat_x_assum `assign_tuple_target_list cx _ _ st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), raise_def] >>
  strip_tac >> metis_tac[]
QED

Theorem case_Assign_map_fdom[local]:
  !cx g e st res st'. eval_stmt cx (Assign g e) st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt gen_tac >> Cases_on `g` >> strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac place_evaluators_scopes_dom >>
  imp_res_tac eval_target_place_preserves_scopes_dom >>
  imp_res_tac eval_expr_preserves_scopes_dom >>
  imp_res_tac read_result_state >>
  imp_res_tac read_result_scopes >> imp_res_tac read_result_scopes >>
  imp_res_tac write_place_scopes_dom >> gvs[] >> metis_tac[]
QED

Theorem case_Assign_dom[local]:
  eval_stmt cx (Assign g e) st = (res,st') ==> preserves_scopes_dom st st'
Proof
  metis_tac[case_Assign_map_fdom, map_fdom_eq_preserves_dom]
QED

Theorem case_AugAssign_map_fdom[local]:
  !cx ty bt bop e st res st'.
    eval_stmt cx (AugAssign ty bt bop e) st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac place_evaluators_scopes_dom >>
  imp_res_tac eval_target_place_preserves_scopes_dom >>
  imp_res_tac eval_expr_preserves_scopes_dom >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac read_result_scopes >> imp_res_tac lift_sum_state >>
  imp_res_tac write_place_scopes_dom >> gvs[] >> metis_tac[]
QED

Theorem case_AugAssign_dom[local]:
  eval_stmt cx (AugAssign ty bt bop e) st = (res,st') ==> preserves_scopes_dom st st'
Proof
  metis_tac[case_AugAssign_map_fdom, map_fdom_eq_preserves_dom]
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
  imp_res_tac read_result_scopes >> imp_res_tac return_scopes >>
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
    imp_res_tac read_result_scopes >>
    imp_res_tac read_result_scopes >> gvs[] >>
    Cases_on `s'³'.scopes` >> gvs[] >-
    gvs[new_variable_def, bind_def, get_scopes_def, return_def, check_def, type_check_def, assert_def, lookup_scopes_def, ignore_bind_def, raise_def] >>
    `s'⁴'.scopes ≠ []` by simp[] >>
    drule_all new_variable_scope_property >> strip_tac >> gvs[] >>
    Cases_on `st.scopes` >> gvs[]
  ) >~
  (* read_result cx/read_result error case *)
  [`read_result _ _ _ = (INR _, _)`]
  >- (
    imp_res_tac read_result_scopes >> gvs[] >>
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
  gvs[switch_BoolV_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  rename1 `read_result cx tv st1 = (INL v,st1)` >>
  Cases_on `v = BoolV T` >> gvs[]
  >- (qpat_x_assum `∀st res st'. eval_stmts _ ss1 _ = _ ⇒ _` drule >>
      gvs[preserves_scopes_dom_def] >> strip_tac >> gvs[]) >>
  Cases_on `v = BoolV F` >> gvs[raise_def] >>
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
  gvs[switch_BoolV_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  rename1 `read_result cx tv st1 = (INL v,st1)` >>
  Cases_on `v = BoolV T` >> gvs[]
  >- (qpat_x_assum `∀st res st'. eval_stmts _ ss1 _ = _ ⇒ _` drule >>
      gvs[preserves_scopes_dom_def] >> strip_tac >> gvs[]) >>
  Cases_on `v = BoolV F` >> gvs[raise_def] >>
  qpat_x_assum `∀st res st'. eval_stmts _ ss2 _ = _ ⇒ _` drule >>
  gvs[preserves_scopes_dom_def] >> strip_tac >> gvs[]
QED

Theorem case_For_dom[local]:
  ∀cx id typ it n body.
    (* IH for eval_for: conditional on lift_option_type, eval_iterator and check succeeding *)
    (∀tenv s'' tyv t s'³' vs t' s'⁴' x t''.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv, t) ∧
       eval_iterator cx it s'³' = (INL vs, t') ∧
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'⁴' = (INL x, t'') ⇒
       ∀st res st'. eval_for cx tyv id body vs st = (res, st') ⇒
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
  rename1 `eval_for cx tyv nm loop_body (v::vs) st = (res,st')` >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, push_scope_with_var_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* Handle error case from finally: unfold and use try_body_preserves_tl_dom *)
  TRY (
    gvs[finally_def, AllCaseEqs(), bind_def, ignore_bind_def, pop_scope_def, return_def, raise_def] >>
    qspecl_then [`cx`, `loop_body`, `nm`, `tyv`, `v`, `st`] mp_tac try_body_preserves_tl_dom >>
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
  sg `MAP FDOM (TL (st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v; popped := [] |>))).scopes) = MAP FDOM (TL s'³'.scopes)` >-
  (qspecl_then [`cx`, `loop_body`, `nm`, `tyv`, `v`, `st`] mp_tac try_body_preserves_tl_dom >>
   impl_tac >- (rpt strip_tac >> gvs[push_scope_with_var_def, return_def] >> first_x_assum drule >> simp[]) >>
   simp[push_scope_with_var_def, return_def] >> strip_tac >>
   first_x_assum drule >> simp[]) >> gvs[] >>
  (* Case split on broke *)
  Cases_on `broke` >> gvs[return_def, preserves_scopes_dom_def] >-
  (* broke = T: return () *)
  (Cases_on `st.scopes` >> Cases_on `tl` >> gvs[]) >>
  (* broke = F: use recursive IH *)
  qpat_x_assum `∀s'⁴' t s'⁵' t'. _ ⇒ _` (qspecl_then [`st`, `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v; popped := [] |>))`,
                                                       `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v; popped := [] |>))`,
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
  imp_res_tac read_result_scopes >> imp_res_tac read_result_scopes >>
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
  imp_res_tac read_result_scopes >> imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >>
  imp_res_tac return_scopes >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[])
QED

(* Canonical ten-function scope-domain interface. *)
Theorem scopes_dom_extended[local]:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> preserves_scopes_dom st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> preserves_scopes_dom st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx ty nm body vs st res st'. eval_for cx ty nm body vs st = (res,st') ==> preserves_scopes_dom st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes)
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
     imp_res_tac read_result_scopes >> gvs[] >>
     qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
     simp[switch_BoolV_def] >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     Cases_on `v' = BoolV T` >>
     gvs[return_def, eval_expr_preserves_scopes_dom] >>
     Cases_on `v' = BoolV F` >>
     gvs[return_def, raise_def, bind_def, AllCaseEqs()] >>
     imp_res_tac eval_expr_preserves_scopes_dom >>
     imp_res_tac read_result_state >>
     imp_res_tac lift_option_type_state >> gvs[] >>
     metis_tac[eval_expr_preserves_scopes_dom])
  (* Log *) >- (drule_all case_Log_dom >> gvs[])
  (* AnnAssign *) >- (drule case_AnnAssign_dom >> simp[])
  (* Append *) >- (drule case_Append_dom >> simp[])
  (* Assign base/tuple *) >- (drule case_Assign_dom >> simp[])
  >- (drule case_Assign_dom >> simp[])
  (* AugAssign *) >- (drule case_AugAssign_dom >> simp[])
  (* If *) >- (irule case_If_dom >> qexists_tac `cx` >> qexists_tac `e` >> qexists_tac `res` >> qexists_tac `ss` >> qexists_tac `ss'` >>
    gvs[push_scope_def, return_def] >> metis_tac[])
  (* For *) >- (drule_all case_For_dom >> simp[])
  (* Expr *) >- (drule_all case_Expr_dom >> gvs[])
  (* === eval_stmts cases === *)
  (* [] *) >- gvs[evaluate_def, return_def, preserves_scopes_dom_def]
  (* s::ss *) >- (drule_all case_eval_stmts_cons_dom >> gvs[])
  (* === Iterator cases === *)
  (* Array *) >- (drule_all case_Array_iterator_dom >> gvs[])
  (* Range *) >- (drule case_Range_iterator_dom >> metis_tac[eval_expr_preserves_scopes_dom])
  (* === eval_for cases === *)
  (* [] *) >- gvs[evaluate_def, return_def, preserves_scopes_dom_def]
  (* v::vs *) >- (drule case_eval_for_cons_dom >> metis_tac[])
  (* === Expression cases - use eval_expr_preserves_scopes_dom === *)
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  (* chain interaction builtins *)
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_expr_preserves_scopes_dom
  >- drule_all_then ACCEPT_TAC eval_exprs_preserves_scopes_dom
  >- (drule eval_exprs_preserves_scopes_dom >> gvs[])
  >- metis_tac[eval_base_place_preserves_scopes_dom]
  >- metis_tac[eval_base_place_preserves_scopes_dom]
  >- metis_tac[eval_base_place_preserves_scopes_dom]
  >- metis_tac[eval_base_place_preserves_scopes_dom]
  >- metis_tac[eval_target_place_preserves_scopes_dom]
  >- metis_tac[place_evaluators_scopes_dom]
  >- metis_tac[place_evaluators_scopes_dom]
  >- metis_tac[place_evaluators_scopes_dom]
  >> metis_tac[place_evaluators_scopes_dom]
QED

(* ------------------------------------------------------------------------
   Main theorems
   ------------------------------------------------------------------------ *)




Theorem eval_stmts_preserves_scopes_dom:
  ∀cx st st' ss res.
    eval_stmts cx ss st = (res, st') ⇒
    preserves_scopes_dom st st'
Proof
  metis_tac[scopes_dom_extended]
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

Theorem eval_stmts_preserves_tail_lookup_none:
  !cx ss st sc rest res st' id h t.
    eval_stmts cx ss (st with scopes := sc::rest) = (res, st') /\
    lookup_scopes id rest = NONE /\
    st'.scopes = h::t ==>
    lookup_scopes id t = NONE
Proof
  rpt strip_tac >>
  irule lookup_scopes_none_map_fdom >>
  qexists_tac `rest` >> simp[] >>
  drule eval_stmts_preserves_scopes_dom >>
  simp[preserves_scopes_dom_def]
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

Theorem new_in_head_extended[local]:
  (!cx s st res st'. eval_stmt cx s st = (res, st') ==>
    st.scopes <> [] ==>
    !id. id IN FDOM (HD st'.scopes) /\ id NOTIN FDOM (HD st.scopes) ==>
         lookup_scopes id (TL st'.scopes) = NONE) /\
  (!cx ss st res st'. eval_stmts cx ss st = (res, st') ==>
    st.scopes <> [] ==>
    !id. id IN FDOM (HD st'.scopes) /\ id NOTIN FDOM (HD st.scopes) ==>
         lookup_scopes id (TL st'.scopes) = NONE) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ==>
    st.scopes <> [] ==>
    !id. id IN FDOM (HD st'.scopes) /\ id NOTIN FDOM (HD st.scopes) ==>
         lookup_scopes id (TL st'.scopes) = NONE) /\
  (!(cx:evaluation_context) (e:expr). T) /\
  (!(cx:evaluation_context) (es:expr list). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T)
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
      imp_res_tac read_result_scopes >>
      imp_res_tac read_result_scopes >>
      imp_res_tac raise_scopes >> gvs[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- ( (* Raise *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      qpat_x_assum`eval_stmt _ _ _ = _`mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac read_result_scopes >>
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
      imp_res_tac read_result_scopes >>
      imp_res_tac lift_option_scopes >>
      imp_res_tac lift_option_type_scopes >> gvs[] >>
      gvs[return_def, raise_def, bind_def, AllCaseEqs(), COND_RATOR] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      imp_res_tac read_result_scopes >>
      imp_res_tac lift_option_type_scopes >>
      imp_res_tac raise_scopes >> gvs[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- (
    rw[evaluate_def, bind_apply] >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      gvs[AllCaseEqs(),raise_def] >>
      imp_res_tac read_result_state >>
      imp_res_tac lift_option_type_state >> gvs[] >>
      drule eval_expr_preserves_scopes_dom >> rw[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- (
    rw[evaluate_def, bind_apply] >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      gvs[AllCaseEqs(),switch_BoolV_def, bind_def, raise_def, COND_RATOR, return_def] >>
      imp_res_tac read_result_state >> gvs[] >>
      drule eval_expr_preserves_scopes_dom >> rw[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- (
    rw[evaluate_def, bind_apply] >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      gvs[AllCaseEqs(),switch_BoolV_def, bind_def, raise_def, COND_RATOR, return_def] >>
      imp_res_tac read_result_state >> gvs[] >>
      drule eval_expr_preserves_scopes_dom >> rw[]) >>
    Cases_on`st.scopes` >> Cases_on`st'.scopes` >> gvs[])
  >> conj_tac >- (
    rw[evaluate_def, bind_apply] >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      gvs[AllCaseEqs(),raise_def, switch_BoolV_def, COND_RATOR,
          bind_apply, return_def] >>
      imp_res_tac read_result_state >>
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
      imp_res_tac lift_option_scopes >>
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
         imp_res_tac read_result_scopes >> gvs[] >>
         Cases_on `st.scopes` >> Cases_on `s'³'.scopes` >> gvs[] >> NO_TAC) >>
    (* success case: apply new_variable_new_not_in_tail *)
    imp_res_tac eval_expr_preserves_scopes_dom >>
    imp_res_tac read_result_scopes >> gvs[] >>
    imp_res_tac read_result_state >> gvs[] >>
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
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by
      (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
       imp_res_tac eval_target_place_preserves_scopes_dom >>
       imp_res_tac eval_expr_preserves_scopes_dom >>
       imp_res_tac read_result_state >>
       imp_res_tac append_place_scopes_dom >> gvs[] >> metis_tac[]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- (
    rpt strip_tac >> imp_res_tac case_Assign_map_fdom >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- (
    rpt strip_tac >> imp_res_tac case_Assign_map_fdom >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- (
    rpt strip_tac >> imp_res_tac case_AugAssign_map_fdom >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- ( (* If *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      irule case_If_map_fdom >>
      qexists_tac `cx` >> qexists_tac `e` >> qexists_tac `res` >>
      qexists_tac `ss` >> qexists_tac `ss'` >>
      metis_tac[scopes_dom_extended, eval_expr_preserves_scopes_dom]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- ( (* For *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by (
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac lift_option_type_scopes >>
      imp_res_tac (cj 3 scopes_dom_extended) >> (* eval_iterator *)
      imp_res_tac check_scopes >> imp_res_tac type_check_scopes >> gvs[] >>
      gvs[ignore_bind_apply, check_def, type_check_def,
          AllCaseEqs(), assert_def] >>
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
      imp_res_tac read_result_scopes >>
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
      imp_res_tac (cj 2 scopes_dom_extended) >>
      gvs[preserves_scopes_dom_def] >>
      (* TL s_mid.scopes = TL st'.scopes (MAP FDOM) *)
      imp_res_tac lookup_scopes_none_map_fdom >> gvs[]) >>
    (* Case 2: id ∉ FDOM (HD s_mid.scopes) — new entry came from ss *)
    last_x_assum $ drule_then (drule_then irule) >> gvs[] >>
    drule (cj 1 scopes_dom_extended) >>
    rw[preserves_scopes_dom_def])
  >> conj_tac >- simp[] (* Array: T *)
  >> conj_tac >- simp[] (* Range: T *)
  >> conj_tac >- (rpt strip_tac >> gvs[evaluate_def, return_def]) (* for [] *)
  >> conj_tac >- ( (* for v::vs *)
    rpt strip_tac >>
    `MAP FDOM st.scopes = MAP FDOM st'.scopes` by
      (irule eval_for_map_fdom >>
       goal_assum $ drule_at Any >> rw[] >>
       metis_tac[scopes_dom_extended]) >>
    Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[])
  >> conj_tac >- simp[] (* Name: T *)
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
  >> conj_tac >- simp[] (* RawCallTarget: T *)
  >> conj_tac >- simp[] (* RawCallCalldataTarget: T *)
  >> conj_tac >- simp[] (* RawLog: T *)
  >> conj_tac >- simp[] (* RawRevert: T *)
  >> conj_tac >- simp[] (* SelfDestructTarget: T *)
  >> conj_tac >- simp[] (* CreateTarget: T *)
  >> conj_tac >- simp[] (* exprs []: T *)
  >> simp[] (* remaining expression/list/resolver/tuple clauses are vacuous *)
QED


Theorem eval_stmts_new_in_head_not_in_tail:
  !cx ss st res st' id.
    eval_stmts cx ss st = (res, st') /\
    st.scopes <> [] /\
    id IN FDOM (HD st'.scopes) /\
    id NOTIN FDOM (HD st.scopes) ==>
    lookup_scopes id (TL st'.scopes) = NONE
Proof
  metis_tac[new_in_head_extended]
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
  ∀n sc pre env old_entry rest.
    find_containing_scope n sc = SOME (pre, env, old_entry, rest) ⇒
    ∀id entry new_v.
      lookup_scopes id sc = SOME entry ⇒
      ∃entry'. lookup_scopes id (pre ++ [env |+ (n, old_entry with value := new_v)] ++ rest) =
           SOME entry' ∧ entry'.type = entry.type
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
  (* FLOOKUP h n = SOME old_entry *)
  gvs[] >>
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
    (∀i id entry. i < LENGTH st.scopes ∧
                 FLOOKUP (EL i st.scopes) id = SOME entry ⇒
                 ∃entry'. FLOOKUP (EL i st'.scopes) id = SOME entry' ∧
                          entry'.type = entry.type ∧
                          entry'.assignable = entry.assignable) ∧
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
  simp[preserves_tv_def] >> rpt strip_tac >>
  res_tac >> res_tac >> metis_tac[]
QED

Theorem preserves_tv_eq:
  ∀cx st st'.
    st'.scopes = st.scopes ∧
    st'.immutables = st.immutables ⇒
    preserves_tv cx st st'
Proof
  simp[preserves_tv_def]
QED

Theorem replace_memory_entry_metadata[local]:
  replace_memory_entry entry path v = INL entry' ==>
  entry'.type = entry.type /\ entry'.assignable = entry.assignable
Proof
  simp[replace_memory_entry_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Theorem write_place_preserves_tv:
  write_place cx p v st = (res,st') ==> preserves_tv cx st st'
Proof
  Cases_on `p`
  >- (strip_tac >> irule preserves_tv_eq >>
      metis_tac[write_storage_place_scopes, write_storage_place_immutables])
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
      drule find_containing_scope_structure >> strip_tac >> gvs[] >>
      imp_res_tac replace_memory_entry_metadata >>
      gvs[preserves_tv_def] >> rpt gen_tac >> strip_tac >>
      Cases_on `i < LENGTH x0` >> gvs[rich_listTheory.EL_APPEND1] >>
      Cases_on `i > LENGTH x0` >>
      gvs[rich_listTheory.EL_APPEND, rich_listTheory.EL_CONS,
          arithmeticTheory.PRE_SUB1] >>
      `i = LENGTH x0` by decide_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >> rw[] >> gvs[]) >>
  simp[write_place_def, bind_def, lift_option_type_def, lift_sum_def,
       get_immutables_def, get_address_immutables_def, set_immutable_def,
       set_address_immutables_def, return_def, raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), return_def, raise_def, preserves_tv_def,
      get_source_immutables_def, set_source_immutables_def] >>
  rw[] >> CASE_TAC >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[alistTheory.ALOOKUP_ADELKEY]
QED

Theorem append_logs_preserves_tv:
  ∀cx logs st res st'.
    append_logs logs st = (res,st') ⇒ preserves_tv cx st st'
Proof
  rpt strip_tac >> irule preserves_tv_eq >>
  imp_res_tac append_logs_scopes >>
  imp_res_tac append_logs_immutables >>
  simp[]
QED

Theorem preserves_tv_stk_update[local]:
  ∀cx f st st'.
    preserves_tv (cx with stk updated_by f) st st' ⇔ preserves_tv cx st st'
Proof
  simp[preserves_tv_def]
QED
Theorem preserves_tv_restore_scopes[local]:
  ∀cx st st' scopes.
    preserves_tv cx (st with scopes := scopes) st' ⇒
    preserves_tv cx st (st' with scopes := st.scopes)
Proof
  rw[preserves_tv_def]
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

Theorem preserves_tv_scope_bracket[local]:
  preserves_tv cx (st with scopes updated_by CONS sc) mid ==>
  preserves_tv cx st (mid with scopes := TL mid.scopes)
Proof
  rw[preserves_tv_def] >>
  Cases_on `mid.scopes` >> gvs[] >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem switch_BoolV_preserves_tv[local]:
  (!s r s'. yes s = (r,s') ==> preserves_tv cx s s') /\
  (!s r s'. no s = (r,s') ==> preserves_tv cx s s') /\
  switch_BoolV cx pv yes no st = (res,st') ==>
  preserves_tv cx st st'
Proof
  rw[switch_BoolV_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  rename1 `read_result cx pv st = (INL loaded,st)` >>
  Cases_on `loaded = BoolV T` >> gvs[] >>
  Cases_on `loaded = BoolV F` >> gvs[raise_def] >>
  metis_tac[]
QED

Theorem finally_pop_preserves_tv[local]:
  (!s r s'. f s = (r,s') ==> preserves_tv cx s s') /\
  finally f pop_scope (st with scopes updated_by CONS sc) = (res,st') ==>
  preserves_tv cx st st'
Proof
  rw[finally_def, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  rename1 `preserves_tv cx (st with scopes updated_by CONS sc) mid` >>
  `mid.scopes <> []` by
    (fs[preserves_tv_def] >> Cases_on `mid.scopes` >> gvs[]) >>
  gvs[ignore_bind_def, bind_def, pop_scope_def, return_def, raise_def, AllCaseEqs()] >>
  drule preserves_tv_scope_bracket >> simp[]
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

Theorem append_place_preserves_tv:
  append_place cx p v st = (res,st') ==> preserves_tv cx st st'
Proof
  Cases_on `p`
  >- (strip_tac >> irule preserves_tv_eq >>
      metis_tac[append_storage_place_scopes_immutables]) >>
  simp[append_place_def, bind_def, lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, lift_sum_def, return_def, raise_def]) >>
  rpt strip_tac >>
  imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
  gvs[] >> metis_tac[write_place_preserves_tv]
QED


Theorem pop_place_preserves_tv:
  pop_place cx p st = (res,st') ==> preserves_tv cx st st'
Proof
  Cases_on `p`
  >- (strip_tac >> irule preserves_tv_eq >>
      metis_tac[pop_storage_place_scopes_immutables])
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
      imp_res_tac lift_sum_state >> imp_res_tac lift_option_type_state >> gvs[] >>
      pairarg_tac >> gvs[bind_def, ignore_bind_def, set_scopes_def, return_def] >>
      drule find_containing_scope_structure >> strip_tac >> gvs[] >>
      gvs[preserves_tv_def] >> rpt gen_tac >> strip_tac >>
      Cases_on `i < LENGTH x0` >> gvs[rich_listTheory.EL_APPEND1] >>
      Cases_on `i > LENGTH x0` >>
      gvs[rich_listTheory.EL_APPEND, rich_listTheory.EL_CONS,
          arithmeticTheory.PRE_SUB1] >>
      `i = LENGTH x0` by decide_tac >>
      gvs[finite_mapTheory.FLOOKUP_UPDATE] >> rw[] >> gvs[]) >>
  simp[pop_place_def, bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       get_immutables_def, get_address_immutables_def, set_immutable_def,
       set_address_immutables_def, return_def, raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), return_def, raise_def, preserves_tv_def,
      get_source_immutables_def, set_source_immutables_def] >>
  rw[] >> CASE_TAC >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[alistTheory.ALOOKUP_ADELKEY]
QED
(* TODO(cleanup): this generic handle_function state-frame fact belongs with
   the interpreter/function-call support lemmas once those are split out. *)
Theorem handle_function_state:
  handle_function x y = (a,b) ==> b = y
Proof
  simp[oneline handle_function_def]
  >> CASE_TAC >> rw[raise_def, return_def]
QED

Theorem acquire_nonreentrant_lock_immutables[local]:
  ∀addr slot is_view st res st'.
    acquire_nonreentrant_lock addr slot is_view st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem release_nonreentrant_lock_immutables[local]:
  ∀addr slot st res st'.
    release_nonreentrant_lock addr slot st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem lock_acquire_cond_scopes_immutables[local]:
  ∀nr slot_opt addr is_view s res s'.
    (if nr then
       case slot_opt of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock addr slot is_view
     else return ()) s = (res, s') ⇒
    s'.scopes = s.scopes ∧ s'.immutables = s.immutables
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[raise_def]
  \\ imp_res_tac acquire_nonreentrant_lock_scopes
  \\ imp_res_tac acquire_nonreentrant_lock_immutables
  \\ gvs[]
QED

Theorem lock_release_cond_scopes_immutables[local]:
  ∀nr is_view slot_opt addr s res s'.
    (if nr ∧ ¬is_view then
       case slot_opt of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock addr slot
     else return ()) s = (res, s') ⇒
    s'.scopes = s.scopes ∧ s'.immutables = s.immutables
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr` \\ gvs[return_def]
  \\ Cases_on `is_view` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[return_def]
  \\ imp_res_tac release_nonreentrant_lock_scopes
  \\ imp_res_tac release_nonreentrant_lock_immutables
  \\ gvs[]
QED

(* Helper: preserves_tv composes when scopes are restored to an intermediate
   state and immutables chain through a later state (e.g. function calls
   where pop_function restores scopes but body modifies immutables) *)
Theorem preserves_tv_scope_restore[local]:
  preserves_tv cx s1 s2 ∧ preserves_tv cx s2 s3 ∧
  (s4.scopes = s2.scopes) ∧ (s4.immutables = s3.immutables) ⇒
  preserves_tv cx s1 s4
Proof
  rw[preserves_tv_def] >> metis_tac[]
QED

(* Helper: preserves_tv composes for function calls where cleanup restores
   scopes to pre-call state but immutables chain through the body.
   st_mid = post-eval_exprs, st_push = post-push_function, st_body = post-body *)
Theorem preserves_tv_function_call[local]:
  preserves_tv cx st st_mid /\
  preserves_tv cx' st_push st_body /\
  (cx.txn = cx'.txn) /\
  (st_push.immutables = st_mid.immutables) /\
  (st'.scopes = st_mid.scopes) /\
  (st'.immutables = st_body.immutables) ==>
  preserves_tv cx st st'
Proof
  rw[preserves_tv_def] >> metis_tac[preserves_tv_txn_eq]
QED

(* finally preserves immutables through cleanup to the state after f *)
Theorem finally_immutables[local]:
  !f g st res st'.
    finally f g st = (res, st') /\
    (!st0 res0 st0'. g st0 = (res0, st0') ==> st0'.immutables = st0.immutables) ==>
    st'.immutables = (SND (f st)).immutables
Proof
  rpt strip_tac >>
  gvs[finally_def] >>
  Cases_on `f st` >> Cases_on `q` >>
  gvs[ignore_bind_apply] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def] >>
  res_tac >> gvs[]
QED

(* Combined: finally with pop_function+g gives scopes=prev AND immutables from f,
   when g preserves both scopes and immutables *)
Theorem finally_pop_function_then_facts[local]:
  !f g prev st res st'.
    finally f (do pop_function prev; g od) st = (res, st') /\
    (!st0 res0 st0'. g st0 = (res0, st0') ==>
       st0'.scopes = st0.scopes /\ st0'.immutables = st0.immutables) ==>
    st'.scopes = prev /\ st'.immutables = (SND (f st)).immutables
Proof
  rpt strip_tac >> gvs[finally_def] >>
  Cases_on `f st` >> Cases_on `q` >>
  gvs[ignore_bind_apply, bind_def, ignore_bind_def,
      pop_function_def, set_scopes_def, return_def, raise_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def] >>
  res_tac >> fs[]
QED

val PLACE_TV_TAC =
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def] >> rpt strip_tac >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac read_result_state >> imp_res_tac get_place_state >>
  imp_res_tac extend_place_state >> imp_res_tac lookup_global_state >>
  imp_res_tac read_result_state >>
  imp_res_tac lift_sum_state >> imp_res_tac read_result_state >>
  imp_res_tac write_place_preserves_tv >> imp_res_tac type_check_state >>
  gvs[get_scopes_def, return_def] >>
  rpt (first_x_assum drule_all >> strip_tac >> gvs[]) >>
  metis_tac[preserves_tv_trans];

Theorem eval_preserves_tv_extended:
  (∀cx s st res st'. eval_stmt cx s st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx ss st res st'. eval_stmts cx ss st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx it st res st'. eval_iterator cx it st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒
     preserves_tv cx st st') ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒
     preserves_tv cx st st') /\
  (!cx t st res st'. eval_base_place cx t st = (res,st') ==> preserves_tv cx st st') /\
  (!cx t st res st'. eval_target_place cx t st = (res,st') ==> preserves_tv cx st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==> preserves_tv cx st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> preserves_tv cx st st')
Proof
  ho_match_mp_tac evaluate_ind >>
  conj_tac >- rw[evaluate_def, return_def] >>
  conj_tac >- rw[evaluate_def, raise_def] >>
  conj_tac >- rw[evaluate_def, raise_def] >>
  conj_tac >- rw[evaluate_def, raise_def] >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, AllCaseEqs(), raise_def] >>
    imp_res_tac read_result_state >> gvs[] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, AllCaseEqs(), raise_def] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac read_result_state >> gvs[] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac read_result_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac read_result_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac read_result_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac read_result_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def] >>
    gvs[bind_apply, switch_BoolV_def, COND_RATOR, return_def,
        raise_def, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac read_result_state >> gvs[] >>
    first_x_assum drule_all >>
    first_x_assum drule_all >> rw[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rw[evaluate_def, bind_apply, AllCaseEqs(), push_log_def, return_def] >>
    imp_res_tac lift_option_state >> gvs[] >>
    first_x_assum drule >>
    gvs[preserves_tv_def] ) >>
  conj_tac >- (
    rw[evaluate_def, bind_apply, AllCaseEqs()] >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac read_result_state >>
    imp_res_tac new_variable_immutables >>
    imp_res_tac new_variable_preserves_tv >>
    gvs[] >> first_x_assum drule_all >> gvs[] >>
    metis_tac[preserves_tv_trans] ) >>
  conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
    imp_res_tac read_result_state >>
    imp_res_tac append_place_preserves_tv >> gvs[] >>
    rpt (first_x_assum drule_all >> strip_tac >> gvs[]) >>
    metis_tac[preserves_tv_trans]) >>
  conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
    rpt strip_tac >>
    imp_res_tac read_result_state >>
    imp_res_tac write_place_preserves_tv >> gvs[] >>
    rpt (first_x_assum drule_all >> strip_tac >> gvs[]) >>
    metis_tac[preserves_tv_trans]) >>
  conj_tac >- PLACE_TV_TAC >>
  conj_tac >- PLACE_TV_TAC >>
  conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
         return_def, AllCaseEqs()] >> rpt strip_tac >>
    gvs[] >>
    `push_scope s'' = (INL (),s'' with scopes updated_by CONS FEMPTY)` by
      simp[push_scope_def, return_def] >>
    rpt (first_x_assum drule_all >> strip_tac) >>
    `!s r s'. switch_BoolV cx tv (eval_stmts cx ss) (eval_stmts cx ss') s = (r,s') ==>
       preserves_tv cx s s'` by
      (metis_tac[switch_BoolV_preserves_tv]) >>
    drule_all finally_pop_preserves_tv >> strip_tac >>
    metis_tac[preserves_tv_trans]) >>
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
    imp_res_tac check_state >>
    imp_res_tac type_check_state >>
    gvs[] >>
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
    imp_res_tac read_result_state >> gvs[return_def] >>
    first_x_assum drule >> rw[]) >>
  (* Range iterator *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(), return_def] >>
    imp_res_tac read_result_state >>
    imp_res_tac lift_sum_state >> gvs[] >>
    TRY (first_x_assum drule >> rw[] >> NO_TAC) >>
    first_x_assum drule_all >> strip_tac >>
    first_x_assum drule_all >> strip_tac >>
    irule preserves_tv_trans >> first_assum (irule_at Any) >> simp[]) >>
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
         lift_option_type_def, option_CASE_rator, ignore_bind_def] >>
    imp_res_tac type_check_state >> gvs[bind_def, return_def]) >>
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
    imp_res_tac read_result_state >>
    imp_res_tac conditional_result_state >> gvs[] >>
    rpt (first_x_assum drule_all >> strip_tac) >>
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
    imp_res_tac select_result_state >>
    imp_res_tac lift_sum_state >>
    imp_res_tac read_result_state >>
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
    imp_res_tac select_result_state >> gvs[] >>
    first_x_assum drule >> rw[]) >>
  (* Builtin *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply,
        AllCaseEqs(), COND_RATOR, return_def] >>
    imp_res_tac type_check_state >>
    imp_res_tac lift_sum_state >>
    imp_res_tac read_result_state >>
    imp_res_tac result_array_length_state >> gvs[] >>
    rpt(first_x_assum drule >> rw[]) >>
    gvs[get_accounts_def, return_def]) >>
  (* Pop *)
  conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `eval_expr _ (Pop _ _) _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
    imp_res_tac pop_place_preserves_tv >>
    rpt (first_x_assum drule_all >> strip_tac) >>
    metis_tac[preserves_tv_trans]) >>
  (* TypeBuiltin *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(),
        ignore_bind_apply, return_def] >>
    imp_res_tac type_check_state >>
    imp_res_tac lift_sum_state >> gvs[] >>
    first_x_assum drule_all >> rw[]) >>
  (* Send and ExtCall: operands, then eval_send / eval_ext_call, which
     preserve scopes and immutables. *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
        return_def] >>
    imp_res_tac type_check_state >>
    imp_res_tac eval_send_preserves_non_accounts >> gvs[] >>
    qpat_x_assum `!s'' t. type_check _ _ _ = _ ==> _` drule >>
    disch_then drule >> rw[] >> gvs[preserves_tv_def]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, AllCaseEqs(), return_def] >>
    imp_res_tac eval_ext_call_preserves_non_accounts >> gvs[] >>
    first_x_assum drule >> rw[] >> gvs[preserves_tv_def]) >>
  (* IntCall *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    pop_assum mp_tac >>
    simp_tac std_ss [evaluate_def, bind_apply, ignore_bind_apply] >>
    (* check recursion *)
    BasicProvers.TOP_CASE_TAC >>
    imp_res_tac type_check_state >>
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
    (* LET bindings + consume 3 IHs *)
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
    gvs[get_scopes_def, return_def, bind_apply, ignore_bind_apply,
        finally_def, set_scopes_def, return_def] >>
    Cases_on `eval_exprs cxd needed_dflts (r' with scopes := [FEMPTY])` >>
    Cases_on `q` >> gvs[return_def, raise_def] >>
    first_x_assum drule_all >> strip_tac >>
    (* Derive preserves_tv cx from preserves_tv cxd via txn_eq *)
    drule preserves_tv_restore_scopes >>
    disch_then assume_tac >>
    qpat_x_assum `preserves_tv cxd r' (r'' with scopes := r'.scopes)` mp_tac >>
    simp[Abbr`cxd`, preserves_tv_stk_update] >> strip_tac >>
    suspend "IntCall_ptv") >>
  (* Shared approach: IH gives preserves_tv for eval_exprs.
     Remaining ops preserve scopes+immutables, so preserves_tv_eq +
     preserves_tv_trans finishes. *)
  (* Both raw_call input forms preserve scopes and immutables after operands. *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(), return_def] >>
    imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
    imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >>
    first_x_assum drule >> rw[] >> gvs[preserves_tv_def]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(), return_def] >>
    imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
    imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >>
    first_x_assum drule >> rw[] >> gvs[preserves_tv_def]) >>
  (* RawLog *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
         return_def] >>
    imp_res_tac check_state >>
    imp_res_tac type_check_state >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac push_log_scopes >>
    imp_res_tac push_log_immutables >> gvs[] >>
    first_x_assum drule >> rw[] >>
    gvs[preserves_tv_def]) >>
  (* RawRevert *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
         return_def, raise_def] >>
    imp_res_tac type_check_state >>
    imp_res_tac check_state >> gvs[] >>
    first_x_assum drule >> rw[] >>
    gvs[preserves_tv_def]) >>
  (* SelfDestructTarget *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
         return_def] >>
    imp_res_tac check_state >>
    imp_res_tac type_check_state >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac get_accounts_state >>
    imp_res_tac transfer_value_scopes >>
    imp_res_tac transfer_value_immutables >> gvs[] >>
    first_x_assum drule >> rw[] >>
    gvs[preserves_tv_def]) >>
  (* CreateTarget *)
  conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    Cases_on `kind` >> gvs[] >>
    gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
    imp_res_tac check_create_blueprint_result_state >> gvs[] >>
    res_tac >>
    imp_res_tac eval_create_preserves_scopes_immutables >>
    metis_tac[preserves_tv_trans, preserves_tv_eq]) >>
  (* eval_exprs [] *)
  conj_tac >- rw[evaluate_def, return_def] >>
  (* eval_exprs e::es *)
  conj_tac >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
   gvs[Once evaluate_def, bind_apply, AllCaseEqs()] >>
   imp_res_tac read_result_state >> gvs[] >>
   TRY (first_x_assum drule >> rw[] >> NO_TAC) >>
   first_x_assum drule_all >> strip_tac >>
   first_x_assum drule_all >> strip_tac >>
   irule preserves_tv_trans >> first_assum (irule_at Any) >>
   gvs[return_def]) >>
  rpt conj_tac >> rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac read_result_state >> imp_res_tac get_place_state >>
  imp_res_tac extend_place_state >> imp_res_tac lookup_global_state >>
  imp_res_tac read_result_state >>
  imp_res_tac lift_sum_state >> imp_res_tac read_result_state >>
  imp_res_tac write_place_preserves_tv >> imp_res_tac type_check_state >>
  gvs[get_scopes_def, return_def] >>
  rpt (first_x_assum drule_all >> strip_tac >> gvs[]) >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  TRY (metis_tac[preserves_tv_trans] >> NO_TAC) >>
  Cases_on `v` >> gvs[raise_def] >> Cases_on `a` >>
  gvs[raise_def] >> metis_tac[]
QED

Theorem try_handle_function_state[local]:
  !f s. SND (try f handle_function s) = SND (f s)
Proof
  rw[try_def, bind_def, return_def] >>
  Cases_on `f s` >> Cases_on `q` >>
  rw[handle_function_def, return_def, raise_def] >>
  Cases_on `y` >> gvs[return_def, raise_def, handle_function_def]
QED

Theorem bind_return_snd[local]:
  !f (v:'a) s. SND (do x <- f; return v od s) = SND (f s)
Proof
  rw[bind_def, return_def] >> Cases_on `f s` >> Cases_on `q` >> rw[]
QED

Theorem ignore_bind_return_snd[local]:
  !f (v:'a) s. SND (do f; return v od s) = SND (f s)
Proof
  rw[ignore_bind_def, bind_def, return_def] >>
  Cases_on `f s` >> Cases_on `q` >> rw[]
QED

Theorem intcall_body_ih_pack[local]:
  (!s6 vs t4 s7 s8 dflt_vs t6 s9 env t7 s10 rtv t8 s11 t9 st res st'.
     ((eval_exprs cx es s6 = (INL vs,t4) /\
       (case eval_exprs cxf needed_dflts (s8 with scopes := [FEMPTY]) of
          (INL x,s'') => (INL x,s'' with scopes := s7.scopes)
        | (INR e,s'') => (INR e,s'' with scopes := s7.scopes)) = (INL dflt_vs,t6) /\
       lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
         "IntCall bind_arguments" s9 = (INL env,t7) /\
       lift_option_type (evaluate_type (get_tenv cx) ret)
         "IntCall eval ret" s10 = (INL rtv,t8) /\
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ()) s11 = (INL (),t9)) /\
      eval_stmts cxf body st = (res,st')) ==>
     preserves_tv cxf st st') ==>
  eval_exprs cx es r = (INL vs0,r1) ==>
  eval_exprs cxf needed_dflts (r1 with scopes := [FEMPTY]) = (INL dflt_vs0,r2) ==>
  lift_option_type (bind_arguments (get_tenv cx) args (vs0 ++ dflt_vs0))
    "IntCall bind_arguments" (r2 with scopes := r1.scopes) =
    (INL env0,r2 with scopes := r1.scopes) ==>
  lift_option_type (evaluate_type (get_tenv cx) ret)
    "IntCall eval ret" (r2 with scopes := r1.scopes) =
    (INL rtv0,r2 with scopes := r1.scopes) ==>
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) (r2 with scopes := r1.scopes) = (INL (),r_lock) ==>
  !st res st'. eval_stmts cxf body st = (res,st') ==> preserves_tv cxf st st'
Proof
  rpt strip_tac >>
  qpat_assum `!s6 vs t4 s7 s8 dflt_vs t6 s9 env t7 s10 rtv t8 s11 t9 st0 res0 st1.
    _ ==> preserves_tv cxf st0 st1`
    (qspecl_then [`r`, `vs0`, `r1`, `r1`, `r1`, `dflt_vs0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `env0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `rtv0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `r_lock`,
      `st`, `res`, `st'`] mp_tac) >>
  simp[]
QED

Theorem intcall_body_ih_resume_pack[local]:
  (!s6 vs t4 s7 s8 dflt_vs t6 s9 env t7 s10 rtv t8 s11 t9 st res st'.
     ((eval_exprs cx es s6 = (INL vs,t4) /\
       (case eval_exprs (cx with stk updated_by CONS (src_id_opt,fn)) needed_dflts
              (s8 with scopes := [FEMPTY]) of
          (INL x,s'') => (INL x,s'' with scopes := s7.scopes)
        | (INR e,s'') => (INR e,s'' with scopes := s7.scopes)) = (INL dflt_vs,t6) /\
       lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
         "IntCall bind_arguments" s9 = (INL env,t7) /\
       lift_option_type (evaluate_type (get_tenv cx) ret)
         "IntCall eval ret" s10 = (INL rtv,t8) /\
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ()) s11 = (INL (),t9)) /\
      eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) body' st = (res,st')) ==>
     preserves_tv (cx with stk updated_by CONS (src_id_opt,fn)) st st') ==>
  eval_exprs cx es r = (INL vs0,r1) ==>
  eval_exprs (cx with stk updated_by CONS (src_id_opt,fn)) needed_dflts
    (r1 with scopes := [FEMPTY]) = (INL dflt_vs0,r2) ==>
  lift_option_type (bind_arguments (get_tenv cx) args (vs0 ++ dflt_vs0))
    "IntCall bind_arguments" (r2 with scopes := r1.scopes) =
    (INL env0,r2 with scopes := r1.scopes) ==>
  lift_option_type (evaluate_type (get_tenv cx) ret)
    "IntCall eval ret" (r2 with scopes := r1.scopes) =
    (INL rtv0,r2 with scopes := r1.scopes) ==>
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) (r2 with scopes := r1.scopes) = (INL (),r_lock) ==>
  !st res st'.
    eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) body' st = (res,st') ==>
    preserves_tv (cx with stk updated_by CONS (src_id_opt,fn)) st st'
Proof
  rpt strip_tac >>
  qpat_assum `!s6 vs t4 s7 s8 dflt_vs t6 s9 env t7 s10 rtv t8 s11 t9 st0 res0 st1.
    _ ==> preserves_tv (cx with stk updated_by CONS (src_id_opt,fn)) st0 st1`
    (qspecl_then [`r`, `vs0`, `r1`, `r1`, `r1`, `dflt_vs0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `env0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `rtv0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `r_lock`,
      `st`, `res`, `st'`] mp_tac) >>
  simp[]
QED

Theorem intcall_body_ih_resume_point[local]:
  (!s6 vs t4 s7 s8 dflt_vs t6 s9 env t7 s10 rtv t8 s11 t9 st res st'.
     ((eval_exprs cx es s6 = (INL vs,t4) /\
       (case eval_exprs (cx with stk updated_by CONS (src_id_opt,fn)) needed_dflts
              (s8 with scopes := [FEMPTY]) of
          (INL x,s'') => (INL x,s'' with scopes := s7.scopes)
        | (INR e,s'') => (INR e,s'' with scopes := s7.scopes)) = (INL dflt_vs,t6) /\
       lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
         "IntCall bind_arguments" s9 = (INL env,t7) /\
       lift_option_type (evaluate_type (get_tenv cx) ret)
         "IntCall eval ret" s10 = (INL rtv,t8) /\
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ()) s11 = (INL (),t9)) /\
      eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) body' st = (res,st')) ==>
     preserves_tv (cx with stk updated_by CONS (src_id_opt,fn)) st st') ==>
  eval_exprs cx es r = (INL vs0,r1) ==>
  eval_exprs (cx with stk updated_by CONS (src_id_opt,fn)) needed_dflts
    (r1 with scopes := [FEMPTY]) = (INL dflt_vs0,r2) ==>
  lift_option_type (bind_arguments (get_tenv cx) args (vs0 ++ dflt_vs0))
    "IntCall bind_arguments" (r2 with scopes := r1.scopes) =
    (INL env0,r2 with scopes := r1.scopes) ==>
  lift_option_type (evaluate_type (get_tenv cx) ret)
    "IntCall eval ret" (r2 with scopes := r1.scopes) =
    (INL rtv0,r2 with scopes := r1.scopes) ==>
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) (r2 with scopes := r1.scopes) = (INL (),r_lock) ==>
  eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) body' st = (res,st') ==>
  preserves_tv (cx with stk updated_by CONS (src_id_opt,fn)) st st'
Proof
  rpt strip_tac >>
  qpat_assum `!s6 vs t4 s7 s8 dflt_vs t6 s9 env t7 s10 rtv t8 s11 t9 st0 res0 st1.
    _ ==> preserves_tv (cx with stk updated_by CONS (src_id_opt,fn)) st0 st1`
    (qspecl_then [`r`, `vs0`, `r1`, `r1`, `r1`, `dflt_vs0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `env0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `rtv0`,
      `r2 with scopes := r1.scopes`, `r2 with scopes := r1.scopes`, `r_lock`,
      `st`, `res`, `st'`] mp_tac) >>
  simp[]
QED

(* Standalone lemma: preserves_tv through the IntCall finally+safe_cast chain.
   Abstracts away variable names so we can prove it with hol_state_at. *)
Theorem intcall_ptv_chain[local]:
  preserves_tv cx r r_mid /\
  (r_lock.scopes = r_mid.scopes) /\
  (r_lock.immutables = r_mid.immutables) /\
  (!st res st'. eval_stmts cxf body st = (res, st') ==>
     preserves_tv cxf st st') /\
  (cx.txn = cxf.txn) /\
  (!st0 (res0:unit + exception) st0'. cleanup st0 = (res0, st0') ==>
     st0'.scopes = st0.scopes /\ st0'.immutables = st0.immutables) /\
  (case
     finally
       (try (do eval_stmts cxf body; return NoneV od) handle_function)
       (do pop_function r_mid.scopes; cleanup od)
       (r_lock with scopes := [env])
   of
     (INL rv, s'') =>
       (case lift_option_type (safe_cast rtv rv) msg s'' of
          (INL crv, s'') => (INL (Value crv), s'')
        | (INR e, s'') => (INR e, s''))
   | (INR e, s'') => (INR e, s'')) = (res, st') ==>
  preserves_tv cx r st'
Proof
  strip_tac >>
  (* Name the finally result *)
  `?fres fst. finally
     (try (do eval_stmts cxf body; return NoneV od) handle_function)
     (do pop_function r_mid.scopes; cleanup od)
     (r_lock with scopes := [env]) = (fres, fst)` by
    metis_tac[pairTheory.PAIR] >>
  (* Get facts from finally_pop_function_then_facts *)
  `fst.scopes = r_mid.scopes /\
   fst.immutables = (SND (try (do eval_stmts cxf body; return NoneV od)
     handle_function (r_lock with scopes := [env]))).immutables` by (
    qpat_x_assum `finally _ _ _ = _`
      (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
        finally_pop_function_then_facts)) >>
    impl_tac >- simp[] >>
    simp[]) >>
  (* Simplify immutables through try+handle_function+bind *)
  `(SND (try (do eval_stmts cxf body; return NoneV od) handle_function
     (r_lock with scopes := [env]))).immutables =
   (SND (eval_stmts cxf body (r_lock with scopes := [env]))).immutables` by
    simp[try_handle_function_state, ignore_bind_return_snd] >>
  (* Get preserves_tv cxf for the body via IH *)
  `preserves_tv cxf (r_lock with scopes := [env])
     (SND (eval_stmts cxf body (r_lock with scopes := [env])))` by (
    first_x_assum irule >>
    Cases_on `eval_stmts cxf body (r_lock with scopes := [env])` >> simp[]) >>
  (* Reduce st' to fst: case split on the outer case expression *)
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[] >>
  Cases_on `fres` >> simp[] >| [
    (* INL: safe_cast chain *)
    Cases_on `lift_option_type (safe_cast rtv x) msg fst` >>
    Cases_on `q` >> simp[] >>
    strip_tac >> gvs[] >>
    imp_res_tac lift_option_type_state >> gvs[],
    (* INR: error, st' = fst *)
    strip_tac >> gvs[]
  ] >>
  (* In all cases st' = fst. Apply preserves_tv_function_call *)
  irule preserves_tv_function_call >>
  first_assum (irule_at Any) >>
  qexists_tac `r_mid` >>
  simp[]
QED

Resume eval_preserves_tv_extended[IntCall_ptv]:
  markerLib.RESUME_TAC >- (
    strip_tac >> gvs[] >>
    irule preserves_tv_trans >> first_assum (irule_at Any) >> simp[]) >>
  strip_tac >>
  (* Unfold the do...od assumption *)
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp_tac std_ss [bind_apply, get_scopes_def, return_def] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[] >>
    irule preserves_tv_trans >> first_assum (irule_at Any) >> simp[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[] >>
    irule preserves_tv_trans >> first_assum (irule_at Any) >> simp[]) >>
  simp_tac std_ss [ignore_bind_apply, bind_apply] >>
  (* Reentrancy lock -- split pair, then INL/INR *)
  BasicProvers.TOP_CASE_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    (* INR from lock -- lock failed, state preserved *)
    strip_tac >> gvs[] >>
    imp_res_tac lock_acquire_cond_scopes_immutables >>
    fs[preserves_tv_def]) >>
  (* INL from lock -- lock succeeded *)
  strip_tac >>
  imp_res_tac lock_acquire_cond_scopes_immutables >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp_tac std_ss [bind_apply, push_function_def, return_def] >>
  simp_tac (std_ss ++ sumSimps.SUM_ss ++ pairSimps.PAIR_ss)
    [bind_apply, push_function_def, return_def] >>
  strip_tac >>
  gvs[push_function_def, return_def] >>
  (* Cut the body IH before entering the large tail-chain residual goal. *)
  `!st res st'.
     eval_stmts (cx with stk updated_by CONS (src_id_opt, fn)) body' st = (res,st') ==>
     preserves_tv (cx with stk updated_by CONS (src_id_opt, fn)) st st'` by (
    rpt strip_tac >>
    drule_all intcall_body_ih_resume_point >>
    simp[]
  ) >>
  irule intcall_ptv_chain >>
  qexistsl_tac [`body'`,
    `if nr /\ mut <> View /\ mut <> Pure then
       case cx.nonreentrant_slot of NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()`,
    `cx with stk updated_by CONS (src_id_opt, fn)`,
    `x'3'`, `"IntCall cast ret"`, `r'5'`, `r'' with scopes := r'.scopes`, `res`, `x'5'`] >>
  simp[] >> conj_tac >- (
    rpt gen_tac >>
    IF_CASES_TAC >> simp[return_def] >>
    Cases_on `cx.nonreentrant_slot` >> simp[return_def] >>
    strip_tac >>
    imp_res_tac release_nonreentrant_lock_scopes >>
    imp_res_tac release_nonreentrant_lock_immutables >> simp[]
  ) >>
  conj_tac >- (
    qpat_x_assum `(case _ of (INL rv,s'') => _ | (INR e,s'') => _) = (res,st')` mp_tac >>
    simp[finally_def, ignore_bind_def, bind_def, return_def, raise_def]
  ) >>
  irule preserves_tv_trans >> qexists_tac `r'` >> simp[]
QED

Finalise eval_preserves_tv_extended

Theorem eval_preserves_tv:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> preserves_tv cx st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> preserves_tv cx st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==> preserves_tv cx st st') /\
  (!cx ty nm body vs st res st'. eval_for cx ty nm body vs st = (res,st') ==> preserves_tv cx st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> preserves_tv cx st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> preserves_tv cx st st') /\
  (!cx t st res st'. eval_base_place cx t st = (res,st') ==> preserves_tv cx st st') /\
  (!cx t st res st'. eval_target_place cx t st = (res,st') ==> preserves_tv cx st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==> preserves_tv cx st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> preserves_tv cx st st')
Proof
  ACCEPT_TAC eval_preserves_tv_extended
QED

Theorem eval_stmt_preserves_tv:
  eval_stmt cx s st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 1 eval_preserves_tv]
QED

Theorem eval_stmts_preserves_tv:
  eval_stmts cx ss st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 2 eval_preserves_tv]
QED

Theorem eval_iterator_preserves_tv:
  eval_iterator cx it st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 3 eval_preserves_tv]
QED

Theorem eval_for_preserves_tv:
  eval_for cx ty nm body vs st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 4 eval_preserves_tv]
QED

Theorem eval_expr_preserves_tv:
  eval_expr cx e st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 5 eval_preserves_tv]
QED

Theorem eval_exprs_preserves_tv:
  eval_exprs cx es st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 6 eval_preserves_tv]
QED

Theorem eval_base_place_preserves_tv:
  eval_base_place cx t st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 7 eval_preserves_tv]
QED

Theorem eval_target_place_preserves_tv:
  eval_target_place cx t st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 8 eval_preserves_tv]
QED

Theorem assign_tuple_targets_preserves_tv:
  assign_tuple_targets cx g v st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 9 eval_preserves_tv]
QED

Theorem assign_tuple_target_list_preserves_tv:
  assign_tuple_target_list cx gs vs st = (res,st') ==> preserves_tv cx st st'
Proof
  metis_tac[cj 10 eval_preserves_tv]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail ("vyperEvalPreservesScopes." ^ name ^ ": admitted dependency")
  end) (DB.thms "vyperEvalPreservesScopes");
