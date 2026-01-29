Theory vyperEvalStmtsPreservesScopes

Ancestors
  vyperInterpreter vyperLookup vyperEvalExprPreservesScopeDom vyperScopePreservationLemmas

(***)

(* ========================================================================
   Proof Sketch: eval_stmts_preserves_scopes

   Main theorem: eval_stmts preserves scope structure - HD can grow (⊆),
   while TL scopes remain exactly the same (MAP FDOM equality).

   Generated from proof plan. Helper lemmas are cheated.
   ======================================================================== *)

(* ------------------------------------------------------------------------
   Section 1: Core Helper Lemmas for Scope Operations

   These establish foundational facts about scope-modifying operations.
   ------------------------------------------------------------------------ *)

(* new_variable adds to HD scope, preserves TL.

   WHY THIS IS TRUE:
   new_variable_def does: set_scopes ((e |+ (n, v))::es) where e::es = st.scopes
   - HD st'.scopes = e |+ (n, v), so FDOM (HD st.scopes) = FDOM e ⊆ FDOM (e |+ (n,v))
   - TL st'.scopes = es = TL st.scopes, so MAP FDOM (TL st'.scopes) = MAP FDOM (TL st.scopes)

   Plan reference: Category 2 - AnnAssign case
   Used in: case_AnnAssign *)
Theorem new_variable_scope_property:
  ∀id v st res st'.
    new_variable id v st = (res, st') ∧ st.scopes ≠ [] ⇒
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    TL st'.scopes = TL st.scopes
Proof
  rpt strip_tac >> Cases_on `st.scopes` >> gvs[] >>
  gvs[new_variable_def, bind_def, get_scopes_def, return_def, check_def,
      assert_def, set_scopes_def, AllCaseEqs(), raise_def, ignore_bind_def] >>
  irule pred_setTheory.SUBSET_INSERT_RIGHT >> simp[]
QED

(* push_scope creates empty HD, preserves original as TL.

   WHY THIS IS TRUE:
   push_scope_def does: set_scopes (FEMPTY :: st.scopes)
   After push: HD = FEMPTY, TL = st.scopes

   Plan reference: Intermediate state for If/For cases
   Used in: case_If, case_For *)
Theorem push_scope_creates_empty_hd:
  ∀st res st'.
    push_scope st = (INL (), st') ⇒
    HD st'.scopes = FEMPTY ∧
    TL st'.scopes = st.scopes
Proof
  rw[push_scope_def, return_def] >> simp[]
QED

(* push_scope_with_var creates singleton HD, preserves original as TL.

   WHY THIS IS TRUE:
   push_scope_with_var_def does: set_scopes ((FEMPTY |+ (nm, v)) :: st.scopes)
   After push: HD = FEMPTY |+ (nm, v), TL = st.scopes

   Plan reference: eval_for uses this
   Used in: case_eval_for_cons *)
Theorem push_scope_with_var_creates_singleton_hd:
  ∀nm v st res st'.
    push_scope_with_var nm v st = (INL (), st') ⇒
    HD st'.scopes = FEMPTY |+ (nm, v) ∧
    TL st'.scopes = st.scopes
Proof
  rw[push_scope_with_var_def, return_def] >> simp[]
QED

(* finally with pop_scope: if body preserves TL, final state has MAP FDOM = MAP FDOM (TL original).

   WHY THIS IS TRUE:
   finally runs body, then unconditionally runs pop_scope.
   pop_scope sets scopes to TL body_st'.scopes.
   If body preserved TL (MAP FDOM (TL body_st'.scopes) = MAP FDOM (TL st.scopes)),
   then final MAP FDOM st'.scopes = MAP FDOM (TL st.scopes).

   Plan reference: Key for If and For - pop_scope restores scope structure
   Used in: case_If, case_For, case_eval_for_cons *)
Theorem finally_pop_scope_preserves_tl_dom:
  ∀body st res st'.
    finally body pop_scope st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM (TL st.scopes)
Proof
  rpt strip_tac >>
  gvs[finally_def, AllCaseEqs()] >>
  gvs[pop_scope_def, AllCaseEqs(), bind_def, ignore_bind_def, return_def, raise_def] >>
  first_x_assum drule >> simp[]
QED

(* Combined: push_scope then finally body pop_scope restores MAP FDOM.

   WHY THIS IS TRUE:
   1. push_scope: HD' = FEMPTY, TL' = st.scopes
   2. body runs on pushed state. By IH: MAP FDOM (TL body_st'.scopes) = MAP FDOM (TL pushed_st.scopes) = MAP FDOM st.scopes
   3. pop_scope: st'.scopes = TL body_st'.scopes
   4. Therefore: MAP FDOM st'.scopes = MAP FDOM st.scopes

   Plan reference: Core pattern for If statement
   Used in: case_If *)
Theorem push_scope_finally_pop_preserves_dom:
  ∀body st res st'.
    do push_scope; finally body pop_scope od st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       FDOM (HD st1.scopes) ⊆ FDOM (HD st1'.scopes) ∧
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM st.scopes
Proof
  rpt strip_tac >>
  gvs[push_scope_def, bind_def, ignore_bind_def, return_def] >>
  gvs[finally_def, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[pop_scope_def, AllCaseEqs(), bind_def, ignore_bind_def, return_def, raise_def]
QED

(* ------------------------------------------------------------------------
   Section 2: Preservation Property Definition

   We define the property that will be proven by mutual induction.
   ------------------------------------------------------------------------ *)

(* The core property for statement/stmts evaluation:
   - HD scope can grow (subset)
   - TL scopes preserved exactly (MAP FDOM equality) *)
Definition preserves_scopes_dom_def:
  preserves_scopes_dom st st' ⇔
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)
End

(* Expressions, targets, iterators preserve scopes exactly (not just ⊆).
   This is already proven in vyperEvalExprPreservesScopeDomTheory. *)

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

(* Return (SOME e): eval_expr preserves MAP FDOM, get_Value and raise preserve scopes.

   WHY THIS IS TRUE:
   eval_expr preserves MAP FDOM st.scopes exactly (eval_expr_preserves_scopes_dom).
   get_Value and raise preserve scopes exactly (return_scopes, raise_scopes).
   Chain: MAP FDOM unchanged through all operations.

   Plan reference: Category 1
   Used in: main induction *)
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
  imp_res_tac get_Value_scopes >> imp_res_tac raise_scopes >> gvs[]
QED

(* Similar proofs for Raise, Assert, Log, Assign, AugAssign, Append, Expr *)

Theorem case_Raise_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Raise e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >>
  imp_res_tac raise_scopes >> gvs[]
QED

Theorem case_Assert_dom[local]:
  ∀cx e se.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx se st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Assert e se) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt IF_CASES_TAC >> simp[return_def, raise_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> gvs[]) >>
  rpt (qpat_x_assum `∀st res st'. eval_expr cx e st = _ ⇒ _` (drule_then assume_tac) >>
       qpat_x_assum `∀st res st'. eval_expr cx se st = _ ⇒ _` (drule_then assume_tac) >> gvs[])
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
  imp_res_tac assign_target_preserves_scopes_dom >> gvs[] >>
  Cases_on `x` >> gvs[bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >>
  imp_res_tac assign_target_preserves_scopes_dom >> gvs[] >>
  rpt (first_x_assum (drule_then assume_tac) >> gvs[])
QED

Theorem case_Assign_dom[local]:
  ∀cx g e.
    (∀st res st'. eval_target cx g st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Assign g e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >> irule map_fdom_eq_preserves_dom >>
  gvs[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >>
  imp_res_tac assign_target_preserves_scopes_dom >> gvs[] >>
  rpt (first_x_assum (drule_then assume_tac) >> gvs[])
QED

Theorem case_AugAssign_dom[local]:
  ∀cx bt bop e.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (AugAssign bt bop e) st = (res, st') ⇒ preserves_scopes_dom st st'
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
  imp_res_tac get_Value_scopes >> imp_res_tac return_scopes >> gvs[]
QED

(* === Category 2: AnnAssign adds to HD, preserves TL === *)

(* AnnAssign: eval_expr preserves exactly, new_variable adds to HD only.

   WHY THIS IS TRUE:
   1. eval_expr cx e st = (tv, st1) - preserves MAP FDOM exactly
   2. get_Value tv st1 = (v, st2) - preserves scopes exactly
   3. new_variable id v st2 = (res, st') - adds id to HD, TL unchanged

   Combined:
   - FDOM (HD st.scopes) = FDOM (HD st1.scopes) = FDOM (HD st2.scopes) ⊆ FDOM (HD st'.scopes)
   - MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)

   Plan reference: Category 2
   Used in: main induction *)
Theorem case_AnnAssign_dom[local]:
  ∀cx id typ e st res st'.
    eval_stmt cx (AnnAssign id typ e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >~
  (* Main case with new_variable *)
  [`new_variable _ _ _ = _`]
  >- (
    imp_res_tac eval_expr_preserves_scopes_dom >>
    imp_res_tac get_Value_scopes >> gvs[] >>
    Cases_on `s''.scopes` >> gvs[] >-
    (* Empty scopes case - new_variable raises error *)
    gvs[new_variable_def, bind_def, get_scopes_def, return_def, check_def,
        assert_def, lookup_scopes_def, ignore_bind_def, raise_def] >>
    (* Non-empty scopes case - apply new_variable_scope_property *)
    `s'³'.scopes ≠ []` by simp[] >>
    drule_all new_variable_scope_property >> strip_tac >> gvs[] >>
    Cases_on `st.scopes` >> gvs[]
  ) >~
  (* get_Value error case *)
  [`get_Value _ _ = (INR _, _)`]
  >- (
    imp_res_tac get_Value_scopes >> gvs[] >>
    imp_res_tac eval_expr_preserves_scopes_dom >>
    Cases_on `st.scopes` >> Cases_on `s''.scopes` >> gvs[]
  ) >>
  (* eval_expr error case *)
  imp_res_tac eval_expr_preserves_scopes_dom >>
  Cases_on `st.scopes` >> Cases_on `s''.scopes` >> gvs[]
QED

(* === Category 3: If statement (push_scope, body, pop_scope via finally) === *)

(* If: push_scope, body under finally with pop_scope.

   WHY THIS IS TRUE:
   1. eval_expr cx e st = (tv, st1) - preserves MAP FDOM exactly
   2. push_scope st1 = ((), st2) - creates HD = FEMPTY, TL = st1.scopes
   3. Body (switch_BoolV with eval_stmts) runs on st2
      By IH: FDOM (HD st2.scopes) ⊆ FDOM (HD body_st'.scopes) ∧
             MAP FDOM (TL st2.scopes) = MAP FDOM (TL body_st'.scopes)
      Note: TL st2.scopes = st1.scopes, so MAP FDOM st1.scopes = MAP FDOM (TL body_st'.scopes)
   4. finally with pop_scope: st'.scopes = TL body_st'.scopes
   5. Final: MAP FDOM st'.scopes = MAP FDOM (TL body_st'.scopes) = MAP FDOM st1.scopes = MAP FDOM st.scopes

   Plan reference: Category 3
   Used in: main induction

   NOTE: The IH from evaluate_ind is conditional on eval_expr succeeding and push_scope succeeding.
   Since push_scope always succeeds (returns ()), we simplify to just the eval_expr condition. *)
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
  >- (first_x_assum drule >> simp[preserves_scopes_dom_def]) >>
  Cases_on `tv = Value (BoolV F)` >> gvs[raise_def] >>
  first_x_assum drule >> simp[preserves_scopes_dom_def]
QED

(* === Category 4: For statement === *)

(* For: eval_iterator, check, then eval_for.

   WHY THIS IS TRUE:
   1. eval_iterator preserves MAP FDOM exactly (uses eval_expr)
   2. check preserves exactly
   3. eval_for preserves by its own IH
   Combined: preserves_scopes_dom

   Plan reference: Category 4
   Used in: main induction

   NOTE: The IH from evaluate_ind is conditional on eval_iterator succeeding and check succeeding. *)
Theorem case_For_dom[local]:
  ∀cx id typ it n body.
    (* IH for eval_for: conditional on eval_iterator and check succeeding *)
    (∀s'' vs t s'³' x t'.
       eval_iterator cx it s'' = (INL vs, t) ∧
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'³' = (INL x, t') ⇒
       ∀st res st'. eval_for cx (string_to_num id) body vs st = (res, st') ⇒
         preserves_scopes_dom st st') ∧
    (* IH for iterator *)
    (∀st res st'. eval_iterator cx it st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* Case: eval_iterator failed *)
  TRY (irule map_fdom_eq_preserves_dom >> first_x_assum drule >> simp[] >> NO_TAC) >>
  (* Case: check failed *)
  TRY (imp_res_tac check_scopes >> gvs[] >>
       irule map_fdom_eq_preserves_dom >> first_x_assum drule >> gvs[] >> NO_TAC) >>
  (* Case: both succeeded, use IH *)
  imp_res_tac check_scopes >> gvs[] >>
  `preserves_scopes_dom s'³' st'` by
    (first_x_assum (qspecl_then [`st`, `vs`, `s''`, `s''`, `s'³'`] mp_tac) >>
     simp[] >> strip_tac >> first_x_assum drule >> simp[]) >>
  gvs[preserves_scopes_dom_def] >>
  Cases_on `st.scopes` >> Cases_on `s''.scopes` >> gvs[] >>
  TRY (`MAP FDOM [] = MAP FDOM (h::t)` by
         (qpat_x_assum `∀st res st'. eval_iterator _ _ _ = _ ⇒ _` drule >> gvs[]) >> gvs[]) >>
  TRY (`MAP FDOM (h::t) = MAP FDOM []` by
         (qpat_x_assum `∀st res st'. eval_iterator _ _ _ = _ ⇒ _` drule >> gvs[]) >> gvs[]) >>
  `FDOM h::MAP FDOM t = FDOM h'::MAP FDOM t'` by
    (qpat_x_assum `∀st res st'. eval_iterator _ _ _ = _ ⇒ _` drule >> gvs[]) >> gvs[]
QED

(* === Category 5: eval_stmts (sequencing) === *)

Theorem case_eval_stmts_nil_dom[local]:
  ∀cx st res st'.
    eval_stmts cx [] st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, return_def, preserves_scopes_dom_def]
QED

(* eval_stmts cons: chain IH on statement and rest.

   WHY THIS IS TRUE:
   1. eval_stmt cx s st = (res1, st1) - by IH: FDOM (HD st.scopes) ⊆ FDOM (HD st1.scopes),
                                               MAP FDOM (TL st.scopes) = MAP FDOM (TL st1.scopes)
   2. eval_stmts cx ss st1 = (res, st') - by IH: FDOM (HD st1.scopes) ⊆ FDOM (HD st'.scopes),
                                                  MAP FDOM (TL st1.scopes) = MAP FDOM (TL st'.scopes)
   Combined: ⊆ is transitive, so FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes)
             TL equality chains: MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)

   Plan reference: Category 5
   Used in: main induction *)
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
  first_x_assum (qspecl_then [`st`, `s''`] mp_tac) >> simp[] >>
  strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  irule pred_setTheory.SUBSET_TRANS >>
  qexists_tac `FDOM (HD s''.scopes)` >> simp[]
QED

(* === Category 6: eval_for (iteration) === *)

Theorem case_eval_for_nil_dom[local]:
  ∀cx nm body st res st'.
    eval_for cx nm body [] st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, return_def, preserves_scopes_dom_def]
QED

(* Helper: the try body (eval_stmts + handle_loop_exception) preserves TL scopes.

   WHY THIS IS TRUE:
   - try runs body: if INL, preserves by IH on eval_stmts
   - if INR: handle_loop_exception returns T/F (preserves) or re-raises (preserves)
   - All branches preserve TL scopes.

   NOTE: Takes conditional IH that matches evaluate_ind structure. *)
Theorem try_body_preserves_tl_dom[local]:
  ∀cx body nm v st0.
    (* IH for eval_stmts: conditional on push_scope_with_var succeeding *)
    (∀s'' x t. push_scope_with_var nm v s'' = (INL x, t) ⇒
       ∀st res st'. eval_stmts cx body st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st1 res1 st1'.
      push_scope_with_var nm v st0 = (INL (), st1) ⇒
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
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt IF_CASES_TAC >> simp[return_def, raise_def]
QED

(* eval_for cons: push_scope_with_var, body under finally with pop_scope, then recursive.

   WHY THIS IS TRUE:
   1. push_scope_with_var nm v st = ((), st1): HD st1 = FEMPTY |+ (nm,v), TL st1 = st.scopes
   2. finally (try ...) pop_scope st1 = (broke, st2):
      - Body (eval_stmts) preserves by IH: MAP FDOM (TL st1'.scopes) = MAP FDOM (TL st1.scopes) = MAP FDOM st.scopes
      - pop_scope: st2.scopes = TL body_st'.scopes
      - So MAP FDOM st2.scopes = MAP FDOM st.scopes
   3. If not broke, eval_for cx nm body vs st2 = (res, st'):
      By IH: FDOM (HD st2.scopes) ⊆ FDOM (HD st'.scopes), MAP FDOM (TL st2.scopes) = MAP FDOM (TL st'.scopes)
   4. Combined: st.scopes and st2.scopes have same MAP FDOM, so preserves_scopes_dom st st'

   Plan reference: Category 6
   Used in: main induction

   NOTE: Takes conditional IH that matches evaluate_ind structure. *)
Theorem case_eval_for_cons_dom[local]:
  ∀cx nm body v vs.
    (* IH for eval_for: conditional on push_scope_with_var succeeding and finally succeeding with broke=F *)
    (∀s'' x t s'³' broke t'.
       push_scope_with_var nm v s'' = (INL x, t) ∧
       finally (try (do eval_stmts cx body; return F od) handle_loop_exception) pop_scope s'³' = (INL broke, t') ∧
       ¬broke ⇒
       ∀st res st'. eval_for cx nm body vs st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (* IH for eval_stmts: conditional on push_scope_with_var succeeding *)
    (∀s'' x t. push_scope_with_var nm v s'' = (INL x, t) ⇒
       ∀st res st'. eval_stmts cx body st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_for cx nm body (v::vs) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, push_scope_with_var_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* Handle error case from finally: unfold and use try_body_preserves_tl_dom *)
  TRY (
    gvs[finally_def, AllCaseEqs(), bind_def, ignore_bind_def, pop_scope_def, return_def, raise_def] >>
    qspecl_then [`cx`, `body`, `nm`, `v`, `st`] mp_tac try_body_preserves_tl_dom >>
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
  sg `MAP FDOM (TL (st with scopes updated_by CONS (FEMPTY |+ (nm,v))).scopes) = MAP FDOM (TL s'³'.scopes)` >-
  (qspecl_then [`cx`, `body`, `nm`, `v`, `st`] mp_tac try_body_preserves_tl_dom >>
   impl_tac >- (rpt strip_tac >> gvs[push_scope_with_var_def, return_def] >> first_x_assum drule >> simp[]) >>
   simp[push_scope_with_var_def, return_def] >> strip_tac >>
   first_x_assum drule >> simp[]) >> gvs[] >>
  (* Case split on broke *)
  Cases_on `broke` >> gvs[return_def, preserves_scopes_dom_def] >-
  (* broke = T: return () *)
  (Cases_on `st.scopes` >> Cases_on `tl` >> gvs[]) >>
  (* broke = F: use recursive IH *)
  qpat_x_assum `∀s'⁴' t s'⁵' t'. _ ⇒ _` (qspecl_then [`st`, `st with scopes updated_by CONS (FEMPTY |+ (nm,v))`,
                                                       `st with scopes updated_by CONS (FEMPTY |+ (nm,v))`,
                                                       `s'³' with scopes := tl`] mp_tac) >>
  simp[push_scope_with_var_def, return_def] >>
  simp[finally_def, AllCaseEqs(), bind_def, ignore_bind_def, pop_scope_def, return_def, raise_def] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  Cases_on `st.scopes` >> Cases_on `tl` >> gvs[]
QED

(* ------------------------------------------------------------------------
   Section 4: Helper Lemmas for Iterators and Targets

   These show iterators and targets preserve MAP FDOM exactly.
   We can reuse theorems from vyperEvalExprPreservesScopeDomTheory.
   ------------------------------------------------------------------------ *)

(* Iterator cases - preserve MAP FDOM exactly *)

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
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >>
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
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >>
  imp_res_tac return_scopes >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[])
QED

(* Target cases - preserve MAP FDOM exactly *)

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
  Cases_on `x` >> gvs[return_def] >>
  first_x_assum drule >> gvs[]
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
  imp_res_tac return_scopes >> gvs[] >>
  first_x_assum drule >> gvs[]
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
   Section 5: Main Mutual Induction Theorem

   Combines all cases via ho_match_mp_tac evaluate_ind.
   ------------------------------------------------------------------------ *)

(* Main mutual preservation theorem using evaluate_ind.

   WHY THIS IS TRUE:
   By structural induction on the mutually recursive evaluation.
   Each case is handled by the corresponding helper lemma above.
   The key insight is that:
   - Most operations preserve MAP FDOM exactly
   - Only AnnAssign adds to HD (via new_variable)
   - If/For use push/pop pattern which restores scopes exactly
   - Sequencing (eval_stmts cons) chains preservations

   Plan reference: Main theorem structure (Section "Proof Structure")
   Used in: Final theorem extraction *)
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
  (∀cx nm body vs st res st'. eval_for cx nm body vs st = (res, st') ⇒
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
  (* Raise *) >- (drule_all case_Raise_dom >> gvs[])
  (* Assert *) >- (drule case_Assert_dom >> rpt strip_tac >> metis_tac[eval_expr_preserves_scopes_dom])
  (* Log *) >- (drule_all case_Log_dom >> gvs[])
  (* AnnAssign *) >- (drule case_AnnAssign_dom >> simp[])
  (* Append *) >- (drule case_Append_dom >> rpt strip_tac >> metis_tac[eval_expr_preserves_scopes_dom])
  (* Assign *) >- (drule case_Assign_dom >> rpt strip_tac >> metis_tac[eval_expr_preserves_scopes_dom])
  (* AugAssign *) >- (drule case_AugAssign_dom >> rpt strip_tac >> metis_tac[eval_expr_preserves_scopes_dom])
  (* If *) >- (irule case_If_dom >> qexists_tac ‘cx’ >> qexists_tac `e` >> qexists_tac `res` >> qexists_tac `ss` >> qexists_tac `ss'` >> metis_tac[])
  (* For *) >- (irule case_For_dom >> qexists_tac ‘body’ >> qexists_tac ‘cx’ >> qexists_tac ‘id’ >> qexists_tac ‘it’ >> qexists_tac ‘n’ >> qexists_tac ‘res’ >> qexists_tac ‘typ’ >> metis_tac[])
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
  (* NameTarget *) >- metis_tac[eval_base_target_preserves_scopes_dom]
  (* TopLevelNameTarget *) >- metis_tac[eval_base_target_preserves_scopes_dom]
  (* AttributeTarget *) >- metis_tac[eval_base_target_preserves_scopes_dom]
  (* SubscriptTarget *) >- metis_tac[eval_base_target_preserves_scopes_dom]
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
   Section 6: Main Theorem
   ------------------------------------------------------------------------ *)

(* Main theorem: eval_stmts preserves scope structure.

   WHY THIS IS TRUE:
   Direct extraction from scopes_dom_mutual second conjunct.
   Unfold preserves_scopes_dom to get the explicit formulation.

   Plan reference: Final goal *)
Theorem eval_stmts_preserves_scopes:
  ∀cx st st' ss res.
    eval_stmts cx ss st = (res, st') ⇒
    (FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
     MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes))
Proof
  rpt strip_tac >>
  `preserves_scopes_dom st st'` by metis_tac[scopes_dom_mutual] >>
  gvs[preserves_scopes_dom_def]
QED
