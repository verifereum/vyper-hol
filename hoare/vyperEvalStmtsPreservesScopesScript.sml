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
   Section 3: Helper Lemmas for Individual Statement Cases

   Each statement type gets a helper lemma showing it preserves scopes.
   Category 1: Preserve exactly (MAP FDOM unchanged)
   Category 2: AnnAssign (HD grows, TL unchanged)
   Category 3-4: If/For (push/pop with body)
   Category 5-6: eval_stmts/eval_for (sequencing/iteration)
   ------------------------------------------------------------------------ *)

(* === Category 1: Statements that preserve scopes exactly === *)

(* These all preserve MAP FDOM exactly, so both parts of preserves_scopes_dom hold trivially *)

Theorem case_Pass_dom:
  ∀cx st res st'.
    eval_stmt cx Pass st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, return_def, preserves_scopes_dom_def]
QED

Theorem case_Continue_dom:
  ∀cx st res st'.
    eval_stmt cx Continue st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, raise_def, preserves_scopes_dom_def]
QED

Theorem case_Break_dom:
  ∀cx st res st'.
    eval_stmt cx Break st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, raise_def, preserves_scopes_dom_def]
QED

Theorem case_Return_NONE_dom:
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
Theorem map_fdom_eq_preserves_dom:
  ∀st st'. MAP FDOM st.scopes = MAP FDOM st'.scopes ⇒ preserves_scopes_dom st st'
Proof
  simp[preserves_scopes_dom_def] >> rpt strip_tac >>
  Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[]
QED

Theorem case_Return_SOME_dom:
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

Theorem case_Raise_dom:
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

Theorem case_Assert_dom:
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

Theorem case_Log_dom:
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

Theorem case_Append_dom:
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

Theorem case_Assign_dom:
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

Theorem case_AugAssign_dom:
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

Theorem case_Expr_dom:
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
Theorem case_AnnAssign_dom:
  ∀cx id typ e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (AnnAssign id typ e) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  cheat (* TODO: Unfold eval_stmt, chain eval_expr (preserves exactly),
           get_Value (preserves exactly), new_variable (adds to HD only).
           Use new_variable_scope_property. *)
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
   Used in: main induction *)
Theorem case_If_dom:
  ∀cx e ss1 ss2.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_stmts cx ss1 st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (∀st res st'. eval_stmts cx ss2 st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_stmt cx (If e ss1 ss2) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  cheat (* TODO: Unfold eval_stmt for If.
           Use eval_expr preserves (exactly), push_scope_finally_pop_preserves_dom,
           IH on bodies via switch_BoolV_scopes. Key: push/pop pattern restores. *)
QED

(* === Category 4: For statement === *)

(* For: eval_iterator, check, then eval_for.

   WHY THIS IS TRUE:
   1. eval_iterator preserves MAP FDOM exactly (uses eval_expr)
   2. check preserves exactly
   3. eval_for preserves by its own IH
   Combined: preserves_scopes_dom

   Plan reference: Category 4
   Used in: main induction *)
Theorem case_For_dom:
  ∀cx id typ it n body.
    (∀st res st'. eval_iterator cx it st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀vs st res st'. eval_for cx (string_to_num id) body vs st = (res, st') ⇒
       preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  cheat (* TODO: Unfold eval_stmt For, chain eval_iterator (preserves exactly),
           check_scopes (preserves exactly), IH on eval_for *)
QED

(* === Category 5: eval_stmts (sequencing) === *)

Theorem case_eval_stmts_nil_dom:
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
Theorem case_eval_stmts_cons_dom:
  ∀cx s ss.
    (∀st res st'. eval_stmt cx s st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (∀st res st'. eval_stmts cx ss st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_stmts cx (s::ss) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  cheat (* TODO: Unfold eval_stmts cons, use bind_def.
           Apply IH on s to get st -> st1, then IH on ss to get st1 -> st'.
           Use SUBSET_TRANS for HD, equality chain for TL. *)
QED

(* === Category 6: eval_for (iteration) === *)

Theorem case_eval_for_nil_dom:
  ∀cx nm body st res st'.
    eval_for cx nm body [] st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  simp[evaluate_def, return_def, preserves_scopes_dom_def]
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
   Used in: main induction *)
Theorem case_eval_for_cons_dom:
  ∀cx nm body v vs.
    (∀st res st'. eval_stmts cx body st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (∀st res st'. eval_for cx nm body vs st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_for cx nm body (v::vs) st = (res, st') ⇒ preserves_scopes_dom st st'
Proof
  cheat (* TODO: Unfold eval_for cons.
           push_scope_with_var creates new scope.
           finally with pop_scope pattern restores.
           Recursive call uses IH.
           Handle broke=T case (return ()) and broke=F case (recursive). *)
QED

(* ------------------------------------------------------------------------
   Section 4: Helper Lemmas for Iterators and Targets

   These show iterators and targets preserve MAP FDOM exactly.
   We can reuse theorems from vyperEvalExprPreservesScopeDomTheory.
   ------------------------------------------------------------------------ *)

(* Iterator cases - preserve MAP FDOM exactly *)

Theorem case_Array_iterator_dom:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_iterator cx (Array e) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  cheat (* TODO: Unfold eval_iterator Array, chain eval_expr, get_Value, lift_option *)
QED

Theorem case_Range_iterator_dom:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e2 st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_iterator cx (Range e1 e2) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  cheat (* TODO: Unfold eval_iterator Range, chain two eval_exprs *)
QED

(* Target cases - preserve MAP FDOM exactly *)

Theorem case_BaseTarget_dom:
  ∀cx bt.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_target cx (BaseTarget bt) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  cheat (* TODO: eval_target just wraps eval_base_target *)
QED

Theorem case_TupleTarget_dom:
  ∀cx gs.
    (∀st res st'. eval_targets cx gs st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_target cx (TupleTarget gs) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  cheat (* TODO: eval_target just wraps eval_targets *)
QED

Theorem case_eval_targets_nil_dom:
  ∀cx st res st'.
    eval_targets cx [] st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_targets_cons_dom:
  ∀cx g gs.
    (∀st res st'. eval_target cx g st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_targets cx gs st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_targets cx (g::gs) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  cheat (* TODO: Chain eval_target and eval_targets *)
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
Theorem scopes_dom_mutual:
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
  cheat (* TODO: ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
           Apply each case_*_dom helper lemma in order.
           For expr/base_target/exprs cases, use existing theorems from
           vyperEvalExprPreservesScopeDomTheory (eval_expr_preserves_scopes_dom etc.) *)
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
