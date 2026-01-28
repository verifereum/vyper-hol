# TASK: Main Mutual Induction Theorem - scopes_dom_mutual

## Goal

Replace cheat in `scopes_dom_mutual`. This is the main theorem that combines all cases via `ho_match_mp_tac evaluate_ind`.

## Theorem Statement

```sml
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
```

## Location

- File: `vyperEvalStmtsPreservesScopesScript.sml`
- Lines: ~530-550
- Context: Main mutual induction theorem combining all cases

## Mathematical Argument

**WHY THIS IS TRUE:**

This is proven by `ho_match_mp_tac evaluate_ind`. The evaluate_def creates a mutually recursive definition covering:
- eval_stmt (all statement cases)
- eval_stmts (nil and cons)
- eval_iterator (Array and Range)
- eval_target (BaseTarget and TupleTarget)
- eval_targets (nil and cons)
- eval_base_target (NameTarget, TopLevelNameTarget, SubscriptTarget, AttributeTarget)
- eval_for (nil and cons)
- eval_expr (all expression cases)
- eval_exprs (nil and cons)

The induction gives us IH for each recursive call. Each case is handled by the corresponding helper lemma:
- Statements use `preserves_scopes_dom` (HD can grow, TL unchanged)
- All other evaluators preserve `MAP FDOM` exactly

## Available Resources

### Helper Lemmas (all to be proven in other TASK files)
Statement cases:
- `case_Pass_dom`, `case_Continue_dom`, `case_Break_dom`, `case_Return_NONE_dom`
- `case_Return_SOME_dom`, `case_Raise_dom`, `case_Assert_dom`, `case_Log_dom`
- `case_Append_dom`, `case_Assign_dom`, `case_AugAssign_dom`, `case_Expr_dom`
- `case_AnnAssign_dom`
- `case_If_dom`, `case_For_dom`
- `case_eval_stmts_nil_dom`, `case_eval_stmts_cons_dom`
- `case_eval_for_nil_dom`, `case_eval_for_cons_dom`

Iterator/Target cases:
- `case_Array_iterator_dom`, `case_Range_iterator_dom`
- `case_BaseTarget_dom`, `case_TupleTarget_dom`
- `case_eval_targets_nil_dom`, `case_eval_targets_cons_dom`

Expression/base_target cases:
- Use `eval_expr_preserves_scopes_dom` and `eval_base_target_preserves_scopes_dom` from `vyperEvalExprPreservesScopeDomTheory`

### Key Theorems from vyperEvalExprPreservesScopeDomTheory
- `eval_expr_preserves_scopes_dom`: `∀e cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes`
- `eval_base_target_preserves_scopes_dom`: `∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes`

## Proof Structure

```sml
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  
  (* Statement cases - apply case_*_dom lemmas *)
  (* 1. Pass *)
  >- ACCEPT_TAC case_Pass_dom
  (* 2. Continue *)
  >- ACCEPT_TAC case_Continue_dom
  (* 3. Break *)
  >- ACCEPT_TAC case_Break_dom
  (* 4. Return NONE *)
  >- ACCEPT_TAC case_Return_NONE_dom
  (* 5. Return (SOME e) *)
  >- (rpt strip_tac >> irule case_Return_SOME_dom >>
      qexists_tac `e` >> simp[] >> rpt strip_tac >> res_tac >> simp[])
  (* ... similar for other statement cases ... *)
  
  (* eval_stmts cases *)
  >- ACCEPT_TAC case_eval_stmts_nil_dom
  >- (rpt strip_tac >> irule case_eval_stmts_cons_dom >> ...)
  
  (* Iterator cases *)
  >- (rpt strip_tac >> irule case_Array_iterator_dom >> ...)
  >- (rpt strip_tac >> irule case_Range_iterator_dom >> ...)
  
  (* Target cases *)
  >- (rpt strip_tac >> irule case_BaseTarget_dom >> ...)
  >- (rpt strip_tac >> irule case_TupleTarget_dom >> ...)
  >- ACCEPT_TAC case_eval_targets_nil_dom
  >- (rpt strip_tac >> irule case_eval_targets_cons_dom >> ...)
  
  (* base_target cases - use eval_base_target_preserves_scopes_dom *)
  >- (rpt strip_tac >> drule eval_base_target_preserves_scopes_dom >> simp[])
  (* ... for each base_target constructor ... *)
  
  (* eval_for cases *)
  >- ACCEPT_TAC case_eval_for_nil_dom
  >- (rpt strip_tac >> irule case_eval_for_cons_dom >> ...)
  
  (* expr cases - use eval_expr_preserves_scopes_dom *)
  >- (rpt strip_tac >> drule eval_expr_preserves_scopes_dom >> simp[])
  (* ... for each expr constructor ... *)
  
  (* eval_exprs cases *)
  >- simp[evaluate_def, return_def]
  >- (rpt strip_tac >> ... chain eval_expr and eval_exprs IH ...)
QED
```

## Key Insight

The proof has ~46 cases matching evaluate_ind. Most cases fall into patterns:
1. **Simple statement cases**: Apply corresponding case_*_dom lemma with IH from induction
2. **eval_stmts/eval_for nil**: Trivial (return ())
3. **eval_stmts/eval_for cons**: Apply case_*_cons_dom with chained IH
4. **Iterator/target cases**: Apply corresponding helper with IH
5. **Expression/base_target cases**: Directly use existing theorems from vyperEvalExprPreservesScopeDomTheory
6. **eval_exprs cases**: Chain eval_expr preserves with eval_exprs preserves

## Constraints

- Output must be valid HOL4 tactic proof
- Must not introduce new cheats
- All helper lemmas must be proven first
- This proof will be ~100-150 lines due to number of cases

## Deliverable

Replace `cheat` with complete proof. Return:
1. The proof tactics
2. List of any helper lemmas that need adjustment

Note: The exact case order depends on how evaluate_ind is structured. You may need to check the induction principle to match cases correctly:
```sml
DB.find "evaluate_ind" (* in HOL session *)
```
