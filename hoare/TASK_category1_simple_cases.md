# TASK: Category 1 Simple Cases - Statements that preserve scopes exactly

## Goal

Replace cheats in the Category 1 helper lemmas. These are statements that preserve `MAP FDOM st.scopes` exactly (not just subset), so both parts of `preserves_scopes_dom` hold trivially.

Theorems to prove:
1. `case_Return_SOME_dom`
2. `case_Raise_dom`
3. `case_Assert_dom`
4. `case_Log_dom`
5. `case_Append_dom`
6. `case_Assign_dom`
7. `case_AugAssign_dom`
8. `case_Expr_dom`

## Theorem Statements

All have the same pattern: given that sub-expressions preserve MAP FDOM exactly, the statement preserves `preserves_scopes_dom st st'`.

```sml
Theorem case_Return_SOME_dom:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Return (SOME e)) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_Raise_dom:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Raise e) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_Assert_dom:
  ∀cx e se.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx se st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Assert e se) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_Log_dom:
  ∀cx id es.
    (∀st res st'. eval_exprs cx es st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Log id es) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_Append_dom:
  ∀cx bt e.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Append bt e) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_Assign_dom:
  ∀cx g e.
    (∀st res st'. eval_target cx g st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Assign g e) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_AugAssign_dom:
  ∀cx bt bop e.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (AugAssign bt bop e) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_Expr_dom:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Expr e) st = (res, st') ⇒ preserves_scopes_dom st st'
```

## Location

- File: `vyperEvalStmtsPreservesScopesScript.sml`
- Context: Helper lemmas for Category 1 statement cases

## Mathematical Argument

**WHY THESE ARE TRUE:**
All these statements only call operations that preserve `MAP FDOM st.scopes` exactly:
- `eval_expr` (by IH assumption)
- `eval_base_target` (by IH assumption)
- `eval_target` (by IH assumption)
- `eval_exprs` (by IH assumption)
- `get_Value`, `lift_option`, `lift_sum`, `raise` (preserve scopes exactly)
- `assign_target` (preserves scopes_dom - proven in vyperScopePreservationLemmasTheory)
- `push_log` (preserves scopes - push_log_scopes)
- `switch_BoolV` (preserves if both branches preserve)

Since all operations preserve MAP FDOM exactly:
- `HD` unchanged means `FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes)` (reflexive)
- `TL` unchanged means `MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)` (exact equality)

## Available Resources

### From vyperScopePreservationLemmasTheory
- `return_scopes`, `raise_scopes`, `check_scopes`
- `get_Value_scopes`, `lift_option_scopes`, `lift_sum_scopes`
- `push_log_scopes`, `switch_BoolV_scopes`
- `assign_target_preserves_scopes_dom`

### Definition
- `preserves_scopes_dom_def`
- `evaluate_def` (for eval_stmt cases)

## Proof Approach

General pattern:
1. Unfold `preserves_scopes_dom_def`
2. Unfold `evaluate_def` for the specific statement
3. Unfold `bind_def`, handle `AllCaseEqs()`
4. Apply IH assumptions to chain MAP FDOM preservation
5. Use helper lemmas (get_Value_scopes, etc.) for intermediate operations
6. Final state has same MAP FDOM, which implies both ⊆ and TL equality

Example for case_Return_SOME_dom:
```sml
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def, evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_Value_scopes >> gvs[raise_def] >>
  first_x_assum drule >> simp[] >> (* MAP FDOM unchanged through eval_expr *)
  strip_tac >> simp[] (* ⊆ reflexive, TL equal *)
QED
```

## Constraints

- Output must be valid HOL4 tactic proofs
- Must not introduce new cheats
- Key theorems to use: scopes preservation lemmas from vyperScopePreservationLemmasTheory
- All proofs should be similar/uniform in structure

## Deliverable

Replace each `cheat` with a complete proof. Return:
1. The proof tactics for all 8 theorems
2. Any issues encountered
