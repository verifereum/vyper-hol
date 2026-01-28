# TASK: Category 3-4 - If and For statements (push/pop scope pattern)

## Goal

Replace cheats in `case_If_dom` and `case_For_dom`. These statements use the push_scope/pop_scope pattern with finally, which restores the original scope structure.

## Theorem Statements

```sml
Theorem case_If_dom:
  ∀cx e ss1 ss2.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_stmts cx ss1 st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (∀st res st'. eval_stmts cx ss2 st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_stmt cx (If e ss1 ss2) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_For_dom:
  ∀cx id typ it n body.
    (∀st res st'. eval_iterator cx it st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀vs st res st'. eval_for cx (string_to_num id) body vs st = (res, st') ⇒
       preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res, st') ⇒ preserves_scopes_dom st st'
```

## Location

- File: `vyperEvalStmtsPreservesScopesScript.sml`
- Lines: ~200-230
- Context: Category 3-4 cases using push/pop pattern

## Mathematical Argument

### case_If_dom

**WHY THIS IS TRUE:**

The If statement evaluates as:
```sml
eval_stmt cx (If e ss1 ss2) = do
  tv <- eval_expr cx e;
  push_scope;
  finally (
    switch_BoolV tv (eval_stmts cx ss1) (eval_stmts cx ss2)
  ) pop_scope
od
```

Step by step:
1. `eval_expr cx e st = (tv, st1)` - preserves MAP FDOM exactly (by IH)
2. `push_scope st1 = ((), st2)` - creates HD = FEMPTY, TL = st1.scopes
3. Body `switch_BoolV` runs one of ss1 or ss2 on st2
   - By IH: `preserves_scopes_dom st2 body_st'`
   - This means: `FDOM (HD st2.scopes) ⊆ FDOM (HD body_st'.scopes)` (FEMPTY ⊆ anything)
   - And: `MAP FDOM (TL st2.scopes) = MAP FDOM (TL body_st'.scopes)` = `MAP FDOM st1.scopes`
4. `finally` with `pop_scope`: `st'.scopes = TL body_st'.scopes`
5. Therefore: `MAP FDOM st'.scopes = MAP FDOM (TL body_st'.scopes) = MAP FDOM st1.scopes = MAP FDOM st.scopes`

Since MAP FDOM st'.scopes = MAP FDOM st.scopes, we have `preserves_scopes_dom st st'` (with reflexive ⊆ and exact TL equality).

### case_For_dom

**WHY THIS IS TRUE:**

The For statement evaluates as:
```sml
eval_stmt cx (For id typ it n body) = do
  vs <- eval_iterator cx it;
  check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
  eval_for cx (string_to_num id) body vs
od
```

Step by step:
1. `eval_iterator cx it st = (vs, st1)` - preserves MAP FDOM exactly (by IH)
2. `check` - preserves scopes exactly (check_scopes)
3. `eval_for` - preserves scopes_dom (by IH)

Combined: MAP FDOM st.scopes = MAP FDOM st1.scopes, then st1 -> st' preserves scopes_dom, so st -> st' preserves scopes_dom.

## Available Resources

### Definitions
- `evaluate_def` (for If, For cases)
- `preserves_scopes_dom_def`
- `finally_def`, `push_scope_def`, `pop_scope_def`
- `switch_BoolV_def`

### Helper Lemmas
- `push_scope_finally_pop_preserves_dom` (to be proven in TASK_infrastructure_lemmas)
- `switch_BoolV_scopes` (from vyperScopePreservationLemmasTheory)
- `check_scopes`
- `eval_expr_preserves_scopes_dom`

## Proof Approach

### case_If_dom
```sml
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* eval_expr preserves MAP FDOM *)
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_x_assum drule >> simp[]) >>
  (* Key: push_scope; finally body pop_scope pattern *)
  (* Use push_scope_finally_pop_preserves_dom or inline reasoning *)
  (* The body (switch_BoolV) preserves scopes_dom by IH *)
  (* After pop_scope: MAP FDOM st'.scopes = MAP FDOM s''.scopes = MAP FDOM st.scopes *)
  cheat
QED
```

### case_For_dom
```sml
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* eval_iterator preserves MAP FDOM *)
  `MAP FDOM st.scopes = MAP FDOM iter_st.scopes` by res_tac >>
  (* check preserves *)
  imp_res_tac check_scopes >> gvs[] >>
  (* eval_for preserves scopes_dom *)
  first_x_assum drule >> simp[preserves_scopes_dom_def] >> strip_tac >>
  (* Chain: st -> iter_st (equal) -> st' (preserves_scopes_dom) *)
  cheat
QED
```

## Constraints

- Output must be valid HOL4 tactic proofs
- Must not introduce new cheats
- Depends on infrastructure lemmas being proven first
- The If case is more complex due to the push/finally/pop pattern

## Deliverable

Replace each `cheat` with complete proof. Return:
1. The proof tactics for both theorems
2. Any issues encountered
