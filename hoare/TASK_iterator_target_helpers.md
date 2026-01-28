# TASK: Iterator and Target Helper Lemmas - Preserve MAP FDOM exactly

## Goal

Replace cheats in the iterator and target helper lemmas. These show that iterators and targets preserve `MAP FDOM st.scopes` exactly.

Theorems to prove:
1. `case_Array_iterator_dom`
2. `case_Range_iterator_dom`
3. `case_BaseTarget_dom`
4. `case_TupleTarget_dom`
5. `case_eval_targets_cons_dom`

## Theorem Statements

```sml
Theorem case_Array_iterator_dom:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_iterator cx (Array e) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes

Theorem case_Range_iterator_dom:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e2 st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_iterator cx (Range e1 e2) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes

Theorem case_BaseTarget_dom:
  ∀cx bt.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_target cx (BaseTarget bt) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes

Theorem case_TupleTarget_dom:
  ∀cx gs.
    (∀st res st'. eval_targets cx gs st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_target cx (TupleTarget gs) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes

Theorem case_eval_targets_cons_dom:
  ∀cx g gs.
    (∀st res st'. eval_target cx g st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_targets cx gs st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_targets cx (g::gs) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
```

## Location

- File: `vyperEvalStmtsPreservesScopesScript.sml`
- Lines: ~310-370
- Context: Helper lemmas for iterators and targets

## Mathematical Argument

**WHY THESE ARE TRUE:**

All these operations only call:
- `eval_expr` (by IH assumption, preserves MAP FDOM)
- `eval_base_target` (by IH assumption)
- `eval_target` (by IH assumption)
- `eval_targets` (by IH assumption)
- `get_Value`, `lift_option`, `lift_sum` (preserve scopes exactly)

Since all operations preserve MAP FDOM exactly, chaining them preserves MAP FDOM exactly.

### case_Array_iterator_dom
```sml
eval_iterator cx (Array e) = do
  tv <- eval_expr cx e;
  v <- get_Value tv;
  vs <- lift_option (extract_elements v) "For not ArrayV";
  return vs
od
```
All operations preserve, so MAP FDOM unchanged.

### case_Range_iterator_dom
```sml
eval_iterator cx (Range e1 e2) = do
  tv1 <- eval_expr cx e1;
  v1 <- get_Value tv1;
  tv2 <- eval_expr cx e2;
  v2 <- get_Value tv2;
  ...
  return $ GENLIST ...
od
```
Both eval_expr calls preserve (by IH), get_Value preserves, return preserves.

### case_BaseTarget_dom and case_TupleTarget_dom
These just wrap eval_base_target/eval_targets with return.

### case_eval_targets_cons_dom
```sml
eval_targets cx (g::gs) = do
  gv <- eval_target cx g;
  gvs <- eval_targets cx gs;
  return $ gv::gvs
od
```
Chain eval_target (by IH), eval_targets (by IH), return.

## Available Resources

### Definitions
- `evaluate_def` (for iterators and targets)

### Helper Lemmas (from vyperScopePreservationLemmasTheory)
- `get_Value_scopes`
- `lift_option_scopes`
- `lift_sum_scopes`
- `return_scopes`

### Already Proven (in this file)
- `eval_expr_preserves_scopes_dom` (from vyperEvalExprPreservesScopeDomTheory)
- `eval_base_target_preserves_scopes_dom` (from vyperEvalExprPreservesScopeDomTheory)

## Proof Approach

General pattern:
1. Unfold `evaluate_def` for the specific case
2. Unfold `bind_def`, handle `AllCaseEqs()`
3. Apply IH assumptions on sub-calls
4. Use helper lemmas for intermediate operations
5. Chain MAP FDOM equalities

Example for case_Array_iterator_dom:
```sml
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* eval_expr preserves by IH *)
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by res_tac >>
  (* get_Value preserves *)
  imp_res_tac get_Value_scopes >> gvs[] >>
  (* lift_option preserves *)
  imp_res_tac lift_option_scopes >> gvs[] >>
  (* return preserves *)
  gvs[return_def]
QED
```

## Constraints

- Output must be valid HOL4 tactic proofs
- Must not introduce new cheats
- All proofs should be similar/uniform in structure

## Deliverable

Replace each `cheat` with complete proof. Return:
1. The proof tactics for all 5 theorems
2. Any issues encountered
