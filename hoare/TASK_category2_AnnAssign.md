# TASK: Category 2 - AnnAssign (adds to HD, preserves TL)

## Goal

Replace cheat in `case_AnnAssign_dom`. This is the only statement that actually adds to the HD scope (via `new_variable`), while preserving TL exactly.

## Theorem Statement

```sml
Theorem case_AnnAssign_dom:
  ∀cx id typ e.
    (∀st res st'. eval_expr cx e st = (res, st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (AnnAssign id typ e) st = (res, st') ⇒ preserves_scopes_dom st st'
```

## Location

- File: `vyperEvalStmtsPreservesScopesScript.sml`
- Line: ~195
- Context: The only Category 2 case - new variable declaration

## Mathematical Argument

**WHY THIS IS TRUE:**

The statement `AnnAssign id typ e` evaluates as:
```sml
eval_stmt cx (AnnAssign id typ e) = do
  tv <- eval_expr cx e;
  v <- get_Value tv;
  new_variable id v
od
```

Step by step:
1. `eval_expr cx e st = (tv, st1)` - preserves MAP FDOM exactly (by IH)
2. `get_Value tv st1 = (v, st2)` - preserves scopes exactly (get_Value_scopes)
3. `new_variable id v st2 = (res, st')` - adds id to HD, TL unchanged

For step 3, `new_variable_def` does:
- `set_scopes ((e |+ (string_to_num id, v))::es)` where `e::es = st2.scopes`
- So `HD st'.scopes = e |+ (string_to_num id, v)`
- And `TL st'.scopes = es = TL st2.scopes`

Combined:
- `FDOM (HD st.scopes) = FDOM (HD st1.scopes) = FDOM (HD st2.scopes) = FDOM e`
- `FDOM (HD st'.scopes) = FDOM (e |+ (string_to_num id, v))` which contains `FDOM e`
- Therefore `FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes)` ✓

For TL:
- `TL st'.scopes = TL st2.scopes = TL st1.scopes = TL st.scopes`
- `MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)` ✓

## Available Resources

### Definitions
- `evaluate_def` (for AnnAssign case)
- `new_variable_def`
- `preserves_scopes_dom_def`

### Helper Lemmas
- `new_variable_scope_property` (to be proven in TASK_infrastructure_lemmas)
- `get_Value_scopes` (from vyperScopePreservationLemmasTheory)
- `eval_expr_preserves_scopes_dom` (from vyperEvalExprPreservesScopeDomTheory)

## Proof Approach

```sml
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* Get st -> st1 from eval_expr *)
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_x_assum drule >> simp[]) >>
  (* Get st1 -> st2 from get_Value *)
  imp_res_tac get_Value_scopes >> gvs[] >>
  (* Get st2 -> st' from new_variable *)
  `FDOM (HD s'³'.scopes) ⊆ FDOM (HD st'.scopes) ∧ TL st'.scopes = TL s'³'.scopes`
    by (irule new_variable_scope_property >> simp[] >> (* need st.scopes ≠ [] *) cheat) >>
  (* Chain the results *)
  conj_tac
  >- (irule SUBSET_TRANS >> qexists_tac `FDOM (HD s'³'.scopes)` >>
      simp[] >> (* Use MAP FDOM equality to get FDOM HD equality *) cheat)
  >- simp[]
QED
```

Note: This proof sketch shows the structure. The actual proof needs to:
1. Handle the case `st.scopes ≠ []` (possibly as additional precondition or by extracting from context)
2. Use `MAP FDOM st.scopes = MAP FDOM st'.scopes` to derive HD equality

A cleaner approach uses the fact that `MAP FDOM unchanged ⇒ HD and TL unchanged`:
```sml
`FDOM (HD st.scopes) = FDOM (HD s'³'.scopes)` by (use MAP FDOM equality)
```

## Constraints

- Output must be valid HOL4 tactic proofs
- Must not introduce new cheats
- Depends on `new_variable_scope_property` being proven first

## Deliverable

Replace `cheat` with complete proof. Return:
1. The proof tactics
2. Any issues encountered (especially around st.scopes ≠ [] assumption)
