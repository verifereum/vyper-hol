# Proof Plan: eval_stmts_preserves_scopes

## Goal

```sml
Theorem eval_stmts_preserves_scopes:
  ∀cx st st' ss res.
    eval_stmts cx ss st = (res, st') ⇒
    (FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
     MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes))
Proof
  cheat
QED
```

## Verdict: PROVABLE

## Unverified Assumptions: NONE

All claims have been verified against the definitions.

## Key Insights

1. **HD scope can only grow**: The only operation that adds to the HD scope is `new_variable` (used by `AnnAssign`), which does `e |+ (n,v)` on the head scope.

2. **TL scopes are preserved by most operations**: `eval_expr`, `eval_base_target`, `assign_target`, and most monad operations preserve `MAP FDOM` of all scopes exactly.

3. **Scoped constructs restore scopes**: `If` and `For` use `push_scope`/`pop_scope` with `finally`, which restores the original scope structure.

4. **Existing theorems cover expressions and targets**: `eval_expr_preserves_scopes_dom` and `eval_base_target_preserves_scopes_dom` already prove that these preserve `MAP FDOM st.scopes` exactly.

## Proof Strategy

Use `ho_match_mp_tac evaluate_ind` to get the induction principle for the mutually recursive definition. The proof requires:

1. **Predicates for mutual induction**: Define predicates for `eval_stmt`, `eval_stmts`, `eval_for`, and other mutually defined functions.

2. **Helper lemmas for complex cases**: Create helper lemmas for each complex statement case that states the goal for that case exactly, then cheat them initially and prove the main theorem using the helpers.

3. **Prove helper lemmas**: After the main theorem structure is established, go back and prove each helper lemma.

## Required Existing Theorems (to be reused)

### From vyperEvalExprPreservesScopeDomTheory
- `eval_expr_preserves_scopes_dom`: `∀e cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes`
- `eval_base_target_preserves_scopes_dom`: `∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes`

### From vyperScopePreservationLemmasTheory
- `assign_target_preserves_scopes_dom`: Preserves `MAP FDOM st.scopes`
- `eval_exprs_preserves_scopes_dom`: Preserves `MAP FDOM st.scopes`
- `finally_set_scopes_dom`: `finally f (set_scopes prev) s = (res, s') ⇒ MAP FDOM s'.scopes = MAP FDOM prev`
- `finally_pop_function_scopes`: `finally f (pop_function prev) st = (res, st') ⇒ st'.scopes = prev`
- Various `*_scopes` lemmas for monad operations (preserve scopes exactly)

## Statement Case Analysis

### Category 1: Preserve scopes exactly (MAP FDOM unchanged)
These cases preserve `MAP FDOM st.scopes` exactly, so both parts of the goal are trivially satisfied.

| Statement | Operations | Why it preserves scopes |
|-----------|-----------|------------------------|
| Pass | `return ()` | return_scopes |
| Continue | `raise ContinueException` | raise_scopes |
| Break | `raise BreakException` | raise_scopes |
| Return NONE | `raise (ReturnException NoneV)` | raise_scopes |
| Return (SOME e) | eval_expr, get_Value, raise | eval_expr_preserves_scopes_dom, raise_scopes |
| Raise e | eval_expr, get_Value, lift_option, raise | eval_expr_preserves_scopes_dom, raise_scopes |
| Assert e se | eval_expr, switch_BoolV, eval_expr, raise | eval_expr_preserves_scopes_dom on both |
| Log id es | eval_exprs, push_log | eval_exprs_preserves_scopes_dom, push_log_scopes |
| Append bt e | eval_base_target, eval_expr, assign_target | All three preserve scopes_dom |
| Assign g e | eval_target, eval_expr, assign_target | eval_expr + assign_target preserve scopes_dom |
| AugAssign t bop e | eval_base_target, eval_expr, assign_target | All preserve scopes_dom |
| Expr e | eval_expr, get_Value | eval_expr_preserves_scopes_dom |

**Note on IntCall**: Internal function calls (`Call (IntCall ...)`) are expressions, not statements. They are handled via the `Expr e` statement case, which applies `eval_expr_preserves_scopes_dom`. The `eval_expr` theorem already covers `IntCall` (which uses `push_function`/`pop_function` with `finally` internally to restore scopes).

### Category 2: AnnAssign (adds to HD, preserves TL)
```sml
eval_stmt cx (AnnAssign id typ e) = do
  tv <- eval_expr cx e;
  v <- get_Value tv;
  new_variable id v
od
```

**Analysis:**
- `eval_expr` preserves `MAP FDOM st.scopes` exactly
- `get_Value` preserves scopes exactly
- `new_variable id v` does `set_scopes ((e |+ (n, v))::es)` where `e::es = st.scopes`
- Result: `HD st'.scopes = HD st.scopes |+ (n, v)`, so `FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes)`
- `TL st'.scopes = es = TL st.scopes`, so `MAP FDOM (TL st'.scopes) = MAP FDOM (TL st.scopes)`

**Helper lemma needed:**
```sml
Theorem case_AnnAssign:
  ∀cx id typ e st res st'.
    eval_stmt cx (AnnAssign id typ e) st = (res, st') ⇒
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)
```

### Category 3: If (push_scope, body, pop_scope with finally)
```sml
eval_stmt cx (If e ss1 ss2) = do
  tv <- eval_expr cx e;
  push_scope;
  finally (
    switch_BoolV tv (eval_stmts cx ss1) (eval_stmts cx ss2)
  ) pop_scope
od
```

**Analysis:**
- `eval_expr cx e` preserves `MAP FDOM st.scopes` exactly
- After `push_scope`: scopes become `FEMPTY :: st.scopes`
  - In the new state: HD = FEMPTY, TL = st.scopes
- The body (`switch_BoolV` with eval_stmts) runs with the pushed scope
  - By IH on the body: `FDOM FEMPTY ⊆ FDOM (HD body_st'.scopes)` and `MAP FDOM st.scopes = MAP FDOM (TL body_st'.scopes)`
- `finally` with `pop_scope` restores to the original scope structure
  - After pop_scope: scopes become `TL body_st'.scopes`
  - By the IH on body, this equals `st.scopes` in terms of `MAP FDOM`

**Key insight**: The `finally ... pop_scope` pattern ensures that after If, we're back to the original scopes. Need a lemma about finally with pop_scope.

**Helper lemma needed:**
```sml
Theorem case_If:
  ∀cx e ss1 ss2.
    (∀st res st'. eval_stmts cx ss1 st = (res, st') ⇒
       FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
       MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)) ⇒
    (∀st res st'. eval_stmts cx ss2 st = (res, st') ⇒
       FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
       MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)) ⇒
    ∀st res st'.
      eval_stmt cx (If e ss1 ss2) st = (res, st') ⇒
      FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
      MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)
```

**Proof sketch for case_If:**
1. Unfold `eval_stmt` for If
2. Apply `eval_expr_preserves_scopes_dom` for the condition
3. After `push_scope`, HD = FEMPTY, TL = original scopes
4. Body runs: by IH, `MAP FDOM (TL body_st'.scopes) = MAP FDOM (TL pushed_st.scopes) = MAP FDOM st.scopes`
5. `finally` with `pop_scope` pops the head, leaving TL = body_st' TL
6. By IH reasoning, final scopes = original scopes in terms of MAP FDOM

### Category 4: For (push_scope_with_var, body, pop_scope in finally)
```sml
eval_stmt cx (For id typ it n body) = do
  vs <- eval_iterator cx it;
  check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
  eval_for cx (string_to_num id) body vs
od

eval_for cx nm body [] = return ()
eval_for cx nm body (v::vs) = do
  push_scope_with_var nm v;
  broke <- finally
    (try (do eval_stmts cx body; return F od) handle_loop_exception)
    pop_scope;
  if broke then return () else eval_for cx nm body vs
od
```

**Analysis:**
- `eval_iterator` evaluates expressions → preserves scopes exactly
- `eval_for` loop: each iteration pushes a scope, runs body, pops via finally
- By similar reasoning to If, each iteration preserves the scope structure

**Helper lemma needed:**
```sml
Theorem case_For:
  ∀cx id typ it n body.
    (∀st res st'. eval_for cx (string_to_num id) body vs st = (res, st') ⇒ ...) ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res, st') ⇒
      FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
      MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)
```

### Category 5: eval_stmts (sequencing)
```sml
eval_stmts cx [] = return ()
eval_stmts cx (s::ss) = do eval_stmt cx s; eval_stmts cx ss od
```

**Analysis:**
- Empty: `return ()` preserves scopes exactly
- Cons: By IH on `eval_stmt cx s`, HD can grow, TL preserved. By IH on `eval_stmts cx ss`, HD can grow further, TL preserved.
- Result: HD subset property is transitive (if A ⊆ B and B ⊆ C then A ⊆ C), TL equality chains

**Helper lemma needed:**
```sml
Theorem case_eval_stmts_cons:
  ∀cx s ss.
    (∀st res st'. eval_stmt cx s st = (res, st') ⇒
       FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
       MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)) ⇒
    (∀st res st'. eval_stmts cx ss st = (res, st') ⇒
       FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
       MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)) ⇒
    ∀st res st'.
      eval_stmts cx (s::ss) st = (res, st') ⇒
      FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
      MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)
```

### Category 6: eval_for (iteration)

**Helper lemmas needed:**
```sml
Theorem case_eval_for_nil:
  ∀cx nm body st res st'.
    eval_for cx nm body [] st = (res, st') ⇒
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)

Theorem case_eval_for_cons:
  ∀cx nm body v vs.
    (∀st res st'. eval_stmts cx body st = (res, st') ⇒
       FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
       MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)) ⇒
    (∀st res st'. eval_for cx nm body vs st = (res, st') ⇒
       FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
       MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)) ⇒
    ∀st res st'.
      eval_for cx nm body (v::vs) st = (res, st') ⇒
      FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
      MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)
```

## Additional Supporting Lemmas

### Lemma: finally_pop_scope_preserves_dom

```sml
Theorem finally_pop_scope_preserves_dom:
  ∀body st res st'.
    finally body pop_scope st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM (TL st.scopes)
```

**Proof sketch:**
- `finally` runs `body`, then runs `pop_scope` regardless of result
- `pop_scope` sets scopes to `TL body_st'.scopes`
- By hypothesis on body, `MAP FDOM (TL body_st'.scopes) = MAP FDOM (TL st.scopes)`
- Therefore `MAP FDOM st'.scopes = MAP FDOM (TL st.scopes)`

### Lemma: new_variable_scope_property

```sml
Theorem new_variable_scope_property:
  ∀id v st res st'.
    new_variable id v st = (res, st') ∧ st.scopes ≠ [] ⇒
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    TL st'.scopes = TL st.scopes
```

**Proof sketch:**
- Unfold `new_variable_def`
- In the success case: `set_scopes ((e |+ (n, v))::es)` where `e::es = st.scopes`
- `HD st'.scopes = e |+ (n, v)`, so `FDOM e ⊆ FDOM (e |+ (n, v))`
- `TL st'.scopes = es = TL st.scopes`

### Lemma: push_scope_then_pop_preserves

```sml
Theorem push_scope_then_pop_preserves:
  ∀body st res st'.
    (do push_scope; finally body pop_scope od) st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM st.scopes
```

## Proof Structure

### Main Theorem Proof

```sml
Theorem eval_stmts_preserves_scopes:
  ∀cx st st' ss res.
    eval_stmts cx ss st = (res, st') ⇒
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)
Proof
  (* Step 1: Set up mutual induction *)
  sg `(∀cx s st res st'. eval_stmt cx s st = (res, st') ⇒ P_stmt cx s st res st') ∧
      (∀cx ss st res st'. eval_stmts cx ss st = (res, st') ⇒ P_stmts cx ss st res st') ∧
      (∀cx it st res st'. eval_iterator cx it st = (res, st') ⇒ P_iter cx it st res st') ∧
      ... other predicates ...`
  
  (* Step 2: Apply evaluate_ind *)
  >- (ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
      (* For each case, either:
         - Apply existing theorem directly (Category 1)
         - Apply helper lemma (Categories 2-6) *)
      ...)
  
  (* Step 3: Extract main theorem from conjunction *)
  >> gvs[] >> metis_tac[]
QED
```

### Helper Lemma Proofs (to be done after main structure)

1. **case_AnnAssign**: Unfold definition, apply `eval_expr_preserves_scopes_dom`, then prove `new_variable_scope_property` case.

2. **case_If**: Apply `eval_expr_preserves_scopes_dom`, then use `push_scope_then_pop_preserves` with IH on body.

3. **case_For**: Apply `eval_iterator` preservation, then use IH on `eval_for`.

4. **case_eval_for_cons**: Use `push_scope_with_var` analysis + `finally_pop_scope_preserves_dom` + IH on tail.

5. **case_eval_stmts_cons**: Chain IH on statement and rest using ⊆ transitivity.

## Implementation Plan

### Phase 1: Create skeleton with cheated helpers
1. Define all helper lemmas with `cheat` proofs
2. Prove main theorem using the helper lemmas
3. Verify the main theorem builds

### Phase 2: Prove supporting lemmas
1. `new_variable_scope_property`
2. `finally_pop_scope_preserves_dom`
3. `push_scope_then_pop_preserves`

### Phase 3: Prove helper lemmas for each case
1. Category 1 cases (simple - use existing theorems)
2. `case_AnnAssign`
3. `case_If`
4. `case_For` and `case_eval_for_*`
5. `case_eval_stmts_cons`

### Phase 4: Remove cheats and verify full build

## Notes

- The proof follows a similar pattern to `scopes_len_mutual` in vyperScopesScript.sml
- Key difference: we track `FDOM` not just `LENGTH`, and HD can grow while TL is preserved
- Reusing `eval_expr_preserves_scopes_dom` and `eval_base_target_preserves_scopes_dom` is essential to avoid re-proving expression cases
