# TASK: Category 5-6 - eval_stmts and eval_for sequencing

## Goal

Replace cheats in `case_eval_stmts_cons_dom` and `case_eval_for_cons_dom`. These handle the sequencing/iteration patterns.

## Theorem Statements

```sml
Theorem case_eval_stmts_cons_dom:
  ∀cx s ss.
    (∀st res st'. eval_stmt cx s st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (∀st res st'. eval_stmts cx ss st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_stmts cx (s::ss) st = (res, st') ⇒ preserves_scopes_dom st st'

Theorem case_eval_for_cons_dom:
  ∀cx nm body v vs.
    (∀st res st'. eval_stmts cx body st = (res, st') ⇒ preserves_scopes_dom st st') ∧
    (∀st res st'. eval_for cx nm body vs st = (res, st') ⇒ preserves_scopes_dom st st') ⇒
    ∀st res st'.
      eval_for cx nm body (v::vs) st = (res, st') ⇒ preserves_scopes_dom st st'
```

## Location

- File: `vyperEvalStmtsPreservesScopesScript.sml`
- Lines: ~240-290
- Context: Sequencing and iteration cases

## Mathematical Argument

### case_eval_stmts_cons_dom

**WHY THIS IS TRUE:**

```sml
eval_stmts cx (s::ss) = do eval_stmt cx s; eval_stmts cx ss od
```

1. `eval_stmt cx s st = (res1, st1)` - by IH: `preserves_scopes_dom st st1`
2. `eval_stmts cx ss st1 = (res, st')` - by IH: `preserves_scopes_dom st1 st'`

From `preserves_scopes_dom st st1`:
- `FDOM (HD st.scopes) ⊆ FDOM (HD st1.scopes)`
- `MAP FDOM (TL st.scopes) = MAP FDOM (TL st1.scopes)`

From `preserves_scopes_dom st1 st'`:
- `FDOM (HD st1.scopes) ⊆ FDOM (HD st'.scopes)`
- `MAP FDOM (TL st1.scopes) = MAP FDOM (TL st'.scopes)`

Combined:
- `FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes)` (⊆ is transitive)
- `MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes)` (equality chains)

### case_eval_for_cons_dom

**WHY THIS IS TRUE:**

```sml
eval_for cx nm body (v::vs) = do
  push_scope_with_var nm v;
  broke <- finally
    (try (do eval_stmts cx body; return F od) handle_loop_exception)
    pop_scope;
  if broke then return () else eval_for cx nm body vs
od
```

1. `push_scope_with_var nm v st = ((), st1)`: HD st1 = FEMPTY |+ (nm,v), TL st1 = st.scopes
2. Body runs on st1. By IH: `preserves_scopes_dom st1 body_st'`
   - `FDOM (HD st1.scopes) ⊆ FDOM (HD body_st'.scopes)` (starts with singleton, can grow)
   - `MAP FDOM (TL st1.scopes) = MAP FDOM (TL body_st'.scopes) = MAP FDOM st.scopes`
3. `finally` with `pop_scope`: st2.scopes = TL body_st'.scopes
   - `MAP FDOM st2.scopes = MAP FDOM st.scopes`
4. If broke=T: st' = st2, so `MAP FDOM st'.scopes = MAP FDOM st.scopes`, done.
5. If broke=F: `eval_for cx nm body vs st2 = (res, st')` - by IH: `preserves_scopes_dom st2 st'`
   - Since `MAP FDOM st2.scopes = MAP FDOM st.scopes`:
     - `FDOM (HD st.scopes) = FDOM (HD st2.scopes) ⊆ FDOM (HD st'.scopes)`
     - `MAP FDOM (TL st.scopes) = MAP FDOM (TL st2.scopes) = MAP FDOM (TL st'.scopes)`

## Available Resources

### Definitions
- `evaluate_def` (for eval_stmts cons, eval_for cons)
- `preserves_scopes_dom_def`
- `finally_def`, `try_def`, `handle_loop_exception_def`
- `push_scope_with_var_def`, `pop_scope_def`

### Helper Lemmas
- `push_scope_with_var_creates_singleton_hd` (already proven)
- `finally_pop_scope_preserves_tl_dom` (to be proven)
- `SUBSET_TRANS` (for chaining ⊆)

## Proof Approach

### case_eval_stmts_cons_dom

```sml
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* Get preserves_scopes_dom from IH on s *)
  `preserves_scopes_dom st s''` by res_tac >>
  gvs[preserves_scopes_dom_def] >>
  (* Get preserves_scopes_dom from IH on ss *)
  `preserves_scopes_dom s'' st'` by res_tac >>
  gvs[preserves_scopes_dom_def] >>
  (* Chain the results *)
  conj_tac
  >- (irule SUBSET_TRANS >> qexists_tac `FDOM (HD s''.scopes)` >> simp[])
  >- simp[]
QED
```

### case_eval_for_cons_dom

This one is more complex due to the push/finally/pop pattern and the broke conditional.

```sml
Proof
  rpt strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  qpat_x_assum `eval_for _ _ _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* push_scope_with_var *)
  imp_res_tac push_scope_with_var_creates_singleton_hd >> gvs[] >>
  (* finally body pop_scope pattern - body preserves TL *)
  (* After pop: MAP FDOM st_after_pop.scopes = MAP FDOM st.scopes *)
  (* Case split on broke *)
  Cases_on `broke` >> gvs[return_def]
  >- (* broke = T: return () *)
     (... MAP FDOM unchanged, so preserves_scopes_dom ...)
  >- (* broke = F: recursive call *)
     (... apply IH on eval_for, chain with intermediate state ...)
QED
```

The key insight is that after push/finally/pop, we're back to the original scopes structure (MAP FDOM equality), so the recursive call's preserves_scopes_dom applies cleanly.

## Constraints

- Output must be valid HOL4 tactic proofs
- Must not introduce new cheats
- The eval_for case is complex - consider using helper lemmas for the push/finally/pop pattern

## Deliverable

Replace each `cheat` with complete proof. Return:
1. The proof tactics for both theorems
2. Any issues encountered
