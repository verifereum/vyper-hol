# TASK: Infrastructure Lemmas - Core scope operation properties

## Goal

Replace cheats in the core infrastructure lemmas that establish foundational facts about scope-modifying operations:
1. `new_variable_scope_property`
2. `finally_pop_scope_preserves_tl_dom`
3. `push_scope_finally_pop_preserves_dom`

## Theorem Statements

```sml
Theorem new_variable_scope_property:
  ∀id v st res st'.
    new_variable id v st = (res, st') ∧ st.scopes ≠ [] ⇒
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    TL st'.scopes = TL st.scopes

Theorem finally_pop_scope_preserves_tl_dom:
  ∀body st res st'.
    finally body pop_scope st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM (TL st.scopes)

Theorem push_scope_finally_pop_preserves_dom:
  ∀body st res st'.
    do push_scope; finally body pop_scope od st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       FDOM (HD st1.scopes) ⊆ FDOM (HD st1'.scopes) ∧
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM st.scopes
```

## Location

- File: `vyperEvalStmtsPreservesScopesScript.sml`
- Lines: ~30-90
- Context: These are core helper lemmas used by the If/For cases

## Mathematical Argument

### new_variable_scope_property

**WHY THIS IS TRUE:**
`new_variable_def` does: `set_scopes ((e |+ (n, v))::es)` where `e::es = st.scopes`
- HD st'.scopes = e |+ (n, v), so FDOM e ⊆ FDOM (e |+ (n,v)) (adding a key)
- TL st'.scopes = es = TL st.scopes (unchanged)

### finally_pop_scope_preserves_tl_dom

**WHY THIS IS TRUE:**
`finally` runs body, then unconditionally runs pop_scope (on success or failure).
`pop_scope` sets scopes to `TL body_st'.scopes`.
If body preserved TL (MAP FDOM equality), then:
`MAP FDOM st'.scopes = MAP FDOM (TL body_st'.scopes) = MAP FDOM (TL st.scopes)`

### push_scope_finally_pop_preserves_dom

**WHY THIS IS TRUE:**
1. push_scope: HD' = FEMPTY, TL' = st.scopes
2. body runs on pushed state. By hypothesis: MAP FDOM (TL body_st'.scopes) = MAP FDOM (TL pushed_st.scopes) = MAP FDOM st.scopes
3. pop_scope: st'.scopes = TL body_st'.scopes
4. Therefore: MAP FDOM st'.scopes = MAP FDOM st.scopes

## Available Resources

### Definitions
- `new_variable_def`: Creates new variable in HD scope
- `finally_def`: Run action, then cleanup (always)
- `pop_scope_def`: Sets scopes to TL
- `push_scope_def`: Prepends FEMPTY to scopes
- `set_scopes_def`: Replaces scopes

### Helper Lemmas
- `push_scope_creates_empty_hd` (already proven)
- `push_scope_with_var_creates_singleton_hd` (already proven)

## Proof Approach

### new_variable_scope_property
1. Unfold `new_variable_def`
2. Case split on `st.scopes = e::es`
3. After `set_scopes ((e |+ (n, v))::es)`:
   - HD is `e |+ (n, v)`, so `FDOM e ⊆ FDOM (e |+ (n, v))` by FDOM_FUPDATE
   - TL is `es`

### finally_pop_scope_preserves_tl_dom
1. Unfold `finally_def`, `pop_scope_def`
2. Case split on body result (INL success, INR exception)
3. In both cases, pop_scope runs and sets scopes to TL of body's final state
4. Apply hypothesis to chain MAP FDOM equality

### push_scope_finally_pop_preserves_dom
1. Unfold do-notation (bind_def)
2. push_scope creates state with `FEMPTY :: st.scopes`
3. Apply finally_pop_scope_preserves_tl_dom pattern
4. After pop: scopes = TL of pushed body result = original st.scopes (in MAP FDOM terms)

## Constraints

- Output must be valid HOL4 tactic proofs
- Must not introduce new cheats
- Key definitions: `finally_def`, `pop_scope_def`, `push_scope_def`, `set_scopes_def`, `new_variable_def`

## Deliverable

Replace each `cheat` with a complete proof. Return:
1. The proof tactics for each theorem
2. Any issues encountered
