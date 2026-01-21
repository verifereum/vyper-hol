# Proof Plan: scopes_len_preserved

## BUILD STATUS: ✓ PASSING (with 2 cheats)

The vyperScopesTheory now builds successfully. There are 2 remaining cheated theorems.

## Latest Update (Jan 21, 2026)

**case_eval_for_cons proof COMPLETED!** ✓
- Successfully proved case_eval_for_cons theorem for for loop iteration
- **Proof strategy:** Expand the definition, case split on success/failure of each operation:
  1. Use `push_scope_with_var_len` to establish scopes length after push (+1)
  2. Expand `finally` and `try`/`handle_loop_exception` to track state through success/error paths
  3. Apply `eval_stmts` IH to show body preserves scopes length
  4. Expand `pop_scope` to show it subtracts 1 from scopes length
  5. For `broke = F` (ContinueException), use IH for recursive `eval_for` call
  6. For `broke = T` (BreakException), show `return ()` preserves scopes
  7. Handle error propagation cases by showing state is preserved
- Build now passes with **2 remaining cheats** (down from 3)

## Current Status: 2 Remaining Cheats

The following theorems still have cheats:

### 1. case_IntCall (line 994)
Internal function calls with push_function/finally/pop_function pattern.

```sml
Theorem case_IntCall[local]:
  ∀cx src_id_opt fn es.
    (∀s'' ... (* many conditional premises *) ...
       ∀st res st'. eval_stmts cxf body' st = (res,st') ⇒ 
         LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀s'' ... (* many conditional premises *) ...
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒ 
         LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call (IntCall (src_id_opt,fn)) es) st = (res,st') ⇒
      LENGTH st.scopes = LENGTH st'.scopes
```

**Proof strategy:**
This is the most complex case:
1. Definition involves: check, lift_option (multiple), get_scopes, push_function, finally, pop_function
2. Use `get_scopes_id` to establish `prev = st.scopes`
3. `push_function` sets scopes to `[env]`
4. Body (eval_stmts) preserves LENGTH (by IH on scopes = [env])
5. `pop_function prev` restores `prev = st.scopes`
6. Chain through the state transformations

Key helper lemmas available:
- `push_function_scopes`: `push_function ... st = (INL cxf, st') ⇒ st'.scopes = [sc]`
- `pop_function_scopes`: `pop_function prev st = (res, st') ⇒ st'.scopes = prev`
- `get_scopes_id`: `get_scopes st = (res, st') ⇒ st' = st`

### 2. case_eval_exprs_cons (line 1015)
Expression list evaluation with get_Value.

```sml
Theorem case_eval_exprs_cons[local]:
  ∀cx e es.
    (∀s'' tv t s'³' v t'.
       eval_expr cx e s'' = (INL tv,t) ∧ get_Value tv s'³' = (INL v,t') ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒ 
         LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'. eval_expr cx e st = (res,st') ⇒ 
       LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_exprs cx (e::es) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
```

**Proof strategy:**
- Definition: `do tv <- eval_expr cx e; v <- get_Value tv; vs <- eval_exprs cx es; return (v::vs) od`
- State chain: `st → t (eval e) → t' (get_Value) → st' (eval es)`
- Apply eval_expr IH to get `LENGTH st.scopes = LENGTH t.scopes`
- Apply `get_Value_scopes` to get `LENGTH t.scopes = LENGTH t'.scopes`
- Apply eval_exprs IH (conditional) to get `LENGTH t'.scopes = LENGTH st'.scopes`
- Chain by transitivity

**Suggested proof:**
```sml
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  res_tac >> gvs[]
QED
```
(May need careful IH instantiation if res_tac doesn't find it automatically)

## Completed Theorems

All other case_* theorems are complete:
- case_Pass, case_Continue, case_Break, case_Return_none, case_Return_some
- case_Raise, case_Assert, case_Log, case_AnnAssign, case_Append
- case_Assign, case_AugAssign, case_If, case_For ✓ (just fixed!)
- case_Expr, case_eval_stmts_nil, case_eval_stmts_cons
- case_Array_iterator, case_Range_iterator
- case_BaseTarget, case_TupleTarget, case_eval_targets_nil, case_eval_targets_cons
- case_NameTarget, case_TopLevelNameTarget, case_AttributeTarget, case_SubscriptTarget
- case_eval_for_nil
- case_Name, case_TopLevelName, case_FlagMember, case_IfExp, case_Literal
- case_StructLit, case_Subscript, case_Attribute
- case_Builtin, case_Pop, case_TypeBuiltin, case_Send, case_ExtCall
- case_eval_exprs_nil

## Main Theorem Structure

The `scopes_len_mutual` theorem (line 964+) assembles all case_* theorems using `ho_match_mp_tac evaluate_ind` and `ACCEPT_TAC case_*` for each of the 45 subgoals.

Once all 3 remaining cheats are fixed:
1. Build should pass with 0 cheats
2. The final `scopes_len_preserved` theorem derives from `scopes_len_mutual`

## Priority Order for Remaining Work

1. **case_eval_exprs_cons** - Likely simplest, standard IH chaining pattern
2. **case_eval_for_cons** - Medium difficulty, uses finally_push_var_pop_len  
3. **case_IntCall** - Most complex, many state transformations to track

## Helper Lemmas Available

All helper lemmas are proven (lines 9-228 in vyperScopesScript.sml):
- `return_scopes`, `raise_scopes`, `check_scopes`
- `lift_option_scopes`, `lift_sum_scopes`
- `get_Value_scopes`, `get_scopes_id`
- `get_accounts_scopes`, `get_current_globals_scopes`, `set_current_globals_scopes`
- `get_immutables_scopes`, `lookup_global_scopes`, `set_global_scopes`, `set_immutable_scopes`
- `push_log_scopes`, `transfer_value_scopes`
- `push_scope_len`, `push_scope_with_var_len`, `pop_scope_len`, `set_scopes_len`
- `find_containing_scope_len`
- `new_variable_scopes_len`, `set_variable_scopes_len`
- `push_function_scopes`, `pop_function_scopes`
- `bind_scopes_len`, `finally_push_pop_len`, `finally_push_var_pop_len`
- `switch_BoolV_scopes_len`
- `assign_target_scopes_len`

## Goal

```sml
Theorem scopes_len_preserved:
  !st res s st'.
    eval_stmts cx ss st = (res, st') ==>
    length st.scopes = length st'.scopes
```

Prove that executing statements preserves the length of the scopes list.
