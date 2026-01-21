# Proof Plan: scopes_len_preserved

## BUILD STATUS: ✓ PASSING (with 1 cheat)

The vyperScopesTheory now builds successfully. There is 1 remaining cheated theorem.

## Latest Update (Jan 21, 2026)

**case_eval_exprs_cons proof COMPLETED!** ✓
- Expression list evaluation with get_Value
- **Proof strategy:** Chain through state transformations:
  1. Strip quantifiers, expand evaluate_def/bind_def/AllCaseEqs/return_def
  2. Apply `imp_res_tac get_Value_scopes` to link intermediate states
  3. Apply `res_tac` to use the IH for eval_exprs
  4. Apply `first_x_assum (drule_then assume_tac)` to use the eval_expr IH
  5. Close with `gvs[]`
- Build now passes with **1 remaining cheat** (down from 2)

**Previously: case_eval_for_cons proof COMPLETED!** ✓
- Successfully proved case_eval_for_cons theorem for for loop iteration

## Current Status: 1 Remaining Cheat

The following theorem still has a cheat:

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

### ~~2. case_eval_exprs_cons~~ ✓ COMPLETED
Expression list evaluation with get_Value - **DONE**

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
