# Plan: Proving assign_target_spec_lookup

## Goal
```sml
Theorem assign_target_spec_lookup:
  !cx st n av v.
    lookup_name_target cx st n = SOME av ==>
    assign_target_spec cx st av (Replace v) (λst. lookup_name cx st n = SOME v)
```

## Key Definitions

### lookup_name_target (vyperHoareScript.sml:121-126)
```sml
lookup_name_target cx st n =
  case eval_base_target cx (NameTarget n) st of
  | (INL (loc, sbs), _) => SOME (BaseTargetV loc sbs)
  | (INR _, _) => NONE
```

### lookup_name (vyperHoareScript.sml:114-119)
```sml
lookup_name cx st n =
  case eval_expr cx (Name n) st of
  | (INL (Value v), _) => SOME v
  | (_, _) => NONE
```

### assign_target_spec (vyperHoareScript.sml:362-367)
```sml
assign_target_spec cx st av ao Q <=>
  case assign_target cx av ao st of
  | (INL _, st') => Q st'
  | (INR _, _) => F
```

### eval_base_target for NameTarget (vyperInterpreterScript.sml:2687-2699)
Returns `(ScopedVar n, [])` when variable is in scopes (non-creation mode)
or `(ImmutableVar n, [])` when variable is in immutables (creation mode)

### assign_target for ScopedVar (vyperInterpreterScript.sml:2026-2033)
```sml
assign_target cx (BaseTargetV (ScopedVar id) is) ao = do
  ni <<- string_to_num id;
  sc <- get_scopes;
  (pre, env, a, rest) <- lift_option (find_containing_scope ni sc) "...";
  a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
  set_scopes $ pre ++ env |+ (ni, a') :: rest;
  return $ Value a
od
```

### Key insight: assign_subscripts a [] (Replace v) = INL v
So for empty subscripts, the new value is just `v`.

## Proof Structure

The proof splits into cases based on:
1. `cx.txn.is_creation` (T or F)
2. Whether variable is in scopes or immutables

### Case 1: ScopedVar (variable in scopes)
When `eval_base_target` returns `(ScopedVar n, [])`:
- We have `IS_SOME (lookup_scopes (string_to_num n) st.scopes)`
- `assign_target` calls `find_containing_scope` which succeeds
- Scopes are updated to `pre ++ env |+ (string_to_num n, v) :: rest`
- Need to show `lookup_scopes (string_to_num n)` on new scopes returns `SOME v`

### Case 2: ImmutableVar (variable in immutables, creation mode only)
When `eval_base_target` returns `(ImmutableVar n, [])`:
- Variable is in immutables, not scopes
- `assign_target` updates immutables via `set_immutable`
- Need to show `eval_expr cx (Name n)` returns the new value from immutables

## Required Helper Lemmas

### Lemma 1: lookup_scopes_find_containing
```sml
!id sc. IS_SOME (lookup_scopes id sc) ==> IS_SOME (find_containing_scope id sc)
```
**Proof:** Induction on `sc`. Both functions traverse the scope list similarly.
- Base: Both return NONE for empty list
- Step: Case split on `FLOOKUP h id`. If SOME, both succeed. If NONE, use IH.

### Lemma 2: find_containing_scope_pre_none
```sml
!id sc pre env v rest. 
  find_containing_scope id sc = SOME (pre, env, v, rest) ==> 
  lookup_scopes id pre = NONE
```
**Proof:** Induction on `sc`.
- Base: `find_containing_scope id [] = NONE`, so premise is F
- Step: Case on `FLOOKUP h id`:
  - If `SOME v`: then `pre = []`, so `lookup_scopes id [] = NONE`
  - If `NONE`: then `pre = h :: pre'` where `find_containing_scope id sc = SOME (pre', ...)`.
    By IH, `lookup_scopes id pre' = NONE`. 
    Since `FLOOKUP h id = NONE`, `lookup_scopes id (h::pre') = lookup_scopes id pre' = NONE`.

### Lemma 3: lookup_scopes_update
```sml
!id pre env v rest.
  lookup_scopes id pre = NONE ==>
  lookup_scopes id (pre ++ env |+ (id, v) :: rest) = SOME v
```
**Proof:** Induction on `pre`.
- Base: `lookup_scopes id (env |+ (id,v) :: rest) = SOME v` by FLOOKUP_UPDATE
- Step: If `FLOOKUP h id = NONE` (from lookup_scopes pre = NONE), use IH.

### Lemma 4: eval_expr_Name_after_set_scopes
```sml
!cx st n v pre env rest.
  find_containing_scope (string_to_num n) st.scopes = SOME (pre, env, _, rest) ==>
  eval_expr cx (Name n) (st with scopes := pre ++ env |+ (string_to_num n, v) :: rest) =
  (INL (Value v), st with scopes := pre ++ env |+ (string_to_num n, v) :: rest)
```
**Proof:** 
- Expand eval_expr for Name
- Use Lemmas 2 and 3 to show lookup_scopes returns SOME v
- Handle exactly_one_option: scopes has value, so it's used

### Lemma 5: get_immutables_preserves_state
```sml
!cx st imms st'. get_immutables cx st = (INL imms, st') ==> st' = st
```
**Proof:** Unfold definitions, all operations are reads.

### Lemma 6 (for ImmutableVar case): eval_expr_Name_after_set_immutable
```sml
!cx st n v.
  ~IS_SOME (lookup_scopes (string_to_num n) st.scopes) /\
  IS_SOME (FLOOKUP imms (string_to_num n)) ==>
  ... (similar for immutables case)
```

## Proof Outline

```sml
Theorem assign_target_spec_lookup:
Proof
  rw[lookup_name_target_def, assign_target_spec_def, lookup_name_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  (* Now have: eval_base_target cx (NameTarget n) st = (INL (loc, sbs), _) *)
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >> gvs[return_def, lift_sum_def] >|
  [
    (* is_creation = T *)
    simp[get_immutables_def, ...] >>
    Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def] >>
    simp[immutable_target_def] >>
    Cases_on `IS_SOME (lookup_scopes ...)` >>
    Cases_on `FLOOKUP ... immutables ...` >>
    gvs[exactly_one_option_def, return_def, raise_def] >|
    [
      (* ScopedVar case *)
      strip_tac >> gvs[] >>
      simp[Once assign_target_def, ...] >>
      `IS_SOME (find_containing_scope ...)` by metis_tac[lookup_scopes_find_containing] >>
      Cases_on `find_containing_scope ...` >> gvs[] >>
      (* Destructure tuple *) >>
      simp[assign_subscripts_def, return_def, set_scopes_def, ...] >>
      (* Now show eval_expr returns v *)
      simp[Once evaluate_def, ...] >>
      `lookup_scopes ... (pre ++ env |+ ... :: rest) = SOME v` 
        by metis_tac[find_containing_scope_pre_none, lookup_scopes_update] >>
      simp[exactly_one_option_def, return_def]
      ,
      (* ImmutableVar case *)
      ... (similar structure for immutables)
    ]
    ,
    (* is_creation = F, only ScopedVar possible *)
    ... (similar to ScopedVar case above)
  ]
QED
```

## Status: COMPLETED

The proof of `assign_target_spec_lookup` is complete.

### Changes Made

1. Added two preconditions to the theorem (required for correctness):
   - `IS_SOME (ALOOKUP st.globals cx.txn.target)` - ensures globals are present for lookup_name
   - `IS_SOME (lookup_name cx st n)` - ensures exactly one of scopes/immutables has the variable

2. Proved three helper lemmas:
   - `lookup_scopes_find_containing`: `IS_SOME lookup_scopes ==> IS_SOME find_containing_scope`
   - `find_containing_scope_pre_none`: find_containing_scope returns pre where lookup_scopes is NONE
   - `lookup_scopes_update`: After updating scopes with new value, lookup returns that value

3. The main proof handles three cases:
   - `is_creation = T`, variable in scopes (ScopedVar)
   - `is_creation = T`, variable in immutables (ImmutableVar)
   - `is_creation = F` (only ScopedVar possible)

### Remaining Cheat

The file still has a cheat for `stmts_spec_assign_name` (line 521), which is a separate theorem.
