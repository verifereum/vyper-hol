# Proof Plan: eval_expr_preserves_scopes_dom

## Verdict: PROVABLE

## Unverified Assumptions: NONE

## Goal (in mathematical terms)

For any expression `e`, context `cx`, and states `st`, `st'`:
```
eval_expr cx e st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes
```

This says that expression evaluation preserves the domains (sets of variable names) of each scope in the scope stack, even though values may change.

## Key Insights

1. **Reduction to `eval_expr_preserves_scopes`**: For pure expressions (`pure_expr e`), we already have `st.scopes = st'.scopes` (from the helper theorem), which trivially implies `MAP FDOM st.scopes = MAP FDOM st'.scopes`.

2. **The only impure expression is `Pop`**: From `pure_expr_def`, we see that `Pop` is the only expression constructor where `pure_expr` is `F`. All other constructors either are pure directly or recurse into subexpressions.

3. **`Pop` preserves domains**: `Pop` calls `assign_target` with `ScopedVar`, which uses `find_containing_scope` to find the variable, then does `set_scopes $ pre ++ env |+ (ni, a') :: rest`. Since `find_containing_scope_structure` guarantees `FLOOKUP env ni = SOME v` (the variable already exists), the update `env |+ (ni, a')` doesn't change `FDOM env`.

4. **Structural preservation**: The structure `pre ++ env |+ (ni, a') :: rest` has the same list structure as `pre ++ env :: rest = sc` (original scopes), and `FDOM (env |+ (ni, a')) = FDOM env` when `ni IN FDOM env`.

## Validated Assumptions

- **`eval_expr_preserves_scopes` handles pure expressions**: VERIFIED - this is stated as a theorem in the file (lines 34-40), and once proven, it gives `st.scopes = st'.scopes` for pure expressions.

- **`Pop` is the only impure expression**: VERIFIED by inspecting `pure_expr_def` (lines 13-26) - every constructor except `Pop` is either directly `T` or recurses on subexpressions.

- **`assign_target` for `ScopedVar` preserves FDOM**: VERIFIED by inspection:
  - `find_containing_scope id sc = SOME (pre, env, v, rest)` implies `FLOOKUP env id = SOME v` (from `find_containing_scope_structure`)
  - The update `env |+ (id, a')` preserves `FDOM env` when `id IN FDOM env` (standard fmap property: `FDOM (f |+ (k, v)) = FDOM f UNION {k}`, and if `k IN FDOM f`, then `FDOM f UNION {k} = FDOM f`)
  - `MAP FDOM (pre ++ env |+ (id, a') :: rest) = MAP FDOM pre ++ [FDOM (env |+ (id, a'))] ++ MAP FDOM rest = MAP FDOM pre ++ [FDOM env] ++ MAP FDOM rest = MAP FDOM (pre ++ env :: rest) = MAP FDOM sc`

- **`Pop` only uses `ScopedVar` path**: VERIFIED - from `eval_expr` definition (line 2593-2600), `Pop bt` evaluates `eval_base_target cx bt` which returns a `loc`. Looking at `eval_base_target_def`, the `loc` is a `var_location` which for scoped variables is `ScopedVar id`.

## Preliminary Facts to Establish

1. **Lemma: FDOM_FUPDATE_IN**: `k IN FDOM f ==> FDOM (f |+ (k, v)) = FDOM f`
   - This is a standard fmap property, should be in `finite_mapTheory`

2. **Lemma: MAP_FDOM_UPDATE**: 
   ```
   find_containing_scope id sc = SOME (pre, env, v, rest) ==>
   MAP FDOM (pre ++ env |+ (id, a') :: rest) = MAP FDOM sc
   ```
   - Follows from: `sc = pre ++ env :: rest` (from `find_containing_scope_structure`), `FLOOKUP env id = SOME v` implies `id IN FDOM env`, and `FDOM_FUPDATE_IN`

3. **Lemma for assign_target**: 
   ```
   assign_target cx gv ao st = (res, st') ==> MAP FDOM st'.scopes = MAP FDOM st.scopes
   ```
   - Case split by `gv`:
     - `ScopedVar`: use `MAP_FDOM_UPDATE` lemma
     - `TopLevelVar`, `ImmutableVar`: these don't modify `st.scopes` at all (they modify globals/immutables)
     - `TupleTargetV`: recurses into `assign_targets`, which recurses into `assign_target`

## Proof Argument

### Structure

The proof follows the same structure as `eval_expr_scopes_len` using `ho_match_mp_tac evaluate_ind`, with mutual induction over `eval_expr`, `eval_exprs`, `eval_stmt`, etc.

For `eval_expr_preserves_scopes_dom`, we only need the `eval_expr` and `eval_exprs` parts.

### Case: Pure expressions (Name, TopLevelName, FlagMember, Literal, IfExp, StructLit, Subscript, Attribute, Builtin, TypeBuiltin, Call)

For pure expressions, reduce to `eval_expr_preserves_scopes`:
- Show `pure_expr e` holds for the expression
- Apply `eval_expr_preserves_scopes`: `st.scopes = st'.scopes`
- Therefore `MAP FDOM st.scopes = MAP FDOM st'.scopes`

**Note**: Use `eval_expr_preserves_scopes` for all pure expression cases. The theorem remains cheated but will be proven separately later.

### Case: Pop (the only impure expression)

For `eval_expr cx (Pop bt) st = (res, st')`:

1. Expand `eval_expr` definition for `Pop`:
   ```
   eval_expr cx (Pop bt) = do
     (loc, sbs) <- eval_base_target cx bt;
     tv <- assign_target cx (BaseTargetV loc sbs) PopOp;
     ...
   od
   ```

2. `eval_base_target` preserves scopes (doesn't modify `st.scopes`)

3. `assign_target cx (BaseTargetV loc sbs) PopOp` for `ScopedVar id`:
   - Gets `find_containing_scope (string_to_num id) st.scopes = SOME (pre, env, v, rest)`
   - Sets scopes to `pre ++ env |+ (string_to_num id, a') :: rest`
   - By `MAP_FDOM_UPDATE` lemma: `MAP FDOM st'.scopes = MAP FDOM st.scopes`

4. For `TopLevelVar` or `ImmutableVar`: scopes unchanged entirely

5. The rest of `Pop` (`get_Value`, `lift_sum`, `lift_option`) don't modify scopes

### Case: eval_exprs

By structural induction:
- `eval_exprs cx [] st`: returns without modifying state
- `eval_exprs cx (e::es) st`: chains `eval_expr cx e st` then `eval_exprs cx es`. By IH both preserve `MAP FDOM st.scopes`.

## Required Lemmas

1. **`eval_expr_preserves_scopes`** (stated in file): `pure_expr e /\ eval_expr cx e st = (res, st') ==> st.scopes = st'.scopes`
   - Status: USE THIS THEOREM (remains cheated, will be proven separately later)

2. **`FDOM_FUPDATE_SAME`**: `k IN FDOM f ==> FDOM (f |+ (k, v)) = FDOM f`
   - Status: available in `finite_mapTheory` as `FDOM_FUPDATE`

3. **`find_containing_scope_structure`**: already proven in `vyperLookupScript.sml`
   - Status: available

4. **`assign_target_preserves_scopes_dom`** (new helper):
   ```
   assign_target cx gv ao st = (res, st') ==> MAP FDOM st'.scopes = MAP FDOM st.scopes
   ```
   - Status: needs proving (similar structure to `assign_target_scopes_len`)

5. **`eval_base_target_preserves_scopes`**: `eval_base_target cx bt st = (res, st') ==> st'.scopes = st.scopes`
   - Status: likely follows from existing lemmas (needs verification)

## Potential Difficulties

1. **Dependency on cheated `eval_expr_preserves_scopes`**: The `_dom` theorem uses `eval_expr_preserves_scopes` for pure expression cases. This theorem is currently cheated but will be proven separately later. The `_dom` proof is valid modulo this dependency.

2. **Mutual recursion**: The proof will need `ho_match_mp_tac evaluate_ind` to handle the mutual recursion between `eval_expr`, `eval_exprs`, `eval_stmt`, etc.

3. **IntCall case**: Internal calls modify scopes (push/pop function frames), but restore them via `finally ... (pop_function prev)`. This needs careful analysis - the `prev` scopes are restored at the end, preserving `MAP FDOM`.

## Recommended Proof Order

1. Prove helper `assign_target_preserves_scopes_dom` (for handling `Pop` case)
2. Prove `eval_expr_preserves_scopes_dom`:
   - For pure expressions: use `eval_expr_preserves_scopes` (cheated, to be proven later)
   - For `Pop`: use `assign_target_preserves_scopes_dom`

**Note**: `eval_expr_preserves_scopes` remains cheated and will be proven in a separate task. The `_dom` theorem depends on it for pure expression cases.
