# Plan: CV-Translation for vyper_to_abi and evaluate_abi_encode

## Current State

The file `semantics/vyperABIScript.sml` contains:
- `vyper_to_abi` (lines 161-249): Converts Vyper values to ABI values for encoding
- `evaluate_abi_encode` (lines 699-705): Top-level function for ABI encoding
- `default_to_abi` (lines 141-158): Helper for sparse array encoding

Currently, only `abi_to_vyper` has cv-translation (via `cv_auto_trans_pre`), but `vyper_to_abi` and `evaluate_abi_encode` do not. The build is failing at `vyperInterpreterTheory` because `evaluate_type_builtin` calls `evaluate_abi_encode`, which depends on `vyper_to_abi`.

## Dependencies

The cv-translation dependency chain is:
1. `default_to_abi` - used by `vyper_to_abi_sparse`
2. `vyper_to_abi` / `vyper_to_abi_list` / `vyper_to_abi_same` / `vyper_to_abi_sparse` - mutually recursive
3. `evaluate_abi_encode` - depends on `vyper_to_abi`

## Issues and Solutions

### Issue 1: Mutual Recursion in vyper_to_abi

`vyper_to_abi` has 4 mutually recursive functions:
- `vyper_to_abi env t v`
- `vyper_to_abi_list env ts vs`
- `vyper_to_abi_same env t vs`
- `vyper_to_abi_sparse env t tv n sparse`

**Solution**: Use `cv_auto_trans_rec` with a custom termination argument based on `cv_size`, similar to:
```sml
val () = cv_auto_trans_rec vyper_to_abi_def (
  WF_REL_TAC `measure (λx. case x of
    | INL (_, _, v) => cv_size v
    | INR (INL (_, _, vs)) => cv_size vs
    | INR (INR (INL (_, _, vs))) => cv_size vs
    | INR (INR (INR (_, _, _, n, sparse))) => cv_size sparse + cv$c2n n)`
  \\ ... (* tactics to prove measure decreases *)
);
```

### Issue 2: Num Function in UintT Case

The definition uses `Num i` to convert integer to natural:
```sml
vyper_to_abi env (BaseT (UintT _)) (IntV (Unsigned _) i) = SOME (NumV (Num i))
```

`Num` is already cv-translated (in `cv_stdTheory`), so this should work. However, if there are issues, we could rewrite using `INT_NUM` or `ABS`:
```sml
(* Alternative if Num causes issues *)
vyper_to_abi env (BaseT (UintT _)) (IntV (Unsigned _) i) = 
  SOME (NumV (if 0 ≤ i then Num i else 0))
```

### Issue 3: default_to_abi Has No CV-Translation

`default_to_abi` uses `MAP` on recursive calls:
```sml
default_to_abi (TupleTV tvs) = ListV (MAP default_to_abi tvs)
```

**Solution**: Use `cv_auto_trans` (or `cv_trans` if non-recursive measure works):
```sml
val () = cv_auto_trans default_to_abi_def;
```

If `MAP` causes issues, we may need to define a helper `default_to_abi_list`.

### Issue 4: ALOOKUP in vyper_to_abi_sparse

The sparse case uses `ALOOKUP sparse n` which should already be cv-translated.

### Issue 5: Pre-conditions

Similar to `abi_to_vyper`, we may need `cv_auto_trans_pre` if there are preconditions (e.g., for `word_of_bytes` in AddressT case).

**Pattern from abi_to_vyper:**
```sml
val abi_to_vyper_pre_def =
  abi_to_vyper_def
  |> REWRITE_RULE[GSYM CHR_o_w2n_eq]
  |> cv_auto_trans_pre "abi_to_vyper_pre abi_to_vyper_list_pre";

Theorem abi_to_vyper_pre[cv_pre]:
  (!v1 v0 v. abi_to_vyper_pre v1 v0 v) ∧
  (!v1 v0 v. abi_to_vyper_list_pre v1 v0 v)
Proof
  ho_match_mp_tac abi_to_vyper_ind
  \\ rw[]
  \\ rw[Once abi_to_vyper_pre_def]
QED
```

## Implementation Steps

### Step 1: Add cv_auto_trans for default_to_abi

Add after line 158:
```sml
val () = cv_auto_trans default_to_abi_def;
```

If this fails due to `MAP`, define a helper:
```sml
Definition default_to_abi_list_def:
  default_to_abi_list [] = [] ∧
  default_to_abi_list (tv::tvs) = default_to_abi tv :: default_to_abi_list tvs
End
```

### Step 2: Add cv_auto_trans_rec for vyper_to_abi

Add after line 249 (after the definition):
```sml
val vyper_to_abi_pre_def = cv_auto_trans_pre_rec
  "vyper_to_abi_pre vyper_to_abi_list_pre vyper_to_abi_same_pre vyper_to_abi_sparse_pre"
  vyper_to_abi_def (
  WF_REL_TAC `measure (λx. case x of
    | INL (_, _, v) => cv_size v
    | INR (INL (_, _, vs)) => cv_size vs
    | INR (INR (INL (_, _, vs))) => cv_size vs
    | INR (INR (INR (_, _, _, n, sparse))) => cv_size sparse + cv$c2n n)`
  \\ rw[]
  \\ TRY (Cases_on `cv_v` \\ gvs[cvTheory.cv_size_def] \\ NO_TAC)
  (* Additional tactics for specific cases *)
);

Theorem vyper_to_abi_pre[cv_pre]:
  (∀env t v. vyper_to_abi_pre env t v) ∧
  (∀env ts vs. vyper_to_abi_list_pre env ts vs) ∧
  (∀env t vs. vyper_to_abi_same_pre env t vs) ∧
  (∀env t tv n sparse. vyper_to_abi_sparse_pre env t tv n sparse)
Proof
  ho_match_mp_tac vyper_to_abi_ind
  \\ rw[]
  \\ rw[Once vyper_to_abi_pre_def]
QED
```

### Step 3: Add cv_auto_trans for evaluate_abi_encode

Add after line 705:
```sml
val () = cv_auto_trans evaluate_abi_encode_def;
```

## Testing Strategy

1. Run `Holmake` in `semantics/` to verify vyperABITheory builds
2. Run `Holmake` in parent directory to verify vyperInterpreterTheory builds
3. Test with `cv_eval` on sample cases:
```sml
cv_eval ``vyper_to_abi FEMPTY (BaseT (UintT 256)) (IntV (Unsigned 256) 42)``;
cv_eval ``evaluate_abi_encode FEMPTY (BaseT (UintT 256)) (IntV (Unsigned 256) 42)``;
```

## Potential Complications

1. **Termination proof for cv_auto_trans_rec**: The 4-way mutual recursion with sparse arrays is complex. May need careful case analysis.

2. **Pre-conditions**: `word_of_bytes` in AddressT case may generate preconditions that need to be discharged.

3. **MAP in default_to_abi**: If cv_trans cannot handle MAP directly, need to define explicit list traversal.

4. **REPLICATE in default_to_abi**: Used in `BytesT (Fixed n)` and `ArrayTV tv (Fixed n)` cases.

5. **FlagV uses num not int**: `FlagV _ n` where `n:num` - should be fine for cv-translation.

## Order of Changes

1. First add `cv_auto_trans default_to_abi_def;` (after line 158)
2. Then add `cv_auto_trans_rec` or `cv_auto_trans_pre_rec` for `vyper_to_abi` (after line 249)
3. Finally add `cv_auto_trans evaluate_abi_encode_def;` (after line 705)

## Notes

- Never modify definition semantics - only syntactic rewrites if needed
- Reference `abi_to_vyper_pre` pattern for precondition handling
- Reference `vyper_to_abi_type` cv_auto_trans_rec for termination pattern
- Reference `safe_cast_pre_def` in vyperInterpreterScript.sml for cv_auto_trans_pre_rec pattern

## Success Criteria

- `Holmake` in `semantics/` builds successfully
- `vyperInterpreterTheory` builds without the "nonstdform" error
- `cv_eval` works on sample inputs for `vyper_to_abi` and `evaluate_abi_encode`

## Detailed Termination Proof Strategy

The original termination measure for `vyper_to_abi` is:
```sml
WF_REL_TAC `measure (λx. case x of
  | INL (_, _, v) => value_size v
  | INR (INL (_, _, vs)) => list_size value_size vs
  | INR (INR (INL (_, _, vs))) => list_size value_size vs
  | INR (INR (INR (_, _, _, n, sparse))) =>
      list_size (pair_size (λx. 0) value_size) sparse + n)`
```

For cv-translation, we need an equivalent measure using `cv_size`. The key insight is:
- `cv_size` on a cv-value corresponds to `value_size` after translation
- For the sparse case, we need `cv_size sparse + cv$c2n n` instead of size + n

Reference patterns from existing code:
1. `vyper_to_abi_type` (line 42-50) shows how to handle recursive types
2. `safe_cast_pre_def` (line 810-857 of vyperInterpreterScript.sml) shows complex cv_size reasoning

Specific tactics needed:
```sml
(* For main value case *)
\\ TRY (Cases_on `cv_v` \\ gvs[cvTheory.cv_size_def] \\ NO_TAC)
(* For pairs/tuples *)
\\ qmatch_goalsub_rename_tac `cv_snd p`
\\ Cases_on `p` \\ gvs[cvTheory.cv_size_def]
(* For the sparse array n argument - decreasing SUC n to n *)
\\ Cases_on `cv_v` \\ gvs[cv_lt_Num_0]
```

## Alternative Approach: Simplify vyper_to_abi_sparse

If the 4-way mutual recursion proves too complex, an alternative is to factor out `vyper_to_abi_sparse` as a separate definition that builds a list directly:

```sml
(* Factor out sparse encoding *)
Definition vyper_to_abi_sparse_aux_def:
  vyper_to_abi_sparse_aux conv_fn default_fn 0 sparse = SOME [] ∧
  vyper_to_abi_sparse_aux conv_fn default_fn (SUC n) sparse =
    (case vyper_to_abi_sparse_aux conv_fn default_fn n sparse of
     | NONE => NONE
     | SOME avs =>
         case ALOOKUP sparse n of
         | SOME v => (case conv_fn v of SOME av => SOME (avs ++ [av]) | NONE => NONE)
         | NONE => SOME (avs ++ [default_fn]))
End
```

This would allow `vyper_to_abi_sparse` to be defined as:
```sml
vyper_to_abi_sparse env t tv n sparse =
  vyper_to_abi_sparse_aux (vyper_to_abi env t) (default_to_abi tv) n sparse
```

However, this changes the mutual recursion structure and may require adjusting existing proofs.

## Files to Modify

1. **semantics/vyperABIScript.sml** - Add cv_auto_trans calls
2. No other files should need modification

## Reference: Existing CV-Translation Patterns in Codebase

- `vyper_base_to_abi_type_def` (line 41): Simple cv_auto_trans
- `vyper_to_abi_type_def` (lines 42-50): cv_auto_trans_rec with cv_size termination
- `abi_to_vyper_def` (lines 107-119): cv_auto_trans_pre with CHR_o_w2n rewrite
- `evaluate_binop` (lines 421-429): cv_auto_trans_rec with custom cv values
- `safe_cast` (lines 810-865): cv_auto_trans_pre_rec with complex cv_size reasoning

## Potential Definition Rewrites (Semantics-Preserving)

### Issue: Composition in default_to_abi

The definition uses:
```sml
default_to_abi (StructTV fields) = ListV (MAP (default_to_abi o SND) fields)
```

The `o` (function composition) may need to be expanded for cv-translation:
```sml
default_to_abi (StructTV fields) = ListV (MAP (λ(id,tv). default_to_abi tv) fields)
```

Or using an auxiliary definition:
```sml
Definition default_to_abi_fields_def:
  default_to_abi_fields [] = [] ∧
  default_to_abi_fields ((id,tv)::rest) = 
    default_to_abi tv :: default_to_abi_fields rest
End
```

### Issue: n2w o ORD in vyper_to_abi

The definition uses:
```sml
vyper_to_abi env (BaseT (StringT _)) (StringV _ s) = SOME (BytesV (MAP (n2w o ORD) s))
```

This may need the existing `n2w_o_ORD` helper from vyperMiscScript.sml (line 36), which is already cv-translated.

If needed, rewrite using:
```sml
|> REWRITE_RULE[GSYM n2w_o_ORD_eq]
```

### Pattern from abi_to_vyper

The `abi_to_vyper` definition has:
```sml
(MAP (CHR o w2n) bs)
```

Which is rewritten to use `CHR_o_w2n_eq`:
```sml
val abi_to_vyper_pre_def =
  abi_to_vyper_def
  |> REWRITE_RULE[GSYM CHR_o_w2n_eq]
  |> cv_auto_trans_pre ...
```

We may need similar treatment for `n2w o ORD` in vyper_to_abi:
```sml
val vyper_to_abi_pre_def =
  vyper_to_abi_def
  |> REWRITE_RULE[GSYM n2w_o_ORD_eq]
  |> cv_auto_trans_pre_rec ...
```

## Summary of Required Code Changes

### Add after line 158 (after default_to_abi Termination/End):
```sml
val () = cv_auto_trans default_to_abi_def;
```

### Add after line 249 (after vyper_to_abi Termination/End):
```sml
val vyper_to_abi_pre_def =
  vyper_to_abi_def
  |> REWRITE_RULE[GSYM n2w_o_ORD_eq]
  |> cv_auto_trans_pre_rec
       "vyper_to_abi_pre vyper_to_abi_list_pre vyper_to_abi_same_pre vyper_to_abi_sparse_pre"
       (WF_REL_TAC `measure (λx. case x of
         | INL (_, _, v) => cv_size v
         | INR (INL (_, _, vs)) => cv_size vs
         | INR (INR (INL (_, _, vs))) => cv_size vs
         | INR (INR (INR (_, _, _, n, sparse))) => cv_size sparse + cv$c2n n)`
        \\ rw[]
        \\ TRY (Cases_on `cv_v` \\ gvs[cvTheory.cv_size_def] \\ NO_TAC)
        \\ qmatch_goalsub_rename_tac `cv_snd p`
        \\ Cases_on `p` \\ gvs[cvTheory.cv_size_def]
        \\ qmatch_goalsub_rename_tac `cv_fst p`
        \\ Cases_on `p` \\ gvs[cvTheory.cv_size_def]);

Theorem vyper_to_abi_pre[cv_pre]:
  (∀env t v. vyper_to_abi_pre env t v) ∧
  (∀env ts vs. vyper_to_abi_list_pre env ts vs) ∧
  (∀env t vs. vyper_to_abi_same_pre env t vs) ∧
  (∀env t tv n sparse. vyper_to_abi_sparse_pre env t tv n sparse)
Proof
  ho_match_mp_tac vyper_to_abi_ind
  \\ rw[]
  \\ rw[Once vyper_to_abi_pre_def]
QED
```

### Replace the comment at lines 707-708 with:
```sml
val () = cv_auto_trans evaluate_abi_encode_def;
```

## Execution Order

1. Try `cv_auto_trans default_to_abi_def` first - if it fails, we know we need to expand `MAP (default_to_abi o SND)`
2. Try `cv_auto_trans_pre_rec` for vyper_to_abi - the termination proof is the main challenge
3. Once vyper_to_abi is translated, `cv_auto_trans evaluate_abi_encode_def` should work automatically
4. Run `Holmake` to verify everything builds
