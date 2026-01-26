# Plan: Remove CV-Termination Cheat for vyper_to_abi

## Current Status

**Partially completed.** Most termination goals are proven, but one goal remains cheated.

## What Was Done

### 1. Added Helper Theorems (lines 300-340)
- `cv_ALOOKUP_snd_size` - proves ALOOKUP result size is smaller than sparse list
- `cv_size_cv_fst_le` - cv_fst doesn't increase size (weak bound)
- `cv_size_cv_snd_le` - cv_snd doesn't increase size (weak bound)
- `c2n_le_cv_size` - c2n is bounded by cv_size
- `cv_ispair_is_pair` - cv_ispair guard implies value is a Pair

### 2. Added cv_bounds_tac Helper Tactic (lines 342-392)
A custom tactic that finds cv_fst/cv_snd/c2n subterms in the goal and adds appropriate bounds as assumptions. This enables decide_tac to close arithmetic goals.

### 3. Partial Termination Proof (lines 394-485)
The termination tactic now handles:
- Simple cv_snd cases via cv_termination_simp
- cv_sub for sparse n-1 case
- ALOOKUP result case using cv_ALOOKUP_snd_size
- StructT cv_delete case using cv_delete_ind induction (~45 lines)
- Most projection goals via cv_bounds_tac + decide_tac

## Remaining Cheat

One termination goal is still cheated (SArrayV Fixed case).

### The Goal

After `rw[cv_repTheory.cv_termination_simp]`, the remaining goal is:
```
cv$c2n (cv_fst (cv_snd (cv_snd (cv_snd cv_v)))) +
(cv_size (cv_fst (cv_snd cv_v0)) +
 cv_size (cv_snd (cv_snd (cv_snd (cv_snd cv_v))))) <
cv_size cv_v + cv_size cv_v0
```

### Available Assumptions (Guards)

The goal has these important guards in assumptions:
1. `cv$c2b (cv_ispair cv_v)` - cv_v is a Pair
2. `cv$c2b (cv_ispair cv_v0)` - cv_v0 is a Pair
3. `cv$c2b (cv_ispair (cv_snd (cv_snd cv_v0)))` - nested component of cv_v0 is also a Pair

### Proof Strategy

The proof requires using ALL THREE guards to get enough Pair constructor overhead:

1. **Case split on cv_v**: `Cases_on cv_v` gives `Num m` (dismissed by guard 1) or `Pair g g'`
2. **Case split on cv_v0**: `Cases_on cv_v0` gives `Num m` (dismissed by guard 2) or `Pair g'' g'''`
3. **Case split on g'''**: Guard 3 says `cv_snd g'''` is a Pair, so `g''' = Pair h h'`
4. **Case split on g'**: The LHS has `cv_snd (cv_snd (cv_snd g'))` which requires g' to be nested Pairs

After 4 case splits:
- cv_v = Pair g (Pair g5 g6)
- cv_v0 = Pair g'' (Pair g3 g4)
- g4 = Pair h h' (from guard 3)

This gives:
- cv_size cv_v = cv_size g + cv_size g5 + cv_size g6 + 2  (two Pair constructors)
- cv_size cv_v0 = cv_size g'' + cv_size g3 + cv_size h + cv_size h' + 3 (three Pair constructors)

Total RHS overhead: +5 from Pair constructors

The LHS uses projections from g6 and g4, and with bounds:
- c2n(cv_fst(cv_snd g6)) ≤ cv_size g6
- cv_size(cv_snd(cv_snd g6)) ≤ cv_size g6
- cv_size(cv_fst g4) = cv_size g3 (after case split on g4 = Pair g3 g4')

So LHS ≤ 2*cv_size g6 + cv_size g3 < RHS (because RHS has cv_size g6 + cv_size g3 + other terms + 5)

### Why decide_tac Fails

The issue is that decide_tac needs explicit transitivity chains. The proof requires:
1. `sg \`c2n(cv_fst(cv_snd g6)) <= cv_size g6\` >- simp[]`
2. `sg \`cv_size(cv_snd(cv_snd g6)) <= cv_size g6\` >- simp[]`
3. Then show that `2*cv_size g6 + cv_size g3 < RHS`

The +5 overhead from Pair constructors is enough, but decide_tac doesn't see the connection without explicit intermediate lemmas.

## Files Modified

- `semantics/vyperABIScript.sml`:
  - Added helper theorems (lines 300-340)
  - Added cv_bounds_tac (lines 342-392)
  - Improved termination tactic with TRY blocks for different cases
  - One cheat remains (line 484) with detailed documentation

## Build Status

- Build succeeds with `CHEATED` warning
- The cheat propagates to `cv_vyper_to_abi_thm` and `cv_evaluate_abi_encode_thm`
- All other theorems in vyperABITheory are proven

## Next Steps

To fully remove the cheat:

1. **Replace the cheat with explicit case splits**:
   ```sml
   \\ Cases_on `cv_v` \\ fs[cvTheory.cv_ispair_def, cvTheory.c2b_def]
   \\ Cases_on `cv_v0` \\ fs[cvTheory.cv_ispair_def, cvTheory.c2b_def, cvTheory.cv_snd_def]
   \\ qmatch_asmsub_rename_tac `cv_ispair (cv_snd ggg)`
   \\ Cases_on `ggg` \\ fs[cvTheory.cv_ispair_def, cvTheory.cv_snd_def]
   \\ Cases_on `g'` \\ fs[cvTheory.cv_ispair_def, cvTheory.cv_snd_def, cvTheory.cv_size_def,
                          cvTheory.cv_fst_def, cvTheory.c2n_def]
   ```

2. **Add explicit intermediate bounds** using `sg ... >- simp[]` to chain inequalities

3. **Close with simp[]** after bounds are added (decide_tac may work after explicit chaining)

4. The proof will be ~20-30 lines but should be straightforward once the structure is right
