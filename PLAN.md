# Plan: Remove CV-Termination Cheat for vyper_to_abi

## Current Status

**Partially completed.** Most termination goals are proven, but one goal remains cheated.

## What Was Done

### 1. Added Helper Theorems (lines 300-331)
- `cv_ALOOKUP_snd_size` - proves ALOOKUP result size is smaller than sparse list
- `cv_size_cv_fst_le` - cv_fst doesn't increase size (weak bound)
- `cv_size_cv_snd_le` - cv_snd doesn't increase size (weak bound)
- `c2n_le_cv_size` - c2n is bounded by cv_size

### 2. Added cv_bounds_tac Helper Tactic (lines 333-383)
A custom tactic that finds cv_fst/cv_snd/c2n subterms in the goal and adds appropriate bounds as assumptions. This enables decide_tac to close arithmetic goals.

### 3. Partial Termination Proof (lines 385-474)
The termination tactic now handles:
- Simple cv_snd cases via cv_termination_simp
- cv_sub for sparse n-1 case
- ALOOKUP result case using cv_ALOOKUP_snd_size
- StructT cv_delete case using cv_delete_ind induction (~45 lines)
- Most projection goals via cv_bounds_tac + decide_tac

## Remaining Cheat

One termination goal is still cheated (line 474):

```
cv$c2n (cv_fst (cv_snd (cv_snd (cv_snd cv_v)))) +
(cv_size (cv_fst (cv_snd cv_v0)) +
 cv_size (cv_snd (cv_snd (cv_snd (cv_snd cv_v))))) <
cv_size cv_v + cv_size cv_v0
```

### Root Cause

This goal comes from the `vyper_to_abi -> vyper_to_abi_sparse` transition (SArrayV Fixed case). The issue is:

1. The original termination goal has guards like `cv$c2b (cv_ispair ...)` that ensure cv_v and cv_v0 have Pair structure
2. The `rw[]` tactic simplifies these guards away (e.g., `cv_ispair (Pair a b) = Num 1` becomes trivially true)
3. After rw[], the goal is unconditional with no structure information
4. The cv_bounds_tac adds weak bounds (`<=`) but we need strict bounds (`<`)
5. Without knowing cv_v/cv_v0 are Pairs, we can't prove strict inequality

### Potential Solutions

1. **Don't use rw[] globally** - Instead, handle each goal with strip_tac first to preserve structure information. This requires rewriting all TRY blocks.

2. **Add structure-specific lemmas** - Prove that for sufficiently-nested Pair values, the projections are strictly smaller:
   ```sml
   Theorem cv_size_nested_proj_lt:
     cv_size (cv_fst (cv_snd (Pair a (Pair b c)))) + 
     cv_size (cv_snd (cv_snd (cv_snd (cv_snd (Pair d (Pair e (Pair f (Pair g h)))))))) <
     cv_size (Pair a (Pair b c)) + cv_size (Pair d (Pair e (Pair f (Pair g h))))
   ```
   Then case-split on cv_v and cv_v0 and dismiss Num cases.

3. **Modify the measure** - Perhaps a different measure would avoid this problematic goal.

## Files Modified

- `semantics/vyperABIScript.sml`:
  - Added helper theorems (lines 300-331)
  - Added cv_bounds_tac (lines 333-383)
  - Improved termination tactic with TRY blocks for different cases
  - One cheat remains (line 474)

## Build Status

- Build succeeds with `CHEATED` warning
- The cheat propagates to `cv_vyper_to_abi_thm` and `cv_evaluate_abi_encode_thm`
- All other theorems in vyperABITheory are proven

## Next Steps

To fully remove the cheat:

1. Investigate approach #2 (structure-specific lemmas) as the most promising
2. Would need to case-split on cv_v and cv_v0, using `Cases_on` to get Pair/Num
3. For Pair cases, the strict inequality should follow from Pair overhead
4. For Num cases, need to show they don't arise (contradicts original guards)
