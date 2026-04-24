# STATE: Type Soundness Repair

## Overall Status: eval_expr_not_HashMapRef — P0_Subscript blocked at Triviality level

## Build State
- vyperTypeSoundnessHelpersTheory: FAILS at `subscript_not_HashMapRef_ec` Triviality
- vyperTypeSoundnessTheory: FAILS (depends on helpers)
- Cheats remaining: line 614 (functions_well_typed_body_full, pre-existing from branch diff)

## Theorem IS TRUE
HashMapRef only comes from TopLevelName. Subscript evaluation produces Values
via evaluate_subscript or read_storage_slot, both returning Value not HashMapRef.
The IH application is the only obstacle.

## Current Proof Structure for eval_expr_not_HashMapRef
- Structural induction on `e` via `Induct_on `e` >> rpt conj_tac`
- 13 subgoals (P0 constructors only — P1-P5 internal to expr_induction)
- All Resume blocks proved EXCEPT P0_Subscript and P0_Call

## P0_Subscript: The Core Problem

### Structural Issue
The structural induction IH has `env_consistent` precondition:
```
∀cx' st'' tv' st'''. well_typed_expr env e ∧ env_consistent env cx' st''
  ∧ eval_expr cx' e st'' = (INL tv', st''') ⇒ ¬is_HashMapRef tv'
```

The proven `subscript_not_HashMapRef` Triviality requires a simpler IH:
```
∀st res st'. eval_expr cx e st = (res, st') ⇒ ∀tv. res = INL tv ⇒ ¬is_HashMapRef tv
```

**The gap**: we CAN'T derive the simpler form because it requires env_consistent
for ALL states, but our IH only guarantees it for env_consistent states.

### What's been tried and failed (6+ attempts):
1. **Original proof** (6816-6836): expansion + `first_x_assum (drule_then assume_tac)` + case analysis → stuck at `F` goal, can't bridge from IH
2. **`irule subscript_not_HashMapRef`** in the Resume block → can't discharge the simpler IH precondition
3. **`subscript_not_HashMapRef_ec` Triviality with `metis_tac[]`** bridge → metis can't instantiate the universally-quantified IH
4. **`first_x_assum drule_all`** bridge → wrong assumption selected by first_x_assum
5. **`last_x_assum drule_all`** bridge → same issue
6. **`qpat_x_assum` with pattern** on IH → pattern doesn't match
7. **`irule` inside `by`** to derive weaker IH → irule produces existential variables that simp[] can't close (needs env_consistent for arbitrary s)

### The Right Approach (not yet tried)
Direct proof of `subscript_not_HashMapRef_ec` WITHOUT the bridging step:
- Expand the Subscript evaluate clause (same as subscript_not_HashMapRef)
- After expansion + strip, specific `eval_expr cx e st = ...` facts appear
- Use `eval_expr_preserves_ec` to get env_consistent for intermediate states
- Apply the IH using **explicit `qspecl_then`** at the KNOWN state `st`:
  ```
  qpat_x_assum `!cx' st'' tv' st'''. well_typed_expr env e /\ ... ==> _`
    (qspecl_then [`cx`, `st`] mp_tac) >>
  impl_keep_tac >- (simp[]) >>
  ```
  This should work because after expansion, `eval_expr cx e st = ...`
  IS in the assumptions, `well_typed_expr env e` IS in the assumptions,
  and `env_consistent env cx st` IS in the assumptions.

The key difference from `drule_all`: explicit specialization avoids the need
for HOL to auto-match ALL antecedents simultaneously. By specializing just
cx' and st'' first, we get a residual that matches the eval fact directly.

### P0_Subscript Resume Block
```sml
Resume eval_expr_not_HashMapRef[P0_Subscript]:
  rpt strip_tac >>
  gvs[well_typed_expr_def] >>
  irule subscript_not_HashMapRef_ec >> simp[]
QED
```
This should work IF `subscript_not_HashMapRef_ec` proves.

## P0_Call: proof written but untested
Cases_on `c` with 8 call_target variants. Each uses _returns_Value lemmas
or extcall_*_not_HashMapRef. RawRevert case uses expansion. Needs testing.

## Proved Resume blocks (no cheats)
P0_Name, P0_BareGlobalName, P0_TopLevelName, P0_FlagMember, P0_IfExp,
P0_Literal, P0_StructLit, P0_Attribute, P0_Builtin, P0_Pop, P0_TypeBuiltin
(11 of 13)

## Pre-existing Cheat
Line 614: `functions_well_typed_body_full` - from branch diff, not on main.

## What NOT to Try
- DON'T use `irule` or `drule_all` to bridge IH forms — assumption selection is unreliable
- DON'T use `metis_tac[]` to derive the weaker IH — can't instantiate universal vars
- DON'T use `qpat_x_assum` with wildcard patterns on the IH — matching fails
- DON'T add P1-P5 entries — only 13 subgoals for expr constructors
- DON'T use `simp[evaluate_def]` without `Once` — HANGS
- DON'T use `ho_match_mp_tac evaluate_ind` — guarded ExtCall IH intractable
- DON'T try to derive `∀s. eval_expr cx e s = ... ⇒ ~is_HashMapRef` from guarded IH — impossible without env_consistent for ALL s

## Oracle Feedback
- Claude suggested `qspecl_then [`cx`,`s`,`tv0`,`s0`]` with explicit specialization + `asm_simp_tac` — most promising approach, NOT YET TRIED
- Gemini suggested ML-level MATCH_MP with error handling — too fragile, would rather use tactic-level `qspecl_then`
- Key insight from Claude: "The complex IH can be specialized to cx'=cx with any st'' where env_consistent holds. Since eval_expr_preserves_ec shows evaluating sub-expressions preserves env_consistent, every intermediate state in the Subscript evaluation maintains the invariant."

## Next Steps
1. Fix `subscript_not_HashMapRef_ec` using `qspecl_then` with explicit specialization
2. Test P0_Call Resume block
3. Build vyperTypeSoundnessHelpersTheory, then vyperTypeSoundnessTheory
4. Fix any remaining cheats
