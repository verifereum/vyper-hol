# STATE: Type Soundness Repair

## Overall Status: In-progress — systemic fix partially working, ReturnSome still blocked

## Build State
- vyperTypeSoundnessHelpersTheory: BUILDS OK
- vyperTypeSoundnessTheory: FAILS at ReturnSome block (first failing Resume block)
- Pre-existing cheat: `functions_well_typed_body_full` (line ~620, helpers file)

## KEY BREAKTHROUGH: augment_srw_ss for exception_distinct + error_distinct

Added `val _ = augment_srw_ss[rewrites [exception_distinct, error_distinct]]` to
vyperTypeSoundnessScript.sml. This single-line fix makes `gvs[]`/`simp[]` able to
prove `∀s. INR(AssertException x) ≠ INR(Error(TypeError s))` etc. automatically.

**Result**: Simple blocks that previously needed no-TypeError handling now pass:
Pass, Continue, Break, ReturnNone, Raise1, Raise2, Raise3 all now resolve.

## Remaining Problem: ReturnSome block

After `simp[bind_def, AllCaseEqs(), raise_def] >> strip_tac >> drule_all >> strip_tac >> gvs[]`,
ReturnSome produces 2 subgoals. In each:
- `∀s. e' ≠ Error(TypeError s)` IS in the assumptions (from IH via drule_all)
- The no-TypeError conjunct `∀s. e' ≠ Error(TypeError s)` appears in the goal
- But `not_type_error_tac` STILL can't solve it

**Hypothesis**: `gvs[]` or a prior step is consuming/transforming the IH-derived
`∀s. e' ≠ Error(TypeError s)` assumption before `not_type_error_tac`'s ACCEPT_TAC
can match it. Need to investigate by checking actual assumption list at the point
where `not_type_error_tac` is invoked.

**Alternative hypothesis**: The `spose_not_then` strategy I added to `not_type_error_tac`
may be interfering with `ACCEPT_TAC`. Need to verify ordering.

## not_type_error_tac Current Structure (lines 215-265)
1. `first_assum ACCEPT_TAC` — should match IH-derived no-TypeError if available
2. `first_x_assum drule_all` — IH discharge
3. `spose_not_then strip_assume_tac >> materialise_type_error_imp_NoneTV >> ...`
   (contradiction strategy for materialise INR cases)
4. `gvs[toplevel_value_typed_def, ...]` — may destroy useful assumptions!
5. Various imp_res_tac for bridge lemmas
6. `gvs[raise_def, return_def, ...]` as last resort

**WARNING**: Step 4 (`gvs[toplevel_value_typed_def,...]`) is unconditional and
may transform/destroy the IH-derived assumption needed in step 1.

## Proof Structure: 82 Resume blocks

Blocks now handled by augment_srw_ss (constructor distinctness): Pass, Continue,
Break, ReturnNone, Raise1, Raise2, Raise3, and any others where `res` is directly
a known exception constructor.

Blocks using `tp_stmt_no_return_tac` (includes `TRY not_type_error_tac`):
Raise3, Assert1, Assert2, Log, Expr — these should partially work.

Blocks using `tp_bind_err_tac` (includes `TRY not_type_error_tac`):
Various expression blocks — partial coverage.

59 blocks have NO not_type_error_tac call — they rely solely on `gvs[]` and
`simp[]` for everything. With `augment_srw_ss`, many should now work for
constructor distinctness cases. But blocks with IH-based no-TypeError subgoals
(e.g., where sub-evaluation produces `INR e'`) will still fail.

## IH-Based no-TypeError Pattern (common across ~40 blocks)

After `bind` expansion: `eval_expr cx e st = (v, s'')` where `v = INR e'`.
Goal: `∀s. res ≠ INR (Error(TypeError s))` where `res = INR e'` (after substitution).
IH gives: `∀s. v ≠ INR (Error(TypeError s))` → after gvs: `∀s. e' ≠ Error(TypeError s)`.
This should be identical to the goal → ACCEPT_TAC should work.

**Why it doesn't**: Need to debug. Possible causes:
1. gvs[] normalizes goal/assumptions differently (alpha-equivalence issues?)
2. gvs[] consumes the assumption
3. The spose_not_then step runs first and modifies goal before ACCEPT_TAC
4. Variable naming after gvs[] substitution creates mismatch

## Next Steps
1. **Debug ReturnSome**: Use hol_state_at to see exact goal+assumptions right
   before not_type_error_tac runs. Check if `∀s. e' ≠ Error(TypeError s)` is
   still in assumptions or got consumed.
2. **If ACCEPT_TAC issue**: Consider `first_assum (fn th => MATCH_ACCEPT_TAC th)`
   or `first_x_assum match_mp_tac` for more flexible matching.
3. **If gvs[] consuming assumption**: Split goals BEFORE gvs, or use `fs[]`
   instead of `gvs[]` to avoid variable elimination.
4. **Once ReturnSome fixed**: Build and see how many more blocks pass with the
   augment_srw_ss fix. Expect ~40+ blocks to now work.
5. **Remaining blocks**: Need IH-based no-TypeError propagation. If the
   ACCEPT_TAC approach works, most should resolve automatically.

## What NOT to Try
- DON'T use suspend/Resume for eval_expr_not_HashMapRef (breaks; use >- blocks)
- DON'T use `simp[evaluate_def]` without `Once` — HANGS
- DON'T expand evaluate_def in main proof
- DON'T assume variable names from expr constructor syntax
- DON'T add `spose_not_then` before ACCEPT_TAC in not_type_error_tac (may interfere)
- DON'T create bridge lemmas from guarded to unguarded IH forms
- DON'T patch 59 blocks individually — use systemic tactic/simpset fixes

## Oracle Feedback
- Previous oracle suggested IH discharge + constructor distinctness — partially
  correct. The augment_srw_ss fix handles constructor distinctness. IH-based
  matching (ACCEPT_TAC) should handle the rest but has a bug to debug.
