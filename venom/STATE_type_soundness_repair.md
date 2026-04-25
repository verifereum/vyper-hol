# STATE: Type Soundness Repair

## Overall Status: In-progress — Raise3 still failing, ~48 blocks remaining

## Build State
- vyperTypeSoundnessHelpersTheory: BUILDS OK (pre-existing cheat on `eval_expr_not_HashMapRef` Call case)
- vyperTypeSoundnessTheory: FAILS at Raise3 (first failing Resume block after Raise1/Raise2 fixed)

## Fixes Applied This Session

### 1. Raise1/Raise2: FIXED ✓
- Both `Raise RaiseBare` and `Raise RaiseUnreachable` evaluate to `raise (AssertException ...)`.
- After `gvs[ev_RaiseN, raise_def]`, both TypeError and ReturnException conjuncts are trivially discharged by constructor distinctness (already in augment_srw_ss).
- Fix: Simplified from `gvs[ev_RaiseN, raise_def] >> TRY not_type_error_tac` to just `gvs[ev_RaiseN, raise_def]`

### 2. `tp_stmt_no_return_tac` and `tp_err_tac`: Restructured
- Changed end from `TRY not_return_tac >> TRY not_type_error_tac` to `rpt CONJ_TAC >> TRY not_return_tac >> TRY not_type_error_tac >> TRY (gvs[])`
- Key insight: `rpt CONJ_TAC` splits ALL conjunctions before tactics see individual goals
- Without this, tactics received conjunctions they couldn't handle

### 3. `not_type_error_tac` Strategy 3: Guarded with goal_term
- Strategy 3 (spose_not_then contradiction chain) now ONLY fires when goal mentions `TypeError`
- Guard: `goal_term (fn tm => if can (find_term (fn t => same_const ``TypeError`` t)) tm then ... else NO_TAC)`
- This prevents spose_not_then from corrupting state-well-typedness goals after CONJ_TAC splits

### 4. Raise3: Added `gvs[Once evaluate_type_def]` (CRITICAL FIX from oracle)
- **Root cause**: `evaluate_type` is opaque, so `tyv` from IH stays uninstantiated
- Bridge lemma `value_has_type_StringT_dest_StringV_NEQ_NONE` needs `value_has_type (BaseTV (StringT n)) v` but IH gives `value_has_type tyv v`
- `gvs[Once evaluate_type_def]` instantiates `evaluate_type ... (BaseT (StringT n)) = SOME (BaseTV (StringT n))`, revealing `tyv = BaseTV (StringT n)`
- This likely fixes MANY future cases too — TODO: add to `tp_stmt_no_return_tac` or `not_type_error_tac`

## Current not_type_error_tac Structure (order matters!)
1. Strategy 1: `ACCEPT_TAC` — IH-derived no-TypeError already in assumptions
2. Strategy 2: `drule_all` — IH discharge for sub-evaluation
3. `gvs[toplevel_value_typed_def, evaluate_type_not_NoneT_imp_not_NoneTV, evaluate_type_BaseT_imp_not_ArrayTV]`
4. Retry ACCEPT + drule_all after gvs
5. Bridge lemmas: materialise_Value_no_type_error, materialise_not_HashMapRef_no_type_error
6. More bridge lemmas: toplevel_value_typed_no_ArrayTV_get_Value
7. dest_StringV/BytesV/NumV/AddressV/ArrayV bridge lemmas
8. Constructor distinctness catch-all: `gvs[raise_def, return_def, check_def, ...]`
9. Strategy 3 (LAST): `spose_not_then` guarded by `goal_term` TypeError check

## BLOCKER: Raise3 May Still Fail
Last holmake had `Q_TAC0`/`FIRST_ASSUM` error. This could be:
- The `rpt (first_x_assum drule_all >> strip_tac)` loop applying drule to a no-TypeError IH that introduces constraints
- OR the `gvs[Once evaluate_type_def]` not being sufficient

**Next step**: Test Raise3 interactively with `hol_state_at` to see exact goal state after each step. If `gvs[Once evaluate_type_def]` works but leaves residual goals, add more specific tactics.

## Widespread Fix Needed: evaluate_type instantiation
The `gvs[Once evaluate_type_def]` pattern likely helps MANY cases (any case where the IH gives `evaluate_type ... ty = SOME tyv` but `tyv` needs to be concrete). Consider:
- Adding to `tp_stmt_no_return_tac` after `swt_resolve_state_tac`
- Adding to `not_type_error_tac` before bridge lemmas
- Adding to the ReturnSome block (which already works but might be fragile)

## Remaining ~48 Resume Blocks
Most should be extended with the conjunction-splitting pattern (`rpt CONJ_TAC`) and TypeError guard. Check each:
- **Simple cases** (no IH, direct evaluation): `gvs[...]` suffices
- **Cases with sub-evaluation IH**: Need `rpt CONJ_TAC >> TRY not_return_tac >> TRY not_type_error_tac`
- **Cases with materialise**: Need Strategy 3 (guarded spose_not_then)
- **Cases with evaluate_type**: Need `gvs[Once evaluate_type_def]`

## Key Pre-existing Cheats
- `eval_expr_not_HashMapRef` Call case: CHEAT (helpers line ~6822)
- `functions_well_typed_body_full`: CHEAT (helpers line ~620)

## What NOT to Try
- DON'T use `spose_not_then` without a TypeError guard in goal — it corrupts goals irreversibly
- DON'T use `qhdtm_assum 'materialise'` as guard — matches IH-derived materialise assumptions
- DON'T use `>-` inside Resume blocks (type error with gentactic)
- DON'T expand `evaluate_def` without `Once` — HANGS
- DON'T use `simp[Once run_block_def]` — HANGS; use `ONCE_REWRITE_TAC`
- DON'T forget `rpt BasicProvers.VAR_EQ_TAC` after spose_not_then
- DON'T assume `evaluate_type` auto-instantiates tyv — it's opaque! Need explicit `gvs[Once evaluate_type_def]`

## Oracle Feedback
- **Claude oracle**: Suggested the same proof structure as existing code — correct but doesn't identify the tyv instantiation gap
- **Gemini oracle**: CRITICAL INSIGHT — identified that `evaluate_type` is opaque, `tyv` stays uninstantiated, and `gvs[Once evaluate_type_def]` is needed to resolve `tyv = BaseTV (StringT n)`. This is the KEY fix. Low risk.
- Assessment: Gemini's insight about evaluate_type instantiation is the most important finding this session. The evaluate_type opacity affects MANY cases, not just Raise3.
