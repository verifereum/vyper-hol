# STATE: Type Soundness Repair

## Overall Status: eval_expr_not_HashMapRef — P0_Subscript SOLVED, P0_TypeBuiltin now failing

## Build State
- vyperTypeSoundnessHelpersTheory: FAILS at P0_TypeBuiltin Resume block (goal = F)
- vyperTypeSoundnessTheory: FAILS (depends on helpers)
- Cheats remaining: line 614 (functions_well_typed_body_full, pre-existing from branch diff)
- Deleted: subscript_not_HashMapRef_ec Triviality (no longer needed)

## Key Breakthrough: P0_Subscript SOLVED

### The Approach That Finally Worked
After 6+ failed attempts at the bridge lemma `subscript_not_HashMapRef_ec`, the correct
decomposition was to **prove P0_Subscript directly in the Resume block** using the
structural induction IH, NOT via a bridge lemma. The working proof:

```sml
Resume eval_expr_not_HashMapRef[P0_Subscript]:
  rpt strip_tac >>
  gvs[well_typed_expr_def] >>
  first_x_assum (qspecl_then [`cx`, `st`] assume_tac) >>
  gvs[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac [el 8 ev_expr_cjs] >>
  simp_tac (srw_ss()) [bind_def, return_def, raise_def, ignore_bind_def,
    UNCURRY, lift_option_type_def, lift_option_def, lift_sum_def,
    lift_sum_runtime_def, AllCaseEqs(), is_HashMapRef_def,
    get_Value_def, get_tenv_def, check_array_bounds_def,
    LET_THM, COND_RATOR] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs (AllCaseEqs() :: is_HashMapRef_def :: hmr_case_defs)) >>
  imp_res_tac evaluate_subscript_success_not_HashMapRef >>
  gvs[is_HashMapRef_def]
QED
```

### Why Bridge Lemma Failed (6+ attempts)
The `subscript_not_HashMapRef` requires an UNGUARDED IH:
`∀st res st'. eval_expr cx e st = (res,st') ⇒ ∀tv. res = INL tv ⇒ ¬is_HashMapRef tv`
The structural induction provides a GUARDED IH:
`∀cx' st'' tv' st'''. well_typed_expr env e ∧ env_consistent env cx' st'' ∧ ... ⇒ ¬is_HashMapRef`
Cannot derive unguarded IH from guarded — would need env_consistent for ALL states.
irule/drule_all/metis all failed to bridge this gap.

### Why Direct Proof Works
In the Resume block, `gvs[well_typed_expr_def]` gives `well_typed_expr env e` and
`env_consistent env cx st` as assumptions. So `first_x_assum (qspecl_then [`cx`,`st`] assume_tac)`
specializes the guarded IH at (cx,st), then `gvs[]` discharges the well_typed and
env_consistent preconditions, leaving only `eval_expr cx e st = (INL tv',st''') ⇒ ¬is_HashMapRef tv'`.
After expanding the Subscript clause, `first_x_assum drule >> strip_tac` applies this
at the concrete eval fact. No bridging needed!

## Current Failure: P0_TypeBuiltin

Build output shows: `∀t t0 t1 cx st tv st'. well_typed_expr env (TypeBuiltin t1 t0 t l) ...`
fails with "First unsolved sub-goal is F".

Previous proof was: `imp_res_tac typebuiltin_returns_Value >> gvs[is_HashMapRef_def]`

TypeBuiltin was changed in this branch — AbiEncode was added (previously excluded with `F`).
The `typebuiltin_returns_Value` lemma may no longer cover AbiEncode case, or
the evaluate clause for TypeBuiltin now has branches that can produce non-Value results.

Need to investigate: what does the TypeBuiltin evaluate clause look like after AbiEncode addition?

## Proved Resume blocks (no cheats)
P0_Name, P0_BareGlobalName, P0_TopLevelName, P0_FlagMember, P0_IfExp,
P0_Literal, P0_StructLit, P0_Subscript, P0_Attribute, P0_Builtin, P0_Pop
(11 of 13 proved)

## Remaining Resume blocks
- P0_TypeBuiltin: FAILS — needs TypeBuiltin expansion fix
- P0_Call: written but untested (was working on main, needs retest)

## Pre-existing Cheat
Line 614: `functions_well_typed_body_full` - from branch diff, not on main.

## What NOT to Try
- DON'T create bridge lemmas from guarded to unguarded IH forms — impossible
- DON'T use `irule subscript_not_HashMapRef` with guarded IH — can't discharge all-states precondition
- DON'T use `PairCases_on` for Subscript — not a pair type
- DON'T use `simp[evaluate_def]` without `Once` — HANGS
- DON'T use pattern-specific `qpat_x_assum` with variable names like `p1` — names differ in induction context

## Oracle Feedback
- Claude suggested `qspecl_then [`cx`,`s`,`tv0`,`s0`]` — the key insight was correct (explicit specialization)
  but the full bridge approach was wrong. The correct insight was to specialize BEFORE expanding.
- Gemini suggested ML-level MATCH_MP — too fragile, correct to avoid
- Key pattern: when guarded IH blocks a lemma, prove directly in the Resume block instead

## Next Steps
1. Investigate P0_TypeBuiltin failure (AbiEncode addition to well_typed_type_builtin_args)
2. Fix P0_TypeBuiltin Resume block (possibly expand evaluate clause + use evaluate_type_builtin_not_HashMapRef or similar)
3. Test P0_Call Resume block
4. Build vyperTypeSoundnessHelpersTheory, then vyperTypeSoundnessTheory
5. Fix any remaining cheats
