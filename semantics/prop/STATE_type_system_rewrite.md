# STATE_type_system_rewrite
Updated: 2026-05-31

## Cursor
- component: C2.7
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Write a standalone `extcall_expr_sound[local]` helper theorem before the `Expr_Call_ExtCall` Resume. Then update the Resume to apply it. The helper should take 3 IH premises (eval_exprs, eval_expr for THE drv, plus well_typed_expr/runtime/evaluation facts) and prove the full soundness conclusion. Proof structure: unfold well_typed_expr_def and evaluate_def, case-split on eval_exprs, use IH for args, case-split on is_static, use extcall_static_args_runtime_typed_dest / extcall_nonstatic_args_runtime_typed_dest, step-by-step simplify monadic operations (check, lift_option_type, lift_option, get_accounts, get_transient_storage, run_ext_call, check success, update_accounts, update_transient), then bridge to extcall_return_tail_sound. Key bridging issue: after update_accounts/update_transient, the goal contains a lambda-application continuation `(λ(success,returnData,accounts',tStorage'). ...) result` that must be simplified to match extcall_return_tail_sound's expected shape. Use `simp[update_accounts_def, update_transient_def, return_def]` then further simplification to convert the lambda application into the `do ... od st = (res,st')` form. Alternatively, use `qspecl_then` with Abbrev for the record-updated state.
- expected_goal_shape: After eval_exprs succeeds, args destructed, build_ext_calldata succeeds, code check passes, run_ext_call returns SOME(success,returnData,accounts',tStorage'), success check passes, update_accounts/update_transient applied: goal is the final `extcall_return_tail_sound` continuation equation plus the full soundness conclusion.
- verify_with: `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=120)`. The ExtCall/RawCallTarget cheats should both be removed once extcall_expr_sound builds and the Resume applies it.

## If This Fails
- If extcall_return_tail_sound doesn't match after the monadic simplification, the lambda-application form may need explicit beta reduction or case splitting on the result tuple before the tail helper. Check if `simp[PAIR_EQ]` or `TOP_CASE_TAC` converts the applied lambda to a direct `if ... then ... else ...` form that matches.
- If the RawCallTarget proof also needs work, apply the same step-by-step monadic simplification pattern adapted to that evaluator's fewer bound steps.

## Do Not Retry
- Do not unfold ALL monadic definitions at once with `simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def, return_def, raise_def, lift_option_type_def, lift_option_def, lift_sum_runtime_def, get_accounts_def, get_transient_storage_def, update_accounts_def, update_transient_def]` in the Resume context — this causes timeout/explosion.
- Do not use the `<| ... |>` record update syntax inside backtick quotations in the Resume context — it can cause parse errors within the `markerLib.resume` wrapper. The simpler `st with f1 := v1, f2 := v2` syntax works in standalone Theorem proofs but should also be avoided in backtick quotations within Resumes. Instead use `Abbrev` or avoid constructing record updates inside backticks.

## Reflection
### Tooling Status
- The `holbuild --strict-parse` blocker reported in the old STATE is resolved: holbuild builds successfully without `--strict-parse`. The current holbuild works correctly without that option.
- vyperTypeStmtSoundnessTheory builds with the 2 ExtCall/RawCallTarget cheats and 1 raw_call_return_type_well_formed cheat.

### Proof Architecture Lessons
- The ExtCall proof needs a standalone helper theorem (`extcall_expr_sound[local]`) outside the Resume, not an inline Resume proof. The Resume just applies the helper. This avoids the `markerLib.resume` wrapper limitations.
- Step-by-step monadic simplification works: unfold one or two defs at a time after the initial `simp[Once evaluate_def]`, then case-split the result. Each step is a small `simp[<specific_defs>]` followed by a `Cases_on`.
- The already-proved helpers are sufficient: `extcall_static_args_runtime_typed_dest`, `extcall_nonstatic_args_runtime_typed_dest`, `run_ext_call_accounts_well_typed`, `update_accounts_transient_runtime_consistent`, and `extcall_return_tail_sound`.
- The remaining gap is the bridging tactic between update_accounts/update_transient and extcall_return_tail_sound. After the pair destruct and check-success simplification, the evaluator produces `(λ(success,returnData,accounts',tStorage'). ...) result` where `result = (T, x1, x2, x3)`. This lambda applied to the result tuple needs to be beta-reduced/simplified to get the direct `if ... then eval_expr (THE drv) ... else do evaluate_abi_decode_return ... od st = (res,st')` form that extcall_return_tail_sound expects.
- `evaluate_type env.type_defs ret_type2 = SOME ret_tv` can be derived from `well_formed_type env.type_defs ret_type2` via `well_formed_type_def` and `IS_SOME_EXISTS`.

### Remaining Cheat Inventory
- `vyperTypeStmtSoundnessScript.sml`: 2 cheats (Expr_Call_ExtCall, Expr_Call_RawCallTarget)
- `vyperTypeBuiltinsScript.sml`: 1 cheat (raw_call_return_type_well_formed)
- Total: 3 reachable fresh-stack cheats

### Next Steps
1. Write extcall_expr_sound[local] helper with step-by-step proof
2. Fix the lambda-application bridging to extcall_return_tail_sound
3. Update Resume to apply extcall_expr_sound
4. Apply same pattern for RawCallTarget
5. Audit build for remaining cheats
