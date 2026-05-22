# STATE_type_system_rewrite
Updated: 2026-05-22

## Cursor
- component: C4.3.1
- status: blocked
- active_file: semantics/prop/vyperTypeSystemScript.sml; semantics/prop/vyperTypeBuiltinsScript.sml
- next_action: First run git status/diff to confirm partial C4.3 edits. Then query_plan. Current rendered PLAN unexpectedly says Oracle next is C2.0 even though the urgent broken-source repair is C4.3.1; do not edit until a beginable component authorizes it. If Oracle next is still C2.0, follow the gate or ask plan_oracle to make C4.3.1 next because the worktree is intentionally partial/broken from E0741. Once C4.3.1 is active, add `extract32_result_base_ok` in `vyperTypeSystemScript.sml`, strengthen `well_typed_type_builtin_args_def` Extract32 clause, delete the positive Bool counterexample theorem, and add the negative regression theorem.
- expected_goal_shape: After C4.3.1 repair, regression `¬ well_typed_type_builtin_args Extract32 (BaseT BoolT) [BaseT (BytesT (Fixed 32)); BaseT (UintT 256)]` should close by `simp[well_typed_type_builtin_args_def, extract32_result_base_ok_def]`. Current source before repair fails earlier at the attempted generic `evaluate_extract32_no_type_error` helper because `bt` is unrestricted.
- verify_with: holbuild(targets=["vyperTypeBuiltinsTheory"], timeout=600) after C4.3.1 edits; optionally holbuild(targets=["vyperTypeSystemTheory"], timeout=600) immediately after the definition edit.

## If This Fails
- If the regression is not direct simplification, fix the static predicate/Extract32 clause rather than proving a brittle contradiction. If query_plan still forces C2.0 while source is partial, call plan_oracle with scheduling/blocking evidence before editing. If the supported Extract32 helper still has an unrestricted `bt` residual after C4.3.1, checkpoint_progress under C4.3.2 and escalate.

## Do Not Retry
- Prove `evaluate_extract32_no_type_error` or C4.3 main theorem for arbitrary `BaseT bt` without a supported-result premise.: False: `bt = BoolT` satisfies old static premises but `evaluate_extract32` returns `INR (TypeError "evaluate_extract32 type")`.
  - evidence: episode:E0741
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m41314_t001
- Keep the positive theorem `type_builtin_no_type_error_extract32_bool_counterexample` in executable source after adding `extract32_result_base_ok`.: It is evidence for the old false predicate; after the definition repair the static premise should be false and the positive theorem should not build.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m41320_t001
- Edit C4.3.1 files while a different component is active or while query_plan says Oracle next must be something else.: Harness gate blocked switching once already; next session must begin the authorized component or get strategist scheduling repair before editing/building.
  - evidence: episode:E0742
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m41322_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m41326_t004
- Stage or commit current partial C4.3 source, or use `git add -A`.: Worktree contains intentionally partial source edits and unrelated untracked scratch files; current build is not clean.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m41311_t003
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m41263_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not yet tried: instead of localizing the support predicate to Extract32 only, consider whether a generic `type_builtin_target_supported` predicate would better align all type-builtins with runtime TypeError branches. Current oracle says localized Extract32 repair is sufficient; revisit only if more constructors show similar false cases.
- A fresh expert would first ask whether the static typing rule, not the proof, should rule out every evaluator `TypeError` branch. For Extract32, yes: supported result base types are exactly fixed bytes, uint, int, and address.
- The PLAN decomposition is now the right abstraction mathematically, but the scheduler/frontier may still be wrong. Do not tactic-thrash under the wrong active component.
- Do not optimize the main theorem proof until the definition repair/regression is build-checked. The problem is a definition boundary, not induction or rewrite ordering.

### What Went Wrong
- The original C4.3 theorem was false under the old static predicate: `well_typed_type_builtin_args Extract32` allowed `BaseT BoolT`, but `evaluate_extract32` returns `TypeError` for unsupported base types. Evidence: episode:E0741, tool_output:TO_type_system_rewrite-20260522T073012Z_m41314_t001.
- I left the source partial: `vyperTypeBuiltinsScript.sml` contains helper/proof edits from the failed path, including an obsolete positive counterexample theorem and a generic Extract32 helper that is false without a supported-base premise. Do not commit this state.
- The first replacement PLAN had a dependency scheduling bug: it authorized C4.3.2 before C4.3.1, and switching was blocked by active-component state. This was closed administratively as E0742 and reviewed by the strategist.

### Ignored Signals
- The first Extract32 residual had no target-base support premise; that was a definition/interface problem, not a tactic problem. I initially tried to prove a generic helper anyway before constructing the concrete BoolT counterexample.
- After the oracle repaired the subtree, query_plan still reported Oracle next C2.0 rather than C4.3.1. This is a schedule/frontier signal to re-check the gate before any next-session edits.
- A local counterexample theorem is useful only as evidence before a definition repair; after the repair it must be removed or replaced with a negative regression.

### Strategy Adjustments
- Repair the static interface first: add `extract32_result_base_ok` and strengthen only the Extract32 clause of `well_typed_type_builtin_args_def`. Then prove the negative Bool regression, then the supported Extract32 no-TypeError helper, then the main C4.3 theorem.
- Keep helper conclusions boundary-shaped: `extract32_result_base_ok bt` plus typed byte/int runtime values implies no `TypeError`; do not try to exclude `RuntimeError` or prove success in C4.3.
- Do not work on C4.4 ABI success branches while C4.3 no-TypeError is open. The source-authoritative theorem name `well_typed_type_builtin_no_type_error` should remain, with stronger meaning from the repaired static predicate.

### Oracle Feedback
- Strategist accepted E0741 as valid negative evidence and chose a localized definition repair: add `extract32_result_base_ok` and strengthen the Extract32 static predicate, rather than weakening public wrappers.
- Strategist accepted E0742 as administrative cleanup only, not a mathematical failure of the new supported helper. Current PLAN says C4.3.1 should run first, then C4.3.2 helper, then C4.3.3 main theorem.
- One scheduling issue remains visible in the latest query_plan output: Oracle next is C2.0 even though C4.3.1 is the intended repair and the source is partial. Next session must obey/repair the gate before editing.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41314_t001 - build showed the checked positive BoolT counterexample theorem passed, then generic Extract32 helper failed because target `bt` was unrestricted
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41311_t003 - diff showing current partial source edits: positive counterexample, typed-value helpers, false generic Extract32 helper, and partial main theorem proof
- episode:E0741 - C4.3 closed stuck/wrong_statement with verified falsehood evidence for old theorem/static predicate
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41320_t001 - strategist replaced C4.3 subtree and merged definition repair + Bool regression into new C4.3.1
- episode:E0742 - administrative abandonment of stale active C4.3.2 after subtree replacement; not a mathematical failure
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41326_t004 - latest query_plan: no high-risk components, active none, but Oracle next C2.0 and C4.3.1 queued
