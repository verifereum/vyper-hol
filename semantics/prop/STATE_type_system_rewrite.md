# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.2.1.1
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit/build first. Run query_plan(); if it still shows C0/C0.2/C0.2.1/C0.2.1.1 high-risk with no frontier and blocking episode E0109, call plan_oracle(mode='augment' or 'replace', component_id='C0.2.1.1', evidence_ids=[...]) only if the operator explicitly wants redesign. Otherwise report blocked per the task stop condition.
- expected_goal_shape: Blocked by accepted E0109. The proposed local helper `extcall_expr_sound_from_generated_driver_ih` can traverse ExtCall prefix/error branches only if success-tail driver obligations are cheated. Opening `extcall_generated_driver_ih_def` in the success branch and manually specializing the generated ExtCall prefix produces a >4KiB goal with brittle state-variable plumbing; source has been reverted to the prior build-clean placeholder baseline.
- verify_with: Only after a replacement PLAN authorizes a beginable low-risk leaf: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300). Do not build while the PLAN gate remains blocked.

## If This Fails
- If a redesigned proof again requires broad generated-prefix simplification, long `qspecl_then`/adapter plumbing over ExtCall prefix variables, or exposes >4KiB generated-prefix goals before/tail success, close/checkpoint as risk_mismatch with tool evidence and stop rather than tactic-thrashing.

## Do Not Retry
- Copy `extcall_expr_sound_from_generated_ih` into `extcall_expr_sound_from_generated_driver_ih` and patch only the success-tail obligations by opening `extcall_generated_driver_ih_def`.: E0109 showed the surrounding skeleton is not the problem; the tail still needs long generated-prefix specialization and produces >4KiB goals. This is a proof-interface failure, not a missing tactic.
  - evidence: episode:E0109
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2455_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2458_t001
- Manual `qspecl_then`/`MATCH_MP_TAC` over all `extcall_generated_driver_ih_def` prefix variables in the success branch.: This is exactly the forbidden long adapter/plumbing shape; even after adjusting variable order it failed with a >4KiB generated-prefix goal.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2458_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2460_t001
- Proceed to C0.2.1.2, C0.2.2, C0.2.3, C0.3+, or cleanup proofs while C0.2.1.1 remains blocked.: The structured gate has no beginable frontier and C0.2.1.1@E0109 blocks the subtree; downstream work would violate the PLAN gate and task stop condition.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2470_t004

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not yet tried: change the mutual proof/suspension boundary so the optional-driver IH is never generated as a huge prefix-guarded assumption in unrelated branches, rather than trying to consume that assumption later.
- We may still be optimizing the wrong helper: the failed helper is not `extcall_success_continuation_sound_cond_driver_ih`; the root problem is `extcall_generated_driver_ih_def` itself, whose elimination interface demands all generated prefix witnesses.
- The PLAN decomposition is still too close to the generated evaluator prefix. A true boundary might need a smaller predicate that already stores the conditional driver postcondition, or a suspension point after prefix success, not a theorem that replays the whole prefix.
- Do not retry tactic variants for the long `qspecl_then` list. That is the forbidden adapter/plumbing shape, not a proof-search opportunity.
- A fresh expert should first ask whether the generated mutual proof can name the driver IH at the success continuation directly, or whether a source-level proof-architecture refactor can isolate the prefix success fact without reconstructing all prefix states.

### What Went Wrong
- The replacement plan assumed an opaque-driver boundary lemma would be Risk 2 because the driver predicate would stay hidden until the tail. E0109 showed that opening it at the tail is itself non-straightforward: the eliminator/interface still requires dozens of generated prefix variables and produced a >4KiB goal.
- The copied `extcall_expr_sound_from_generated_ih` skeleton builds with cheats only at the success-tail driver premises, so prefix/error cases are not the blocker. The blocker is precisely deriving the conditional driver IH from `extcall_generated_driver_ih`.
- Manual specialization of `extcall_generated_driver_ih_def` recreated the long generated-prefix adapter theorem the PLAN explicitly said not to introduce.
- Attempted helper edits were reverted; `holbuild` confirms the theory is back to the previous build-clean placeholder baseline, but task obligations remain unresolved.

### Ignored Signals
- Earlier learnings L0031/L0055/L0076 already warned that prefix-guarded driver IHs are proof-interface failures and that long adapter/specialization is not acceptable. The replacement plan underweighted that the same issue would reappear inside the helper.
- The first success-tail proof shape needed a long quoted `qspecl_then` list; that alone was a design smell before the >4KiB failure confirmed it.
- The fact that the helper compiled only with cheats at two identical tail obligations suggested a reusable interface mismatch, not two local tactical holes.

### Strategy Adjustments
- Treat C0.2.1.1 as blocked pending a real redesign/operator instruction, not as an active proof leaf. Query_plan currently reports no scheduled frontier and blocking episode E0109.
- Any next redesign should validate its interface by first deriving the driver postcondition in the success branch with a short match-driven tactic, before copying the full ExtCall prefix proof skeleton.
- Prefer a helper whose premise is already the compact conditional driver postcondition `(returnData=[] /\ IS_SOME drv ==> ...)`, or a suspension that creates that fact where it is generated, over a predicate that must be opened via all prefix witnesses.
- Respect the task contract: if the design cannot be made entirely straightforward inside `semantics/prop`, stop/report blocked instead of editing evaluator definitions or continuing proof search.

### Oracle Feedback
- Held: E0107/E0108 diagnosis was correct that the optional-driver generated prefix is the central ExtCall hazard, and source must not proceed to siblings while this gate is unresolved.
- Missed: the C0.2.1.1 replacement believed `extcall_generated_driver_ih` would be an adequate opaque boundary; E0109 shows its elimination interface is still too close to the generated prefix and non-straightforward.
- Latest strategist review accepted E0109 and made no repair, explicitly aligning with the user's stop-on-design-issue instruction.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2470_t004 - current PLAN gate: high-risk C0/C0.2/C0.2.1/C0.2.1.1, no frontier, blocking E0109
- episode:E0109 - terminal risk_mismatch for C0.2.1.1; opaque-driver helper still not straightforward
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2455_t001 - helper skeleton built only with success-tail cheats, localizing the hard obligations
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2458_t001 - first real tail-specialization attempt exposed >4KiB generated-prefix goal
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2460_t001 - corrected manual specialization still failed with same >4KiB/brittle prefix shape
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2465_t001 - build restored after reverting attempted helper
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2467_t001 - strategist review accepted E0109 and authorized no further proof work
