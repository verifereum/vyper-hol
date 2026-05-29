# STATE_type_system_rewrite
Updated: 2026-05-29

## Cursor
- component: C2.7
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: At next startup, run `git status --short` and `query_plan()`. If there is no operator/tooling report that holbuild/config changed and startup does not explicitly require a retest, propose `end_session(outcome="blocked", blocked_kind="tooling_bug")` citing strict-parse evidence. If tooling is reported fixed or startup explicitly requires a retest, continue active C2.7 and run exactly one focused `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)` before any source edits.
- expected_goal_shape: Currently blocked before HOL: focused holbuild exits immediately with `holbuild: unknown build option: --strict-parse`, so no HOL theorem/goal exists. If tooling recovers, expected first HOL failure remains C2.7 helper `extcall_static_args_runtime_typed_dest`: small `exprs_runtime_typed`/LIST_REL/`value_has_type`/`dest_AddressV` proof where stale proof tries `Cases_on `vs`` after broad rewriting/destruction; prior live variables included y, tv, h.
- verify_with: Only after tooling/config changed/fixed or explicit retest/startup requirement: `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)`. If it again reports `holbuild: unknown build option: --strict-parse`, verification remains blocked pre-HOL.

## If This Fails
- If focused holbuild still reports unknown option `--strict-parse`, treat as tooling_bug/pre-HOL: no source edits, no repeated builds, no plan_oracle; propose blocked end_session unless operator specifically requests another diagnostic action. If holbuild reaches HOL checking but fails outside C2.7 ExtCall/RawCallTarget coverage, call plan_oracle before editing. If it reaches `extcall_static_args_runtime_typed_dest`, patch using E1334/L1856 guidance: destruct args/value/type lists before broad `exprs_runtime_typed_def` rewriting, or consume live head facts plus `evaluate_type_def`, `value_has_type_def`, and `dest_AddressV_def`.

## Do Not Retry
- Editing HOL source while holbuild reports `unknown build option: --strict-parse`.: The failure occurs before HOL source parsing/checking; no verified proof prefix or goal exists, so source edits would be ungrounded in an inherited dirty tree.
  - evidence: tool_output:TO_type_system_rewrite-20260528T153317Z_m69700_t001
  - evidence: episode:E1347
- Treating `holbuild: unknown build option: --strict-parse` as a HOL parse/type/proof failure or proof-decomposition issue.: It is an operational holbuild option rejection before theory checking; no HOL goal is produced and no strategist proof replan is warranted solely from this failure.
  - evidence: tool_output:TO_type_system_rewrite-20260528T153317Z_m69700_t001
  - evidence: tool_output:TO_type_system_rewrite-20260528T153317Z_m69701_t002
  - evidence: episode:E1347
- Calling plan_oracle solely because the strict-parse tooling blocker persists.: PLAN remains active/valid for C2.7; the blocker is operational/tooling. Call plan_oracle only after holbuild reaches HOL and fails outside C2.7 coverage, or if a blocked proposal is rejected with proof-related instructions.
  - evidence: tool_output:TO_type_system_rewrite-20260528T153317Z_m69698_t002
  - evidence: tool_output:TO_type_system_rewrite-20260528T153317Z_m69700_t001
  - evidence: episode:E1347
- Retesting focused holbuild repeatedly in an ordinary next session without an operator report that tooling/config changed or an explicit retest/startup requirement.: The same pre-HOL strict-parse blocker has repeated across many sessions. If unchanged, the terminal action is a tooling_bug blocked proposal, not another proof/build loop.
  - evidence: tool_output:TO_type_system_rewrite-20260528T153317Z_m69701_t002
  - evidence: episode:E1345
  - evidence: episode:E1346
- Closing C2.7 merely because `vyperTypeStmtSoundnessTheory` builds cleanly after tooling recovery.: C2.7 has known build-through cheats; terminal closure requires removing both ExtCall and RawCallTarget cheats and auditing source/theory indexes for reachable cheats/oracles.
  - evidence: episode:E1333
  - evidence: tool_output:TO_type_system_rewrite-20260525T153549Z_m59966_t001
  - evidence: tool_output:TO_type_system_rewrite-20260525T153549Z_m59966_t002

## Reflection
### Tunnel Vision Check
- Outside-the-box after tooling recovery: do not force ExtCall through the existing Resume body if it grows; consider a local ExtCall tail theorem modeled on ExtCall pipeline factoring in `vyperEvalPreservesImmutablesDomScript.sml`, making the Resume a thin consumer.
- We may be optimizing the wrong local proof if ExtCall is attempted by unfolding the evaluator tail inline; a better boundary may combine account preservation, ABI return typing, driver-vs-decoded return typing, destination/value destructors, rollback/error preservation, and state/account preservation.
- The PLAN decomposition is adequate for current cheat coverage but broad for actual proof work. If the ExtCall tail proof becomes large or brittle after holbuild recovers, ask the strategist for finer C2.7 decomposition rather than tactic-thrashing.
- A fresh expert should first question the exact ExtCall tail theorem statement: static vs non-static value transfer, destination/value destructors, driver-vs-decoded return typing, ABI decode dependency/import, account/runtime preservation, rollback/error cases, and whether the tail theorem should be split before the Resume consumer.
- Do not redesign proof architecture until holbuild produces a real HOL goal; right now the gating problem is operational tooling.

### What Went Wrong
- This session followed the blocked cursor and startup request: checked git status/query_plan, began active C2.7 for scoped context, and ran one focused holbuild before edits.
- Focused holbuild again failed before HOL parsing/checking with `holbuild: unknown build option: --strict-parse`; no HOL parse/type/proof goal exists, so source edits, commits, proof tactics, or plan_oracle proof replanning would be ungrounded.
- The substantial dirty worktree remains inherited from previous sessions; this session made no source edits, no staging changes, and no commits.

### Ignored Signals
- Do not reinterpret active/beginable C2.7 as permission to edit while holbuild rejects before HOL parsing. PLAN scheduling is actionable only after verification reaches HOL theory checking.
- Do not treat `holbuild: unknown build option: --strict-parse` as a HOL parse/type/proof failure, missing lemma, theorem falsehood, or proof-decomposition issue. It is an operational option rejection and gives no proof goal.
- Do not keep retesting focused holbuild in ordinary next sessions unless tooling/config changed or the operator/startup explicitly requires a retest. This session retested only because startup explicitly requested using holbuild to check current state.
- Do not assume a future clean focused build closes C2.7; prior audit found build-through ExtCall/RawCallTarget cheats requiring proof and final audit.

### Strategy Adjustments
- Keep the next ordinary session operational: status/plan check first, then propose blocked if no tooling fix or explicit retest instruction is present.
- Do not edit source, stage, commit, build repeatedly, or call plan_oracle solely for the strict-parse blocker; it is not a proof strategy issue.
- After tooling recovery, stay scoped to C2.7 and run one focused holbuild before proof edits. If it reaches `extcall_static_args_runtime_typed_dest`, avoid destructing stale variable names after broad rewrites; use E1334/L1856 guidance.
- After ExtCall argument destructors, avoid a large inline `run_ext_call`/ABI/rollback proof in the Resume if goals grow; prefer a local ExtCall tail boundary theorem and escalate if that boundary itself becomes brittle.

### Oracle Feedback
- Structured PLAN still schedules C2.7 and reports no high-risk proof blockers; this remains useful after tooling recovery but does not override the operational holbuild blocker.
- Dossier history is consistent: repeated E1343-E1347 plus this session document the same pre-HOL strict-parse blocker, while earlier C2.7 evidence E1333/E1334 identifies the actual ExtCall/RawCallTarget frontier after tooling recovery.
- Scoped learning L1861 already captures the reusable strict-parse operational-blocker pattern, so no duplicate learning is added.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260528T153317Z_m69698_t001 - startup git status showed inherited dirty tracked/untracked worktree; no source edits made this session
- tool_output:TO_type_system_rewrite-20260528T153317Z_m69698_t002 - startup query_plan confirmed active/beginable C2.7 and no high-risk proof blockers
- tool_output:TO_type_system_rewrite-20260528T153317Z_m69699_t001 - begin_component confirmed active C2.7 and injected scoped strict-parse dossier/learning context
- tool_output:TO_type_system_rewrite-20260528T153317Z_m69700_t001 - focused holbuild in this session failed pre-HOL with `unknown build option: --strict-parse`
- tool_output:TO_type_system_rewrite-20260528T153317Z_m69701_t001 - STATE read confirms prior blocked cursor and strict-parse policy
- tool_output:TO_type_system_rewrite-20260528T153317Z_m69701_t002 - dossier query shows repeated C2.7 strict-parse blocker episodes E1343-E1347
- tool_output:TO_type_system_rewrite-20260528T153317Z_m69701_t003 - query_plan remains active/beginable C2.7 but does not override operational blocker
- episode:E1347 - latest prior C2.7 checkpoint for pre-HOL strict-parse blocker
- episode:E1334 - expected first HOL failure after tooling recovery is `extcall_static_args_runtime_typed_dest`
- episode:E1333 - prior audit found remaining C2.7 ExtCall/RawCallTarget build-through cheats requiring proof and final audit
