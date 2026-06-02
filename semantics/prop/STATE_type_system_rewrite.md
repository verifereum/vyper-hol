# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/STATE_type_system_rewrite.md
- next_action: Do not edit source, begin descendants, or run proof builds unless the next user/maintainer prompt explicitly approves a new static ExtCall proof architecture or changed scope. First run git status --short and query_plan(). If no explicit approval exists and query_plan still has no frontier, optionally run holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300) only to confirm the PLAN gate, then call end_session(outcome='blocked', blocked_kind='external_precondition') rather than handing off again. If explicit approval exists, call plan_oracle to replace/decompose C0 into low-risk beginable probes before any proof edit/build.
- expected_goal_shape: No HOL proof goal is authorized under the current PLAN. query_plan reports high-risk C0/C0.2/C0.2.1/C0.2.1.3/C0.2.1.3.3, no scheduled leaf frontier, no beginable component, and no Oracle next. holbuild is expected to be PLAN-gated blocked, not to expose a source proof goal. The required static ExtCall Resume remains an intentional cheat.
- verify_with: Without new approval: git status --short; query_plan(); holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300) only as confirmation of the risk gate. With new approval: git status --short; query_plan(); plan_oracle replacement/decomposition for C0; begin the scheduled low-risk frontier; then holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300).

## If This Fails
- If query_plan still has no frontier and no new approval exists, call end_session(outcome='blocked', blocked_kind='external_precondition') with query_plan/holbuild evidence. If a new plan creates a beginable low-risk leaf but proof work becomes non-straightforward, record checkpoint_progress for partial probe evidence or close_component only for terminal proved/stuck/abandoned outcome, then escalate to plan_oracle.

## Do Not Retry
- Prove static ExtCall by deriving the compact driver premise from generated driver_ih using mp_tac driver_ih >> simp[], broad gvs, AllCaseEqs(), drule_all, metis_tac, or a long generated-prefix adapter theorem.: Accepted evidence shows this path times out or requires forbidden broad generated-prefix plumbing, violating both the PLAN guard and maintainer clarification that only straightforward branch-local proof is allowed.
  - evidence: episode:E0149
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3166_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3090_t001
- Choose ready-looking descendants such as nonstatic ExtCall, RawCallTarget, wrapper, or final zero-cheat audit while static ExtCall remains intentionally cheated.: C0 is required for completion and is high-risk blocked with no scheduled frontier; downstream work cannot make the task complete while the required static ExtCall Resume is cheated.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3189_t002
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3166_t001
- Treat a successful holbuild on the cheated baseline as proof completion or zero-cheat cleanliness.: Proof integrity requires no cheats/oracles; prior success was on an intentional-cheat baseline, and current holbuild is blocked by the PLAN risk gate.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3137_t004
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3138_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3190_t001
- Stage or commit semantics/prop/LEARNINGS_type_system_rewrite.legacy.md or semantics/prop/tmp_helper.txt.: They are known pre-existing untracked artifacts outside stable task progress; commits should stage only relevant tracked task-local files and use --no-gpg-sign.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3189_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3172_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not yet authorized: change the static ExtCall proof boundary so the optional-driver premise is produced by a branch-local continuation theorem, adjusted suspension/mutual theorem interface, or another proof-architecture boundary inside semantics/prop before the generated ExtCall prefix is introduced.
- Current efforts were optimizing the wrong level: the static ExtCall Resume consumer proof, where the generated optional-driver IH is not exposed in a straightforward usable form after the concrete success branch is reached.
- The PLAN decomposition is not executable despite many ready-looking descendants; C0 is a high-risk blocked_task_gate and there is no scheduled/frontier leaf.
- Do not retry tactics when the needed change is a maintainer-approved helper/boundary, induction/suspension interface change, or changed task contract.
- A fresh expert should question first how the optional-driver IH/premise is made available at the single concrete ExtCall success continuation, not which simp/gvs variant can recover it from the full generated prefix.

### What Went Wrong
- The maintainer-authorized careful branch-by-branch attempt had already been incorporated into PLAN/STATE and still reached the generated optional-driver IH mismatch; completing it would require forbidden broad generated-prefix simplification, AllCaseEqs cleanup, or long adapter plumbing.
- The task requires zero reachable cheats, but static ExtCall remains an explicit intentional cheat; prior target success was only on that intentional-cheat baseline, not proof completion.
- This fresh session followed the cursor: git status, query_plan, and holbuild were run. query_plan showed no frontier; holbuild was blocked by the PLAN risk gate. No proof/source edits were made.
- There are modified task-memory files from handoff/state rendering and known untracked semantics/prop/LEARNINGS_type_system_rewrite.legacy.md and semantics/prop/tmp_helper.txt; do not stage the untracked legacy/tmp artifacts.

### Ignored Signals
- Ready-looking descendants under C0 are not beginable while high-risk C0 ancestors have no scheduled frontier.
- A PLAN-gated holbuild block is not a HOL proof failure to tactic around; it is the enforced proof-architecture gate.
- The user's 'stop if not straightforward' instruction dominates the temptation to continue downstream nonstatic ExtCall, RawCallTarget, wrapper, or zero-cheat audit leaves.
- Previous holbuild success with an intentional cheat cannot satisfy proof integrity or justify completion.

### Strategy Adjustments
- Next session should only proceed with proof work if the user/maintainer explicitly approves a new static ExtCall architecture or changed scope; otherwise report blocked rather than another handoff.
- If unblocked, ask plan_oracle to replace/decompose C0 into low-risk probes before editing; do not locally invent a new decomposition.
- Future proof architecture should make the optional-driver premise available after reaching one concrete ExtCall success-continuation branch and avoid recovering it by broad simplification of the generated prefix.
- Keep commits unsigned with git commit --no-gpg-sign; stage only relevant tracked files under semantics/prop and never git add -A.

### Oracle Feedback
- Held: strategist reclassified C0 as terminally blocked under the current contract, not complete and not mathematically disproved.
- Held: the blocker is proof architecture around generated optional-driver IH recovery, not a missing local tactic.
- Held: downstream leaves are not authorized while the required static ExtCall cheat remains.
- Missed/legacy reality to remember: query_plan still lists many ready descendants, but they are invalidated as executable work by the blocked C0 gate and no-frontier schedule.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3189_t001 - latest git status: task-memory modifications plus known untracked legacy/tmp artifacts
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3189_t002 - latest query_plan: high-risk C0 chain, no scheduled leaf frontier, no beginable component, no Oracle next
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3190_t001 - latest holbuild blocked by PLAN high-risk/no-frontier gate
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3192_t001 - STATE reviewed for cursor/do-not-retry/reflection
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3192_t002 - dossier confirms E0155 stop-state and earlier stuck/wrong-statement history
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3192_t003 - handoff query_plan reconfirmed same no-frontier high-risk gate
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3166_t001 - strategist replacement/reaffirmation: C0 terminal blocked_task_gate, no authorized proof frontier
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3138_t001 - source audit evidence that static ExtCall Resume remains an explicit cheat
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3137_t004 - prior target build succeeded only on intentional-cheat baseline
- episode:E0149 - direct branch-by-branch attempt stuck at forbidden generated-prefix/IH recovery
- episode:E0155 - accepted source/build/status audit of static ExtCall stop-state
