# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit, build, or prove under the current PLAN. First query_plan to confirm C0 remains done with no frontier. If there is no explicit maintainer/user authorization for a new ancestor-level ExtCall proof-boundary architecture or relaxation of generated-prefix restrictions, immediately report/end blocked rather than handoff-looping. If such authorization is present, call plan_oracle(mode="replace", component_id="C0", planning_reason="new ExtCall architecture after terminal blocked-report closure") before any source edit or build.
- expected_goal_shape: No HOL proof goal is authorized. Residual intentional cheats remain at static ExtCall success, nonstatic ExtCall result, and RawCallTarget. Known failed boundary from E0223: after the current `Cases_on run_ext_call ...` split, HOL exposes 9 generated-prefix goals and a >4KiB optional-driver-prefix implication before any compact `run_ext_call = SOME ...` success continuation is usable.
- verify_with: No verification command is currently authorized because no active/executable PLAN frontier remains; a holbuild attempt was blocked by the structured PLAN gate. If a future authorized audit/proof component is created, use holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300) for the focused target; do not treat build success as proof completion while cheats remain.

## If This Fails
- If a future authorized proof-boundary probe again yields generated-prefix fanout or a >4KiB optional-driver prefix before a compact success continuation, checkpoint/close that component with evidence and escalate to plan_oracle. Do not solve generated-prefix fanout individually. If no new authorization/PLAN frontier exists, end/report blocked status rather than another handoff.

## Do Not Retry
- Retry the current post-`Cases_on run_ext_call ...` boundary probe in `Expr_Call_ExtCall_result_static_success`.: E0223 already retried the narrowest permitted branch-boundary inspection and reproduced 9 generated-prefix goals plus a >4KiB optional-driver prefix before a compact success continuation could be used.
  - evidence: episode:E0223
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4328_t001
  - evidence: episode:E0221
- Solve generated-prefix fanout goals individually, or use broad `simp`/`gvs`/`AllCaseEqs()` over the ExtCall prefix to mine the optional-driver IH.: The maintainer clarification and terminal PLAN explicitly forbid generated-prefix reconstruction; prior probes show this is the hostile large-goal path, not a straightforward proof.
  - evidence: episode:E0223
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4328_t001
  - evidence: episode:E0217
- Begin old proof-completion leaves for static ExtCall, nonstatic ExtCall, RawCallTarget, or final zero-cheat validation under the current PLAN.: Those leaves depended on a compact static success boundary that E0223 showed absent. The current PLAN has C0 done as terminal blocked-report/status-audit and no frontier.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4392_t003
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4332_t001
- Claim completion because `vyperTypeStmtSoundnessTheory` builds.: The focused build is on a restored intentional-cheat baseline; grep confirmed residual cheats remain at the planned sites. Build success is restoration evidence only.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4347_t003
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4389_t002
- Stage or commit `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are pre-existing untracked artifacts unrelated to tracked task-local blocked-report checkpoints.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4388_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box route not yet executed: redesign or suspend the ancestor mutual proof so the optional-driver IH is generated natively inside a compact concrete ExtCall success branch, rather than extracted from the current static-success Resume boundary.
- We were optimizing helpers/tactics at the wrong boundary: projected ExtCall helpers can be semantically reasonable while the current Resume point remains too broad and exposes generated-prefix fanout before helper matching.
- The current PLAN decomposition is intentionally a terminal blocked-report/status-audit closure, not a proof-completion abstraction. A fresh expert should first ask whether the task stop condition is already satisfied, not how to patch the existing ExtCall tactic.
- Do not retry tactics where the actual need is a new proof-boundary architecture, a compact IH interface, or explicit maintainer relaxation of generated-prefix restrictions.
- Fresh expert question: can the mutual proof be refactored so the driver IH is introduced only after all concrete ExtCall prefix operations have been split/discharged, without broad generated-prefix cleanup?

### What Went Wrong
- The assumption that a careful linear branch-by-branch proof could reach a single concrete `run_ext_call SOME` success continuation at the current Resume boundary failed. E0223 reproduced 9 goals and a >4KiB generated optional-driver prefix before the compact branch was available.
- The optional-driver IH remains guarded by the full generated ExtCall monadic prefix at the current Resume boundary. Attempts needing an unconditional or compact driver IH mismatch the live proof interface.
- The requested current-state holbuild check was blocked by the structured PLAN gate because C0 is done and no executable frontier remains; rely on prior accepted C0.2 build evidence unless a new authorized component is created.
- Focused build success is only restoration evidence on an intentional-cheat baseline; residual cheats remain and proof completion is not claimed.

### Ignored Signals
- Earlier E0217/E0221 evidence already showed the same generated-prefix fanout and >4KiB goals; E0223 confirmed a known proof-boundary signal rather than revealing a local tactic gap.
- Ready-looking downstream work for static ExtCall, nonstatic ExtCall, RawCallTarget, or zero-cheat validation is unsafe without the compact static success boundary.
- A clean `vyperTypeStmtSoundnessTheory` build can coexist with intentional cheats and must not be treated as final proof integrity.
- The maintainer restriction forbids broad `simp`/`gvs`/`AllCaseEqs()` and generated-prefix adapter plumbing, exactly the routes the live goal shape invites.

### Strategy Adjustments
- Current next action is not another proof attempt: C0 is done as terminal blocked-report/status-audit, with no scheduled frontier. End/report blocked unless new maintainer authorization changes the task contract.
- If future proof work is authorized, the first strategist-owned component should be a small architecture/probe that demonstrates one compact concrete ExtCall success goal before helper application, not a full proof attempt.
- Keep all edits inside `semantics/prop`; do not change evaluator/semantics definitions; do not stage pre-existing untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.
- Commits must be unsigned (`git commit --no-gpg-sign`). Prior terminal status update was committed unsigned as `8ccefd66e`; current git status showed only STATE/LEARNINGS memory updates plus pre-existing untracked legacy/temp files.

### Oracle Feedback
- Held: strategist accepted E0223 as a real boundary/risk-mismatch failure under maintainer restrictions, and no downstream proof leaves should start under that decomposition.
- Held: strategist replacement made C0 a terminal blocked-report closure, not theorem completion; E0226 was reviewed and accepted with no PLAN changes.
- Held: C0.2 review accepted focused holbuild plus cheat grep as baseline restoration evidence, not proof completion.
- Operational reality: after terminal closure, a final holbuild attempt is blocked by the PLAN gate because no executable frontier remains. This is expected gate behavior, not a HOL source failure.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4392_t003 - current query_plan: C0 done, no frontier/beginable/Oracle-next
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4390_t001 - current holbuild request blocked by structured PLAN gate after no executable frontier remained
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4389_t002 - current grep confirms residual cheats at static ExtCall success, nonstatic ExtCall, and RawCallTarget sites
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4388_t001 - current git status shows only task memory modifications plus pre-existing untracked legacy/temp files
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4328_t001 - E0223 exact failure: 9 generated-prefix goals and >4KiB optional-driver prefix at current run_ext_call split
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4347_t003 - prior accepted C0.2 focused build succeeds on restored cheated baseline
- episode:E0226 - C0 closed as controlled blocked-report/status-audit, not theorem completion
