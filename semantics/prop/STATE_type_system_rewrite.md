# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Run git status and query_plan. If C0 still shows Risk 4 BLOCKED with no scheduled frontier, no Beginable now, no Oracle next, and no maintainer/operator-approved replacement ExtCall proof-boundary architecture has been supplied, do not edit or build; report end_session(outcome='blocked', blocked_kind='external_precondition') with the git/query_plan evidence. If a new approved architecture is supplied, call plan_oracle(mode='replace', component_id='C0') with that design plus E0199/E0200 evidence, then begin only the resulting scheduled low-risk leaf before any edit/build.
- expected_goal_shape: No HOL goal should be active. Current PLAN is a single blocked C0 proof-boundary gate: no scheduled frontier, no Beginable now, no Oracle next. Source is stable/buildable only with intentional ExtCall cheat(s); unresolved boundary is static ExtCall success / optional-driver IH production.
- verify_with: Do not run holbuild until a replacement C0 plan authorizes a low-risk beginable component. Last known relevant verification remains holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300) with intentional ExtCall cheat(s).

## If This Fails
- If query_plan exposes old downstream components beginable (C0.2.3.2.3, C0.2.3.3, C0.3, C0.4.*, C0.5), treat it as PLAN/scheduler regression and either call plan_oracle(mode='replace', component_id='C0') with the evidence or report end_session(outcome='blocked'); do not begin them. If a newly authorized replacement low-risk component later fails, checkpoint_progress for useful partial evidence or close_component(result='stuck') only for a terminal proof-boundary failure.

## Do Not Retry
- Begin old downstream components such as C0.2.3.2.3, C0.2.3.3, C0.3, C0.4.*, or C0.5 while C0 is a blocked proof-boundary gate.: The latest PLAN replacement invalidates their ready/frontier status; query_plan shows no beginable frontier. Starting them would bypass the unresolved ExtCall static driver-tail boundary and violate the user stop condition.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3966_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4016_t002
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4018_t003
- Directly prove compact static_driver_ih from generated_driver_ih using asm "generated_driver_ih" irule after branch isolation.: It failed with no match in the isolated concrete static success branch; this is a proof-interface mismatch, not a missing rewrite.
  - evidence: episode:E0200
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3864_t001
- Assert a concrete generated-prefix conjunction and forward-chain/specialize generated_driver_ih.: Branch-local forward chaining failed and still amounts to brittle generated-prefix reconstruction, which maintainer guidance forbids as the proof architecture.
  - evidence: episode:E0200
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3879_t001
- Use asm "generated_driver_ih" mp_tac >> simp[] or broad gvs/AllCaseEqs() over the ExtCall generated prefix.: This timed out under the fixed tactic timeout and violates the maintainer restriction against broad generated-prefix traversal.
  - evidence: episode:E0200
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3882_t001
- Stabilize by putting cheat or RESUME_TAC >> cheat only inside Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_driver_tail].: Finalise still reported no resumption proof. The stable baseline was achieved only by replacing the original suspend point with a local intentional cheat and removing the orphan Resume.
  - evidence: episode:E0201
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3921_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3923_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box route still open: refactor the mutual proof/suspend boundary inside semantics/prop so the optional-driver recursive IH is produced natively as a compact branch-local assumption instead of reconstructed from the generated monadic ExtCall prefix.
- A fresh expert should first question whether the current theorem/suspend boundary is the wrong abstraction. The consumer helper appears usable if a compact driver IH exists; the missing producer boundary is the blocker.
- Do not optimize local tactics around generated_driver_ih. E0200 shows a proof-interface mismatch, not a missing rewrite, argument-order issue, or local simplification gap.
- Question whether eval_all_type_sound_mutual[Expr_Call_ExtCall] should be split at a different proof boundary before optional-driver evaluation, instead of mining an IH after the full ExtCall prefix is generated.
- Do not treat blocked status as a reason for another handoff loop: the next session must execute the cursor action, either reporting the external-precondition block again or replanning from a supplied maintainer-approved architecture.

### What Went Wrong
- E0199 isolated the concrete static ExtCall driver-success branch, but exact prefix facts still did not make the generated optional-driver IH directly usable.
- E0200 disproved the Risk-2 assumption that compact static_driver_ih production was straightforward: direct irule, exact-prefix forward chaining, and local mp_tac >> simp[] all failed or timed out.
- E0201 restored a stable source baseline only by replacing the original static driver-tail suspend point with an intentional local cheat; putting cheat only inside the Resume body failed Finalise.
- After E0203 the scheduler previously exposed old downstream Risk-2 leaves despite their unresolved proof-boundary dependency; the latest C0 replacement repaired that by making C0 a single blocked gate with no frontier.
- This session followed STATE: git status showed only task-memory changes and known untracked semantics/prop artifacts; query_plan again showed C0 Risk 4 BLOCKED with no frontier, no Beginable now, no Oracle next; end_session(blocked) was accepted. No proof edits/builds were made.

### Ignored Signals
- The old component text already said downstream work must not start while the static driver-tail boundary was unresolved; any downstream frontier was a scheduler/PLAN inconsistency needing semantic review, not mechanical obedience.
- Repeated failures around generated_driver_ih were not missing simp lemmas; they were proof-boundary evidence.
- The task instruction says to stop on unexpected design/plan problems and expects straightforward proof only; continuing downstream integration would violate that instruction.
- The maintainer clarification allows only careful linear ExtCall proof work and explicitly forbids broad generated-prefix reconstruction; E0200 hit exactly the forbidden/generated-prefix traversal shape.

### Strategy Adjustments
- Next session should query PLAN before any build/edit and obey the no-frontier state unless a maintainer-approved replacement architecture exists.
- A replacement architecture should expose the optional-driver IH natively or otherwise avoid broad generated-prefix reconstruction; reject long generated-prefix adapters unless explicitly authorized by the maintainer/operator.
- Keep all edits inside semantics/prop; do not change evaluator/semantics definitions; commits must use git commit --no-gpg-sign.
- Known artifacts semantics/prop/LEARNINGS_type_system_rewrite.legacy.md and semantics/prop/tmp_helper.txt should not be staged unless the operator explicitly requests it.
- If a new C0 plan becomes executable, begin only the scheduled low-risk leaf and stop again on any non-straightforward proof/design/tooling issue.

### Oracle Feedback
- Latest strategist insight held: replacing C0 with a single blocked proof-boundary gate fixed the prior scheduler contradiction; current query_plan again shows no frontier, no Beginable now, and no Oracle next.
- Earlier strategist/scheduler state missed reality: after the terminal report, old downstream Risk-2 leaves remained schedulable despite absent prerequisites.
- The preserved useful evidence is E0199 branch isolation plus E0200 interface failure; old low-risk leaves are invalidated as current work, not as historical evidence.
- The current blocked status is an external precondition/operator-design blocker, not a theorem falsehood claim and not a request to continue proof search.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4016_t001 - fresh-session git status: only task-memory changes and known untracked semantics/prop artifacts
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4016_t002 - fresh-session query_plan before blocked end_session: C0 Risk 4 BLOCKED, no frontier, no Beginable now, no Oracle next
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4018_t003 - handoff query_plan reconfirmed blocked C0/no frontier
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4018_t001 - STATE cursor/do-not-retry/reflection reviewed in handoff mode
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4018_t002 - latest C0 dossier summary confirms E0199 branch isolation, E0200 interface blocker, E0201 cheated stable baseline, E0203 report leaf
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3966_t001 - strategist replacement of C0 with a single blocked ExtCall proof-boundary gate
- episode:E0199 - isolated concrete static ExtCall driver-success branch with generated_driver_ih and exact prefix facts
- episode:E0200 - compact optional-driver IH producer failed after branch isolation; direct matching/forward chaining/broad simplification ruled out
- episode:E0201 - source stabilized with intentional local ExtCall cheat after Resume-body cheat attempts failed Finalise
- episode:E0203 - terminal report leaf for static ExtCall driver-tail blocker accepted as report evidence
