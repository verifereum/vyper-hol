# PLAN

## Structured Components

### C0: Terminal blocked-report closure for the ExtCall proof-boundary stop
- Kind: `blocked_report_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Risk 2 because this component is not a proof-completion obligation and no longer attempts the uncertain ExtCall/RawCallTarget proofs. The completed evidence path is documentation plus audit: E0223 showed the current static ExtCall success Resume boundary is non-straightforward under the maintainer restrictions; E0224 recorded the stop in task-local documentation/status; E0225 verified the restored cheated baseline and committed the task-local status update unsigned. Residual cheats remain by design, so this must be closed only as a controlled blocked-report subtree, not as type-soundness completion.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0, C0.1, C0.2, E0223, E0224, E0225, TO_type_system_rewrite-20260601T220715Z_m4328_t001, TO_type_system_rewrite-20260601T220715Z_m4353_t001

#### Progress note
Carry forward the accepted completed blocked-report path. C0.1 and C0.2 remain the supporting completed leaves; this parent update is only to make explicit that there is no further executable proof/audit work inside C0. The subtree is terminal for the task's stop/report obligation, while the HOL soundness theorem itself is still not completed because the residual cheats remain intentionally present.

#### Summary
- C0 is terminal as a controlled blocked-report subtree, not as proof completion.
- E0223 is accepted evidence that the current static ExtCall success proof boundary exposes 9 generated-prefix goals and a >4KiB optional-driver premise before a compact success continuation is usable.
- Maintainer restrictions forbid solving that by broad `simp`/`gvs`/`AllCaseEqs()`, generated-prefix adapter theorems, or generated-prefix theorem plumbing.
- E0224 recorded the stop in task-local documentation/status; E0225 verified the restored cheated baseline and committed the status update unsigned.
- No further C0 leaf should be begun unless the user/maintainer asks for a new ancestor-level proof-boundary architecture or relaxes the generated-prefix restrictions.
- End the session/report blocked status rather than claiming theorem completion; residual cheats remain at static ExtCall success, nonstatic ExtCall result, and RawCallTarget.

#### Description
This component covers the task-scoped residual obligations in `semantics/prop/vyperTypeStmtSoundnessScript.sml`: the static ExtCall success cheat, the nonstatic ExtCall result cheat, and the RawCallTarget cheat. They are intentionally not scheduled as proof leaves under the current decomposition because the prerequisite static ExtCall boundary failed the task's straightforward-proof requirement in E0223. The completed subtree records and audits that stop condition inside `semantics/prop`; it does not prove the final type-system soundness surface. A future proof attempt would require a genuinely different ancestor-level proof-boundary design inside `semantics/prop` or explicit maintainer relaxation of the generated-prefix restrictions.

#### Statement
Terminal status obligation: the task-scoped C0 work is complete only as a blocked-report/status-audit closure. Under the current `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` Resume boundary and maintainer restrictions, the residual statement-expression soundness proof obligations remain incomplete. The theorem is not shown false, but the current proof architecture is not straightforward and exposes forbidden generated-prefix reconstruction before the optional-driver IH can be specialized in a compact success branch.

#### Approach
Do not edit/build/prove as a new C0 action. Preserve the completed C0.1/C0.2 evidence: E0224 documented the accepted E0223 boundary stop, and E0225 checked that the restored cheated baseline builds and that the status update was committed with `--no-gpg-sign`. The executor's next valid action is to end/report the session with outcome reflecting controlled blocked-report completion, explicitly stating that proof completion is not claimed.

#### Not to try
Do not add another proof leaf for static ExtCall, nonstatic ExtCall, RawCallTarget, or zero-cheat validation under this C0 plan. Do not retry the post-`Cases_on run_ext_call ...` boundary probe, solve the 9 generated-prefix goals individually, use broad `simp`/`gvs`/`AllCaseEqs()` over the ExtCall prefix, or introduce a long generated-prefix adapter theorem. Do not claim final theorem completion merely because `vyperTypeStmtSoundnessTheory` builds on the restored intentional-cheat baseline.

#### Argument
The mathematical/proof-architecture argument for this subtree is negative and task-scoped: the current mutual-proof Resume boundary does not supply the optional-driver IH in a compact concrete ExtCall success-continuation branch. Instead, E0223 shows that even the minimal permitted split after `run_ext_call` leaves a large generated implication containing the full ExtCall monadic prefix and multiple goals. Since the maintainer specifically forbids broad prefix cleanup or generated-prefix adapter theorem plumbing, the proof is not straightforward under the current architecture. Therefore the correct task action is not to prove downstream residual branches, but to record the boundary failure and audit that the source is restored to the intentional cheated baseline.

#### Definition design
No evaluator/type-system definition changes are authorized or needed for this terminal blocked-report subtree. The relevant interface failure is at the proof boundary, not a new low-risk helper definition: consumers need a branch-local compact optional-driver IH after the concrete ExtCall success path has discharged prefix operations, but the current Resume point exposes a generated prefix before that interface is available. Future proof work, if reauthorized, should begin with a strategist-owned ancestor-level boundary design/probe demonstrating such a compact success goal; it should not start by adding tactical adapter lemmas for the generated prefix.

#### Code structure
Keep all files inside `semantics/prop`; do not edit evaluator/semantics definitions or files outside the task scope. The completed status path updated task-local documentation/state and audited `vyperTypeStmtSoundnessTheory` on the restored intentional-cheat baseline. Do not stage pre-existing untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`; if any future task-local documentation changes are explicitly requested, commit them with `git commit --no-gpg-sign`.
