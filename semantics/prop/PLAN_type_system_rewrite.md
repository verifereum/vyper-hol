# PLAN

## Structured Components

### C0: Stop and report ExtCall proof-boundary/design blockage
- Kind: `blocked_report`
- Risk: 2
- Work priority: 0
- Work units: 1
- Rationale: Risk 2 because no HOL proof redesign is authorized or needed: the checked evidence already establishes a proof-architecture blockage, not theorem falsehood. The remaining work is a careful task-scoped report/update that preserves the clean cheated baseline and does not overclaim completion or unprovability.
- Required for completion: yes
- Supersedes: C0, C0.1, C0.1.3, C0.1.3.1, C0.3, C0.4, C0.5, C0.6, C0.7
- Progress transition: `replacement`
- Carries progress/evidence from: E0217, E0218, TO_type_system_rewrite-20260601T220715Z_m4232_t001, TO_type_system_rewrite-20260601T220715Z_m4239_t002, TO_type_system_rewrite-20260601T220715Z_m4241_t001, TO_type_system_rewrite-20260601T220715Z_m4250_t003, TO_type_system_rewrite-20260601T220715Z_m4252_t002
- Invalidates prior progress/evidence: old C0.3 planned static-success proof, old C0.4 optional-driver continuation proof, old C0.5 nonstatic ExtCall proof, old C0.6 RawCallTarget proof, old C0.7 final no-cheat validation

#### Progress note
This replacement carries forward the completed evidence that the static prefix cleanup/prefix-error branches are build-clean, and more importantly the accepted E0218 blocked report based on E0217. It invalidates the old proof-completion frontier because those leaves depended on a proof boundary that never reached the helper-fit point and are therefore not executable under the maintainer's no-generated-prefix-reconstruction constraint.

#### Summary
- The task instruction says to stop on unexpected tooling/design/plan issues; the ExtCall static-success boundary has now been checked and is a design/proof-boundary issue.
- Do not attempt C0.3-C0.7 or any proof work under the old ExtCall decomposition; those leaves are superseded by this stop/report component.
- The report must say the theorem has not been shown false and evaluator/semantics definitions were not changed.
- The report must say proof completion is not valid: the focused build is only for the restored cheated baseline.
- Keep all actions inside `semantics/prop`; do not edit evaluator/semantics definitions and do not commit unrelated untracked files.
- If committing task-memory/report updates, commit unsigned (no GPG signing).

#### Description
Execute the task's stop condition rather than continuing proof search. The accepted evidence shows that the allowed linear ExtCall proof did not materialize: splitting from the current static-success Resume boundary fans out into multiple generated-prefix goals before a concrete `run_ext_call` success continuation is available. Continuing would require solving generated-prefix goals individually, using broad `simp`/`gvs`/`AllCaseEqs()`, or reconstructing the optional-driver premise from the top-level generated context, all of which are explicitly forbidden by the maintainer clarification and previous PLAN guidance. The correct terminal action is to update task-local state/plan notes if needed, verify the source remains restored/build-clean only as baseline evidence, and report blocked/design-stop to the user/maintainer.

#### Statement
Task-scoped terminal obligation: report that the type-system rewrite proof is blocked at the ExtCall static-success proof boundary under the current maintainer constraints. Do not claim `eval_all_type_sound_mutual[Expr_Call_ExtCall]` is false; do not claim task proof completion; do not continue proof attempts from the stale C0 subtree.

#### Approach
First confirm the working tree/source status if the executor needs current evidence, but do not run exploratory proof edits. The report should cite E0217/E0218 and the no-frontier query-plan evidence: E0217 showed the planned split produced 9 input goals and a huge generated optional-driver prefix before helper fit; E0218 accepted the blocked-report closure and verified the source was restored to a clean focused build of the cheated baseline. If updating `STATE_type_system_rewrite.md` or `TYPE_SYSTEM_REWRITE_PLAN.md`, keep the update concise and scoped to `semantics/prop`, then commit only relevant tracked task-local changes without GPG signing.

#### Not to try
Do not retry the straight-line `Cases_on run_ext_call` / `PairCases_on result` / `rename1 SOME result` probe from the current Resume boundary; it already failed before helper matching. Do not solve the generated-prefix goals one by one, do not use broad `simp`/`gvs`/`AllCaseEqs()` to recover the optional-driver IH, and do not introduce long generated-prefix adapter theorems. Do not begin old ready-looking siblings C0.3-C0.7; they were predicated on the now-invalid boundary design. Do not report semantic unprovability, because no counterexample was checked.
