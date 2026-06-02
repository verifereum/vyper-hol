# PLAN

## Structured Components

### C0: Finish task-scoped type-system rewrite proof integrity inside semantics/prop
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The old risk-3/no-frontier decomposition is superseded by a maintainer-authorized proof-architecture repair inside `semantics/prop`: split the static ExtCall evaluator prefix linearly and create a branch-local suspended success-continuation subgoal before using the optional-driver IH. Existing ExtCall continuation helpers and RawCallTarget decomposition evidence remain useful, but the stale blocked-report ancestry must no longer schedule the proof.
- Required for completion: yes
- Supersedes: C0, C0.2, C0.2.1, C0.2.1.3, C0.2.1.3.3, C0.2.1.3.3.4
- Progress transition: `replacement`
- Carries progress/evidence from: E0122, E0123, E0130, E0132, E0142, E0145, E0146, E0150, E0155, TO_type_system_rewrite-20260601T220715Z_m3196_t001
- Invalidates prior progress/evidence: legacy high-risk/no-frontier C0/C0.2/C0.2.1/C0.2.1.3/C0.2.1.3.3 scheduling state

#### Progress note
This replacement carries forward proved helper/source-cleanup evidence, but invalidates the terminal blocked scheduling state. It does not authorize retrying the old top-level generated-prefix/IH recovery tactics; it changes the proof boundary so those tactics are unnecessary.

#### Summary
- Complete exactly the task-scoped proof-integrity obligations in `semantics/prop`, centered on `vyperTypeStmtSoundnessScript.sml`.
- First replace the static ExtCall intentional cheat by a linear prefix proof that suspends only the concrete success-continuation branch.
- Then prove that branch-local success subgoal using existing continuation helpers and the locally captured generated optional-driver IH.
- Close the nonstatic ExtCall result branch and RawCallTarget branch with the same local-tail-boundary discipline.
- Finish with a zero-cheat/build audit and unsigned commit of relevant tracked `semantics/prop` files only.

#### Description
This subtree replaces the stale over-decomposed blocked-report chain with the current proof architecture. The old evidence remains important as a negative result: broad prefix simplification, `AllCaseEqs()` cleanup, and generated-prefix adapter theorem plumbing are not allowed. The new executable frontier begins at C0.1.

#### Approach
Execute children in priority order. C0.1 is the empirical proof-interface probe: if it cannot produce a branch-local suspended static success goal with the generated IH and concrete success-prefix facts in context, stop and escalate. If it succeeds, C0.2 discharges that exact suspended goal; the remaining leaves are standard analogous proof/refactor and audit work.

#### Not to try
Do not retry the old monolithic static ExtCall Resume proof. Do not derive the optional-driver premise from the top-level Resume context by broad `simp`/`gvs`, `AllCaseEqs()`, `drule_all`, `metis_tac`, or long generated-prefix adapter theorems. Do not edit evaluator/semantics definitions or any file outside `semantics/prop`. Do not stage known untracked legacy/tmp artifacts.

#### Argument
The static ExtCall proof should follow evaluator order rather than recover a compact premise from the whole generated prefix. Use the expression-list IH for `eval_exprs`; close expression-error and monadic error cases immediately; in the expression-success case destruct the static ExtCall argument typing to get the target address and argument-list facts. Step through `build_ext_calldata`, account-code checks, account/transient reads, `run_ext_call`, revert assertion, `update_accounts`, and `update_transient` one operation at a time. Error branches prove only `no_type_error_result`/preservation facts by local rewriting and existing preservation lemmas. In the single success-continuation branch, after the updated accounts/transient storage and return data are concrete branch variables, specialize the generated optional-driver IH only under `returnData = [] /\ IS_SOME drv`; otherwise the decode-return branch handles result typing. The branch-local `suspend`/`Resume` boundary is the mathematical interface: it preserves exactly the local prefix facts needed by `extcall_success_continuation_sound_cond_driver_ih` or `extcall_success_continuation_state_well_typed`.

#### Definition design
No evaluator or semantics definition changes are allowed. The proof interface is theorem/suspension based:
- Existing helpers `extcall_after_state_update_tail_sound_cond_driver_ih`, `extcall_success_continuation_sound_cond_driver_ih`, and `extcall_success_continuation_state_well_typed` are the intended ExtCall tail interface.
- Existing argument destructors such as the static/nonstatic ExtCall runtime-typed destructors are the prefix interface.
- The required probe is the branch-local suspended static success goal. It must contain a usable generated driver IH and concrete success-prefix facts; if not, the definition/proof boundary is still wrong.
- For RawCallTarget, use local destructors and a monadic tail boundary analogous to existing send/raw-log helper style; do not expose the whole evaluator prefix to consumers.

#### Code structure
All source edits must remain under `semantics/prop`. Put any new local helper theorem beside the existing ExtCall or RawCallTarget helper blocks in `semantics/prop/vyperTypeStmtSoundnessScript.sml`; put Resume/refactor edits at the existing `eval_all_type_sound_mutual[...]` Resume sites. HOL4 `suspend`/`Resume` inside this script is allowed as proof architecture. Validate with the target theory build when a leaf asks for it. Commit only relevant tracked `semantics/prop` files using `git commit --no-gpg-sign`; never use `git add -A` and do not stage `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.

### C0.1: Refactor static ExtCall Resume into a branch-local suspended success continuation
- Kind: `proof_architecture_probe`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: This is the de-risking step for the former blocker. It changes only proof structure and has a clear pass/fail criterion: all static ExtCall prefix/error branches are discharged, and exactly the concrete success-continuation branch is suspended with the generated optional-driver IH and concrete prefix facts in context.
- Checkpoint: yes
- Supersedes: C0.2.1.3.3, C0.2.1.3.3.4
- Progress transition: `replacement`
- Carries progress/evidence from: E0149, E0155
- Invalidates prior progress/evidence: terminal static ExtCall no-frontier scheduling status

#### Progress note
Prior failed attempts are carried forward as negative evidence identifying the bad interface. This component replaces that interface with a branch-local suspended subgoal.

#### Summary
- Edit only `semantics/prop/vyperTypeStmtSoundnessScript.sml`.
- Replace the explicit static ExtCall `cheat` with a Resume body that follows the evaluator prefix linearly.
- Close expression-error, calldata-error, missing-code, revert, and other failure branches immediately.
- At the single success-continuation branch, use `suspend "Expr_Call_ExtCall_result_static_success"` or an equivalent local name.
- Build the target theory to confirm the remaining obligation is the intended suspended success subgoal, not a broad top-level prefix goal.

#### Statement
Proof-architecture checkpoint at the existing Resume site for `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`. The Resume body must reduce all static ExtCall cases except the final success-continuation branch, which is deliberately suspended with local branch context.

#### Approach
Unfold `evaluate_def` only as needed for `Call ... (ExtCall T ...)`, then split the monadic prefix one operation at a time. Use the expression-list IH and static ExtCall argument destructors only after the expression-list success case. For failing branches, immediately close with local rewrites such as `bind_def`, `return_def`, `raise_def`, `assert_def`, and `no_type_error_result_def`; keep only one success path alive.

#### Not to try
Do not unfold/simplify the entire ExtCall prefix with `AllCaseEqs()` or broad `gvs`. Do not prove the success tail inline here. Do not instantiate the generated optional-driver IH before the concrete success-continuation branch exists.

### C0.2: Prove the branch-local static ExtCall success continuation subgoal
- Kind: `proof`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: Once C0.1 creates the correct suspended goal, the remaining proof is a standard application of existing ExtCall continuation helpers with the generated IH specialized only in the local success branch.
- Dependencies: C0.1
- Checkpoint: yes
- Supersedes: C0.2.1.3.3.1, C0.2.1.3.3.4
- Progress transition: `refinement`
- Carries progress/evidence from: E0130, E0132, E0142, E0145

#### Progress note
Carries forward the proved ExtCall continuation helpers, but refines their use site from the old top-level Resume tail to the new branch-local suspended success goal.

#### Summary
- Resume the suspended `Expr_Call_ExtCall_result_static_success` goal from C0.1.
- Prefer `extcall_success_continuation_sound_cond_driver_ih` if the full result conjunction is present.
- Use `extcall_success_continuation_state_well_typed` only when the goal is a state projection.
- Establish account/state/runtime consistency from local branch facts and existing preservation lemmas.
- Specialize the generated driver IH only under the local `returnData = [] /\ IS_SOME drv` branch.

#### Statement
The exact statement is the suspended HOL goal generated by C0.1. It should be the remaining static ExtCall success-continuation obligation from `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`, involving the final result typing/no-TypeError/state/env-consistency obligations for `Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv`.

#### Approach
First try to apply the full continuation helper; if the goal is projected, use the projection helper and close leftover conjuncts from local facts. For the conditional driver premise, assume `returnData = [] /\ IS_SOME drv`, split `drv`, and specialize the captured generated IH with the concrete updated state/result already present in the suspended context. Use `run_ext_call_accounts_well_typed` and state-update preservation facts for account/state side conditions.

#### Not to try
Do not build a generated-prefix adapter theorem. Do not use `mp_tac driver_ih >> simp[]` from a top-level unsplit context. If the suspended goal lacks a usable generated IH for `THE drv`, stop and escalate rather than adding theorem plumbing.

### C0.3: Close the nonstatic ExtCall result branch using the same linear continuation interface
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: The nonstatic branch has the same proof structure and already has nonstatic argument destructors/projected-state helper evidence. After static ExtCall is repaired, this is standard analogous work with the nonstatic amount argument and `SOME amount` external call.
- Dependencies: C0.2
- Checkpoint: yes
- Supersedes: C0.2.1.4, C0.2.2
- Progress transition: `replacement`
- Carries progress/evidence from: E0134, E0139
- Invalidates prior progress/evidence: old direct top-level nonstatic projected-helper consumer strategy

#### Progress note
Carries forward the nonstatic helper/probe evidence but replaces the direct top-level consumer strategy with the branch-local linear continuation interface validated by the static branch.

#### Summary
- Work at the existing nonstatic ExtCall Resume site in `vyperTypeStmtSoundnessScript.sml`.
- Split the nonstatic evaluator prefix linearly, mirroring the static proof after C0.1/C0.2.
- Use nonstatic runtime-typed argument destructors to expose the target address, value amount, and argument-list facts.
- Apply existing ExtCall continuation helpers only after the concrete success branch is reached.
- Close error/revert branches immediately and audit that the nonstatic ExtCall cheat is gone.

#### Statement
Close the nonstatic `eval_all_type_sound_mutual[Expr_Call_ExtCall_result...]` Resume obligation for external calls whose first runtime argument supplies the call amount, preserving the theorem's existing source statement.

#### Approach
Use the static proof as a template but account for the nonstatic value/amount argument. Keep the generated driver IH local to the success branch. Existing nonstatic projected-state/helper proofs can be copied as proof-shape guidance, but the final Resume proof should not depend on broad generated-prefix cleanup.

#### Not to try
Do not resurrect the old compact-boundary/direct-consumer plan if it requires prefix reconstruction. Do not use global `AllCaseEqs()` cleanup over the whole nonstatic ExtCall expression-call prefix.

### C0.4: Prove RawCallTarget expression-call soundness through local tail boundaries
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 3
- Work units: 0
- Rationale: RawCallTarget was already decomposed into finite local boundary obligations and is independent of the static generated-driver mismatch. The required work is standard: argument destructors, flag-dependent return typing, one monadic tail boundary, and a Resume replacement analogous to existing send/raw-log branches.
- Dependencies: C0.3
- Supersedes: C0.3, C0.4
- Progress transition: `replacement`
- Carries progress/evidence from: E0106
- Invalidates prior progress/evidence: duplicated legacy RawCallTarget component split

#### Progress note
This flattened RawCallTarget parent consolidates the duplicate C0.3/C0.4 plans from the stale subtree and keeps only the durable semantic obligations.

#### Summary
- Add/retain RawCallTarget argument destructors matching the Resume use site.
- Prove flag-dependent return value typing for `raw_call` result shapes.
- Package account/transient updates, no-TypeError, and result typing in one monadic tail boundary.
- Replace the RawCallTarget Resume body with prefix split plus boundary-helper application.
- Build/audit locally before the final zero-cheat audit.

#### Description
This parent owns the RawCallTarget proof work after ExtCall is fixed. The child helpers should make the final Resume proof boring: the consumer should not unfold the whole raw-call tail repeatedly.

#### Approach
Prove children in order. Use existing send/raw-log helper statements as interface models, but phrase conclusions to match the RawCallTarget Resume goal directly via `irule`/`drule`. The final Resume proof should expose typed arguments, split the monadic prefix to the tail, and apply the tail boundary.

#### Not to try
Do not prove RawCallTarget by a large inline monadic proof at the Resume site. Do not duplicate helper families with slightly different conclusions; if the use site does not match, adjust the boundary statement before proceeding.

#### Argument
RawCallTarget soundness is a finite branch proof, not an induction/driver-IH problem. Well-typedness constrains the runtime argument list and flag-dependent return shape. The evaluator tail can only raise explicit runtime/assertion errors or return a value whose type is determined by `raw_call` flags; account/transient mutations preserve account and state typing via existing preservation lemmas. Packaging these facts in a tail boundary lets the Resume proof focus on evaluator prefix alignment.

#### Definition design
No definitions change. The boundary interface should expose: (1) RawCallTarget runtime argument inversion, (2) return-value typing by `rcf_revert_on_failure` and `rcf_max_outsize`, and (3) monadic tail soundness from concrete branch facts. Failure sign: the Resume proof repeatedly unfolds raw-call tail internals or requires manual construction of large conjunction theorems.

#### Code structure
Place RawCallTarget local helper theorems beside nearby expression-call helper blocks in `vyperTypeStmtSoundnessScript.sml`. Keep helper names RawCallTarget-specific and local unless already intended for reuse. The Resume replacement belongs at the existing RawCallTarget suspended/cheated branch site.

### C0.4.1: Derive RawCallTarget runtime argument destructors
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: This is list-shape and value-typing inversion analogous to existing send/raw-log/ExtCall destructors.
- Dependencies: C0.3
- Supersedes: C0.3.1, C0.4.1
- Progress transition: `replacement`

#### Progress note
Consolidates duplicate legacy RawCallTarget destructor leaves into one use-site-matched boundary lemma.

#### Summary
- Prove destructors for the RawCallTarget runtime argument list required by the evaluator branch.
- Conclusions should name the concrete target/value/data/default facts the Resume proof needs.
- Match existing `send_args_runtime_typed_dest`/raw-log/ExtCall destructor style.
- Keep the theorem local if no other script needs it.

#### Statement
A local theorem (or small theorem pair) destructing the RawCallTarget `exprs_runtime_typed`/well-typed-args assumptions into the concrete runtime values and typing facts needed by the RawCallTarget Resume branch. Use the exact constructor/argument names from the existing source branch.

#### Approach
Use list case analysis and simplification of the relevant runtime-typed argument definitions. Split only as far as needed to expose the target address, call data/value/default argument facts, and value typing assumptions used downstream.

#### Not to try
Do not leave the final Resume proof to destruct long nested list/typing assumptions manually. Do not formulate a generic destructor if a RawCallTarget-specific one matches the use site better.

### C0.4.2: Prove flag-dependent RawCallTarget return value typing
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 1
- Work units: 3
- Rationale: Finite case analysis over RawCallTarget flags and return-shape definitions; no generated IH or induction risk.
- Dependencies: C0.4.1
- Supersedes: C0.3.2, C0.4.2
- Progress transition: `replacement`

#### Progress note
Consolidates duplicate legacy return-typing leaves and keeps the flag case split as a reusable boundary.

#### Summary
- Prove the runtime typing of the value returned by RawCallTarget for each flag combination.
- Split on `flags.rcf_revert_on_failure` and `flags.rcf_max_outsize = 0` as required by the source definitions.
- Use existing value typing and raw-call return type well-formedness lemmas if visible.
- Phrase the conclusion so the tail boundary can consume it directly.

#### Statement
A local theorem giving the `expr_result_typed`/`value_runtime_typed` fact for the RawCallTarget return value under the well-typed RawCallTarget flag/return-type assumptions present in the Resume branch.

#### Approach
Perform finite case splits over the relevant RawCallTarget flags, then simplify the return-value constructors and value typing definitions. Keep hypotheses close to the branch context; avoid proving a more abstract theorem that later requires manual instantiation.

#### Not to try
Do not solve this by a huge `metis_tac` over all value-typing definitions. If the theorem is hard to apply later, strengthen/reshape its conclusion before continuing.

### C0.4.3: Prove RawCallTarget monadic tail soundness boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: This packages the missing interface identified by prior work: side-effect preservation, no-TypeError, and result typing for the already-split RawCallTarget tail from concrete branch facts.
- Dependencies: C0.4.2
- Checkpoint: yes
- Supersedes: C0.3.3, C0.4.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0106

#### Progress note
Carries forward the diagnosis that RawCallTarget needs a tail boundary, but replaces duplicate legacy components with a single use-site-matched helper.

#### Summary
- Prove one tail helper for the RawCallTarget monadic operations after arguments are known.
- Inputs should be concrete branch facts, account/state well-typedness, and the destructor facts from C0.4.1.
- Outputs should cover no-TypeError, state/account preservation, and result typing needed by the Resume branch.
- Use C0.4.2 for return value typing and existing account/transient preservation lemmas for state side effects.

#### Statement
A local RawCallTarget tail-soundness theorem whose hypotheses match the concrete post-argument-split branch facts and whose conclusion matches the final conjunction/projection required by the RawCallTarget Resume proof.

#### Approach
Split the raw-call monadic tail one operation at a time. Close error branches with local `no_type_error_result_def` rewriting, use existing account/transient preservation lemmas after updates, and use C0.4.2 for the success result shape. Keep the theorem consumer-oriented: the final Resume proof should apply it without reconstructing a large prefix.

#### Not to try
Do not put this entire proof inline in the Resume. Do not require the final consumer to manually assemble a theorem with `MATCH_MP`/`CONJ` plumbing.

### C0.4.4: Replace RawCallTarget Resume body with boundary-helper proof
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 3
- Work units: 3
- Rationale: With the RawCallTarget boundary lemmas available, the Resume proof is standard prefix splitting plus helper application analogous to nearby expression-call branches.
- Dependencies: C0.4.3
- Checkpoint: yes
- Supersedes: C0.3.4, C0.3.5, C0.4.4
- Progress transition: `replacement`
- Invalidates prior progress/evidence: legacy duplicated RawCallTarget audit leaf

#### Progress note
Combines final proof replacement and local audit for RawCallTarget because the boundary lemmas should make the build check mechanical.

#### Summary
- Edit the existing RawCallTarget Resume/cheat site only.
- Split the evaluator prefix to the concrete RawCallTarget tail.
- Use C0.4.1 destructors and C0.4.3 tail boundary; avoid repeated tail unfolding.
- Build the target theory and verify the RawCallTarget cheat/suspension is removed.

#### Statement
Close the existing RawCallTarget expression-call soundness Resume obligation in `eval_all_type_sound_mutual`, preserving the theorem's source statement.

#### Approach
Follow surrounding successful expression-call Resume proofs. After expression-list success and well-typed-branch inversion, invoke the RawCallTarget destructors and then the tail boundary. Error branches should close immediately by no-TypeError rewrites or existing IH/preservation facts.

#### Not to try
Do not leave stale `suspend`/`cheat` artifacts around RawCallTarget after the proof builds. Do not stage unrelated task-memory or untracked artifacts with the proof edit.

### C0.5: Task-scoped proof-integrity audit and unsigned commit
- Kind: `integration_validation`
- Risk: 1
- Work priority: 4
- Work units: 2
- Rationale: After proof leaves are complete, validation and commit hygiene are mechanical and explicitly required by the task.
- Dependencies: C0.4.4
- Checkpoint: yes
- Supersedes: C0.5
- Progress transition: `refinement`
- Carries progress/evidence from: E0155

#### Progress note
Carries forward the known source/status audit constraints, but now audits the post-proof source rather than the intentional-cheat baseline.

#### Summary
- Run the task-scoped build for `vyperTypeStmtSoundnessTheory`.
- Audit `semantics/prop` for remaining reachable `cheat`/intentional suspension in the task-scoped obligations.
- Check `git status --short` and stage only relevant tracked files under `semantics/prop`.
- Commit with `git commit --no-gpg-sign`; do not GPG sign.
- Do not stage known untracked legacy/tmp files.

#### Statement
Validation checkpoint: target theory builds; task-scoped cheats for static ExtCall, nonstatic ExtCall, and RawCallTarget are gone; relevant tracked `semantics/prop` changes are committed unsigned.

#### Approach
Use grep/source audit plus the target build. If any remaining cheat is outside the task scope, note it but do not plan a repository-wide cleanup. If the build or audit exposes a new non-straightforward proof issue, stop and escalate rather than broadening the task.

#### Not to try
Do not treat a build on an intentional-cheat baseline as success. Do not edit or commit files outside `semantics/prop`. Do not use signed commits or commands that might prompt for GPG credentials.
