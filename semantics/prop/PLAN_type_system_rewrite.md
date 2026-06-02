# PLAN

## Structured Components

### C0: Finish task-scoped type-system rewrite proof integrity inside semantics/prop
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: All executable leaves in this subtree are now risk 1-2 and the static ExtCall gate is encoded by direct leaf dependencies. The old parent risk-3 rationale was stale evidence from before the maintainer clarification and before the C0.2 proof-interface replacement; it no longer describes the current source/PLAN obligations.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0, C0.1, C0.2, E0156, E0159, E0161
- Invalidates prior progress/evidence: stale C0 risk-3 rationale, frontier ordering from TO_type_system_rewrite-20260601T220715Z_m3369_t001

#### Progress note
This is a scheduling/frontier repair only. It carries forward the branch-local ExtCall suspension work, the proved static projected helper, and the C0.2 replacement insight, while invalidating the erroneous frontier that authorized C0.4.1 before C0.2.2/C0.2.3.

#### Summary
- Complete only the task-scoped type-system rewrite proof obligations under `semantics/prop`.
- Static ExtCall success is the immediate gate: prove the tiny option helper if needed, then replace the static-success Resume cheat.
- Nonstatic ExtCall and RawCallTarget work must wait until the static-success Resume is clean.
- Do not edit evaluator/semantics definitions or files outside `semantics/prop`.
- Commit only after clean `holbuild`, using `git commit --no-gpg-sign`.

#### Argument
The task remains a branch-by-branch type-soundness cleanup. The key sequencing invariant is that the static ExtCall success proof validates the generated optional-driver premise interface before any downstream ExtCall/RawCallTarget work begins. Once the static success Resume is proved, the nonstatic ExtCall branch may reuse the same linear continuation discipline; only after that should RawCallTarget local tail boundaries and Resume replacement be attempted. The frontier repair encodes this invariant at the leaf-dependency level, because the scheduler exposed that parent-level intended ordering was insufficient.

#### Definition design
No evaluator or semantics definition changes are allowed. Proof architecture refactoring inside `semantics/prop` is allowed only to create small boundary facts that avoid broad simplification in enormous generated contexts. In particular, use tiny option-typing and tail-soundness boundaries; do not introduce long generated-prefix adapter theorems or recover premises by global `gvs`/`AllCaseEqs()` cleanup.

#### Code structure
All proof edits belong in `semantics/prop/vyperTypeStmtSoundnessScript.sml` and task state/plan notes under `semantics/prop`. Keep the already proved static projected helper in place, but it is no longer an executable PLAN leaf. Replace cheats only for the scoped Resumes named by this subtree. Validate with `holbuild` for `vyperTypeStmtSoundnessTheory`; when committing, stage only relevant tracked `semantics/prop` files and use `--no-gpg-sign`.

### C0.1: Refactor static ExtCall Resume into a branch-local suspended success continuation
- Kind: `proof_architecture_probe`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Already completed by E0156. It remains the structural basis for the current static ExtCall proof shape and imposes no remaining executor work.
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1, E0156

#### Progress note
Carry forward completed checkpoint evidence; no new scheduling work is intended.

#### Summary
Completed checkpoint. Static ExtCall prefix/error branch structure was isolated enough to make the success continuation the active focus. Keep the resulting source structure unless a build failure specifically implicates it.

#### Approach
No action unless the source unexpectedly no longer builds before the active static-success Resume. If audited, preserve the branch-local suspension/refactor shape and do not restart older prefix-replay strategies.

#### Not to try
Do not reopen the old broad linear proof attempt that timed out before the maintainer clarification and C0.2 replacement.

### C0.2: Finish static ExtCall success by using generated driver premise at the concrete tail
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The executable static gate is now represented by two leaves: a mechanical option-typing helper and the direct static-success Resume proof. The completed projected helper is carried in the parent notes rather than queued as work, so the next beginable leaf is C0.2.2.
- Dependencies: C0.1
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2, C0.2.1, E0159, E0161, TO_type_system_rewrite-20260601T220715Z_m3320_t001, TO_type_system_rewrite-20260601T220715Z_m3326_t001
- Invalidates prior progress/evidence: old C0.2.2 standalone-premise obligation, old C0.2.3 dependency split, queued C0.2.1 executable leaf

#### Progress note
C0.2.1's proved `extcall_static_projected_sound` source progress is still valid and should be kept, but it is removed as an executable child because it is already done and was corrupting the frontier. The remaining work starts at C0.2.2.

#### Summary
- Static ExtCall success remains the immediate proof gate.
- The already proved static projected helper is carried forward as source evidence, not scheduled work.
- First add/reuse only the tiny option-typing helper if needed.
- Then replace `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` by a direct projection proof.
- Consume the generated optional-driver premise at the concrete success tail, not as a standalone subgoal.

#### Description
This subtree implements the maintainer-approved static ExtCall unblock. It replaces the failed expectation of a freestanding generated-driver premise with a direct projection proof where the premise is named and applied only after the concrete ExtCall prefix facts are available. It stays inside `semantics/prop` and does not change evaluator definitions.

#### Approach
Use `RESUME_TAC` only to expose the projection goals and assumptions. Name the generated prefix implication assumption, split the ExtCall prefix linearly one monadic operation at a time, close error branches immediately, and keep only one success path active. At the success tail, instantiate the named generated premise with the concrete prefix facts and pass the resulting conditional driver IH to the existing conditional tail helper.

#### Not to try
Do not schedule or redo the proved static projected helper. Do not use `RESUME_TAC >- (...)` expecting a standalone driver-premise goal; E0161 shows that branch is a projection goal. Do not simplify the whole generated prefix with broad `gvs`, `simp[Once well_typed_expr_def]`, `AllCaseEqs()`, or a generated-prefix adapter theorem.

#### Argument
After `RESUME_TAC`, the static success proof obligations are ordinary projection goals plus an assumption whose guarded conclusion is the optional-driver IH. The proof invariant is tail-local: once the prefix is split through successful calldata construction, account/code lookup, `run_ext_call`, state update, and `returnData = []`, the context contains exactly the facts needed to discharge the generated assumption's guard. Existing conditional tail lemmas then turn that conditional driver IH into the full postcondition, from which each projection follows.

#### Definition design
No definition changes. The only authorized helper at this level is a tiny option boundary such as `well_typed_opt env drv /\ IS_SOME drv ==> well_typed_expr env (THE drv)`, used to avoid unfolding `well_typed_expr_def` in a huge Resume context. Failure sign: if the proof needs to copy the whole generated prefix into a lemma statement, the interface is wrong; stop and escalate.

#### Code structure
Keep all edits in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. The already committed/proved static projected helper remains in the file. Put any option helper near the ExtCall helper block or reuse an imported helper if present. Replace only the `Expr_Call_ExtCall_result_static_success` cheat for this subtree.

### C0.2.1: Carry forward proved static ExtCall projected-soundness helper
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0159 proved the helper and E0161 did not undermine its truth. It may or may not be the final helper used by the repaired Resume proof, but the source progress is valid and should not be redone.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1, E0159, TO_type_system_rewrite-20260601T220715Z_m3320_t001, TO_type_system_rewrite-20260601T220715Z_m3326_t001

#### Progress note
This component is retained as completed source progress under the replaced C0.2 subtree.

#### Summary
- Already proved and committed as part of C0.2 progress.
- Keep the theorem in the source; do not rework it unless it blocks the repaired proof.
- It documents the ordinary-evaluator boundary for static ExtCall and may still be useful as a reference.
- No executor work remains for this leaf.

#### Approach
Audit only if a build unexpectedly fails before the active Resume. Otherwise carry forward this proof unchanged.

#### Not to try
Do not revert the targeted `rewrite_tac[Once well_typed_expr_def]` performance fix in `extcall_expr_sound_from_generated_ih`; prior evidence shows broad `simp` timed out after adding helpers.

### C0.2.2: Add or expose a tiny option-typing helper for `THE drv` if needed
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: This is a mechanical option case split and prevents the static Resume proof from unfolding expression typing in a very large context. It is the first real executable leaf after the frontier repair.
- Dependencies: C0.1
- Progress transition: `refinement`
- Carries progress/evidence from: E0161

#### Progress note
This is the same intended tiny helper from the replaced C0.2 plan, now made the first executable C0.2 leaf by removing the completed C0.2.1 evidence leaf.

#### Summary
- Next beginable component after this repair.
- Reuse an existing option-typing theorem if visible; otherwise prove a local theorem.
- Desired fact: `well_typed_opt env drv /\ IS_SOME drv ==> well_typed_expr env (THE drv)`.
- The helper must not mention ExtCall prefix facts.
- If not needed, record that the existing source/imported fact suffices and move to C0.2.3.

#### Statement
Theorem well_typed_opt_THE[local]:
  well_typed_opt env drv /\ IS_SOME drv ==> well_typed_expr env (THE drv)

#### Approach
Search locally/imports for `well_typed_opt_THE` or `well_typed_opt_SOME`. If absent, prove by `Cases_on drv`; `NONE` contradicts `IS_SOME`, and `SOME e` follows by unfolding only the option typing definition or small option theorem. Do not unfold `well_typed_expr_def` in the large static Resume context.

#### Not to try
Do not edit outside `semantics/prop`. Do not solve this by broad simplification inside `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`.

### C0.2.3: Replace static-success Resume cheat with direct projection proof consuming generated premise
- Kind: `main_proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: This is the required static ExtCall gate. E0161 confirmed the proof shape; the risk is standard if the proof obeys the linear branch discipline and uses the generated premise only at the success tail.
- Dependencies: C0.2.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2.3, E0161

#### Progress note
This is the terminal static-success proof leaf. Its completion is now the direct dependency for C0.3 and therefore gates all later work.

#### Summary
- Work only in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`.
- Start with `RESUME_TAC`, name the generated optional-driver premise assumption, and prove projection goals directly.
- Split the static ExtCall prefix one operation at a time; close error cases immediately.
- In the unique success branch, instantiate the named generated premise with concrete prefix facts.
- Apply `extcall_success_continuation_sound_cond_driver_ih` or the matching conditional tail helper and project the desired conjunct.
- End with no cheat/probe/`FAIL_TAC` and a clean `holbuild`.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]:
  (* replace cheat; close the static ExtCall success projection goals *)

#### Approach
Use the proved static helper proof as a guide for the order of monadic splits, but do not replay prefix cleanup globally. Move the whole-call evaluation equation only when needed, unfold `Once evaluate_def` and monadic combinators in controlled steps, and split the next operation only. At the success tail, derive the conditional driver IH by applying the named generated assumption to the concrete facts already in context, then feed it to the conditional continuation helper and close the projection.

#### Not to try
Do not put a tactic branch immediately after `RESUME_TAC` expecting a separate driver-premise subgoal. Do not use broad `gvs`, `AllCaseEqs()`, or broad `simp[Once well_typed_expr_def]` in the projection context. If the success-tail instantiation is not straightforward after two focused attempts, stop and escalate with the exact tail goal rather than building a long adapter theorem.

### C0.3: Close the nonstatic ExtCall result branch using the same linear continuation interface
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: This work is standard analogous ExtCall branch work, but it must not start until the static-success gate is proved. The dependency is therefore the terminal static leaf C0.2.3, not merely the parent C0.2.
- Dependencies: C0.2.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.3

#### Progress note
Dependency repaired so the scheduler cannot authorize nonstatic ExtCall work before static success is complete.

#### Summary
- Begin only after C0.2.3 is proved and reviewed.
- Use the same disciplined linear continuation interface validated by static ExtCall.
- Replace the nonstatic ExtCall result cheat without changing evaluator definitions.
- Stop if the branch is not analogous to the static proof.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  (* replace cheat using the validated ExtCall continuation interface *)

#### Approach
Reuse the successful static proof pattern: expose the branch-local assumptions, split monadic operations linearly, close errors immediately, and use the relevant continuation/tail helper at the unique success tail. Keep any nonstatic-specific return-data or state-update facts local to this Resume.

#### Not to try
Do not start this before C0.2.3. Do not invent new global ExtCall adapter theorems unless the static proof revealed a reusable small boundary that exactly matches the nonstatic tail.

### C0.4: Prove RawCallTarget expression-call soundness through local tail boundaries
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: RawCallTarget work is standard local boundary proof work, but it must remain downstream of the ExtCall gates. Every executable RawCallTarget leaf now has a direct dependency path through C0.3 so it cannot appear on the frontier early.
- Dependencies: C0.3
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4

#### Progress note
This subtree is not strategically changed; only leaf dependencies are strengthened to repair frontier ordering.

#### Summary
- RawCallTarget is later work, not the current frontier.
- Begin only after static and nonstatic ExtCall result branches are complete.
- Prove small argument/return/tail boundary lemmas before replacing the RawCallTarget Resume.
- Keep all work inside `semantics/prop` and avoid evaluator definition changes.

#### Argument
RawCallTarget soundness should be packaged through local facts: destruct the runtime argument list, prove the flag-dependent returned value type, package the monadic tail's state/no-TypeError/result-typing facts, then replace the Resume using those boundaries. This avoids entangling RawCallTarget with the generated ExtCall optional-driver issue.

#### Definition design
No RawCallTarget semantic definition changes. Boundary lemmas should expose consumer-shaped facts: list/value destructors, flag-conditioned result typing, and a monadic tail soundness theorem. Failure sign: a Resume proof repeatedly unfolds the RawCallTarget tail internals instead of applying a boundary lemma.

#### Code structure
Place RawCallTarget boundary lemmas near analogous Send/RawLog/ExtCall helper blocks in `vyperTypeStmtSoundnessScript.sml`. Replace the RawCallTarget Resume only after all local boundary lemmas build.

### C0.4.1: Derive RawCallTarget runtime argument destructors
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: List-shape and value-typing inversion analogous to existing send/raw-log/ExtCall destructors. Direct dependency on C0.3 repairs the scheduler so this cannot begin before ExtCall gates.
- Dependencies: C0.3
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.1

#### Progress note
Only dependency metadata is changed; proof content is carried forward.

#### Summary
Prove the RawCallTarget runtime argument shape facts needed by the later tail proof. This is finite destructuring over evaluated arguments and their runtime typing. Begin only after C0.3.

#### Approach
Follow the nearby Send/RawLog argument inversion style. Keep conclusions consumer-shaped for C0.4.3; avoid proving a broad conjunction if separate destructors are easier to use.

#### Not to try
Do not begin before C0.3. Do not mix the monadic tail proof into the argument destructor lemma.

### C0.4.2: Prove flag-dependent RawCallTarget return value typing
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 2
- Rationale: Finite case analysis over RawCallTarget flags and return-shape definitions. Direct dependency on C0.3 blocks premature scheduling.
- Dependencies: C0.3
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.2

#### Progress note
Only dependency metadata is changed; proof content is carried forward.

#### Summary
Prove that the RawCallTarget result value has the type required by the return flag/shape. This is local finite case analysis and feeds the monadic tail boundary.

#### Approach
Case split on the relevant RawCallTarget mode/flags and simplify the return-value construction and type relation. State the theorem so C0.4.3 can apply it without unfolding the flag logic again.

#### Not to try
Do not combine this with state preservation or no-TypeError facts; keep it as a return-typing boundary.

### C0.4.3: Prove RawCallTarget monadic tail soundness boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: Packages side-effect preservation, no-TypeError, and result typing for the already-split RawCallTarget tail. It depends on the argument and return boundaries and is downstream of C0.3.
- Dependencies: C0.4.1, C0.4.2
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.3

#### Progress note
Only dependency metadata is changed; proof content is carried forward.

#### Summary
Package the RawCallTarget tail proof behind a consumer-shaped boundary lemma. It should use C0.4.1 argument destructors and C0.4.2 return typing, and expose exactly the facts needed by the Resume replacement.

#### Approach
Assume the concrete branch facts produced by the RawCallTarget prefix split. Prove the side-effect, no-TypeError, state typing, and result typing conclusions in a form that the Resume can apply by `irule`/`drule` rather than unfolding the tail.

#### Not to try
Do not unfold the whole RawCallTarget evaluator tail in the final Resume once this boundary exists. Do not make the lemma statement depend on unrelated ExtCall generated premises.

### C0.4.4: Replace RawCallTarget Resume body with boundary-helper proof
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: With C0.4.1-C0.4.3 available, the Resume proof is standard prefix splitting plus helper application. It is sequenced last within RawCallTarget.
- Dependencies: C0.4.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.4

#### Progress note
Only dependency metadata is changed; proof content is carried forward.

#### Summary
Replace the RawCallTarget Resume cheat after all RawCallTarget boundaries are proved. Use prefix splitting only to reach the boundary-helper assumptions, then apply C0.4.3 and project the required conjuncts.

#### Approach
Mirror nearby expression-call branch proofs. Split the evaluator prefix in a controlled way, close immediate errors, use C0.4.1/C0.4.2/C0.4.3 rather than unfolding the tail, and validate with `holbuild`.

#### Not to try
Do not begin before C0.4.3. Do not re-prove argument destructuring or flag typing inline in the Resume.

### C0.5: Task-scoped proof-integrity audit and unsigned commit
- Kind: `integration_validation`
- Risk: 1
- Work priority: 40
- Work units: 1
- Rationale: Final validation and commit hygiene are mechanical after all proof leaves complete. It is now directly blocked on C0.4.4 so it cannot appear early.
- Dependencies: C0.4.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.5

#### Progress note
Dependency repaired to enforce final audit only after all proof leaves complete.

#### Summary
Run the task-scoped final build/audit only after C0.4.4. Confirm no scoped cheats/probes remain, no forbidden files were edited, and commit with `--no-gpg-sign`.

#### Approach
Run the prescribed `holbuild` target, inspect `git status`, stage only relevant tracked files under `semantics/prop`, and commit with `git commit --no-gpg-sign`. Update task state/plan notes to reflect completed proof progress.

#### Not to try
Do not stage known untracked artifacts such as legacy learnings/tmp helper files. Do not GPG-sign the commit.
