# PLAN

## Structured Components

### C0: Complete the ExtCall branch of `eval_all_type_sound_mutual` under the clarified linear-proof discipline
- Kind: `proof_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Risk 2 because the source already contains proved branch helpers (`extcall_static_projected_sound`, `extcall_static_projected_state_well_typed`, `run_ext_call_accounts_well_typed`) and the maintainer has authorized exactly the missing proof-architecture refactoring inside `semantics/prop`. The subtree is decomposed so the first substantive proof step is only a boundary probe; if it recreates generated-prefix fanout, the executor must stop rather than continue.
- Required for completion: yes
- Supersedes: C0, E0218, E0219
- Progress transition: `replacement`
- Carries progress/evidence from: TO_type_system_rewrite-20260601T220715Z_m4232_t001, TO_type_system_rewrite-20260601T220715Z_m4253_t001, TO_type_system_rewrite-20260601T220715Z_m4261_t001, TO_type_system_rewrite-20260601T220715Z_m4274_t002, TO_type_system_rewrite-20260601T220715Z_m4276_t001
- Invalidates prior progress/evidence: prior terminal C0 blocked_report as a no-frontier stop gate

#### Progress note
This replacement does not discard the old proof evidence; it reclassifies it as boundary-risk guidance. The old terminal report was correct before fresh authorization, but it no longer represents the executable plan because the user/maintainer now explicitly asks for continued proof work under a narrowed ExtCall discipline.

#### Summary
- Replace the terminal no-frontier C0 with a fresh, task-scoped ExtCall proof-completion subtree.
- Work only in `semantics/prop`; do not edit evaluator/semantics definitions outside this directory.
- First verify the current cheated baseline and audit the exact remaining ExtCall cheats/suspends.
- Then refactor the static ExtCall proof boundary so the generated optional-driver IH is used only inside a single concrete success-continuation branch.
- Prove static error branches by immediate local rewriting, prove the static `run_ext_call SOME` branch using existing projected ExtCall helpers, and leave no broad generated-prefix reconstruction.
- If a probe produces the old large prefix fanout or needs broad `simp`/`gvs`/`AllCaseEqs()` over the whole prefix, stop and escalate.

#### Description
This subtree is a fresh executable plan after a prior terminal stop. It authorizes only the clarified ExtCall route: careful branch-by-branch proof inside `semantics/prop`, with the generated optional-driver IH specialized only after the proof is in a single concrete success continuation. The plan intentionally starts with audit/probe leaves so the executor can stop early if the old proof-boundary problem recurs.

#### Approach
Begin by making the PLAN gate executable, not by resurrecting stale old leaves. The proof target is the remaining `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` and the related nonstatic ExtCall cheat if it remains in the source; prove only what is required for the task’s current ExtCall soundness obligation. Use the existing projected ExtCall helpers as the consumer interface, and add only strict local lemmas if a helper conclusion fails to match the branch goal directly.

#### Not to try
Do not retry the old top-boundary tactic that split `run_ext_call` and then tried to recover the driver premise from a huge generated prefix. Do not use broad `simp`/`gvs`/`AllCaseEqs()` over the whole ExtCall prefix, do not solve generated-prefix fanout goals one by one, and do not introduce long adapter theorems whose only purpose is to replay the generated prefix. Do not edit evaluator definitions, semantics definitions, or files outside `semantics/prop`.

#### Argument
The mutual theorem’s expression-call branch already proves the argument-evaluation prefix and supplies the generated IHs. For `ExtCall T`, after `eval_exprs` succeeds and the static typing facts are destructed, the evaluator performs a fixed monadic chain: address/argument shape, calldata construction, empty-code check, account/transient reads, `run_ext_call`, state updates, and optional driver evaluation/tail handling. The proof should follow that chain linearly and discharge each error branch immediately, keeping only one success branch alive. In the concrete `run_ext_call = SOME (...)` branch, existing local theorems `extcall_static_projected_sound` and `extcall_static_projected_state_well_typed` express exactly the needed combined postcondition for the original call, provided the branch-local optional-driver IH is available. The strategy is therefore not to reconstruct the full generated prefix from the top Resume context; it is to move/suspend at a better boundary, with concrete prefix assumptions already split, and apply the projected helper there.

#### Definition design
No evaluator or type-system definitions should change. The proof-interface definition boundary is the existing projected-helper interface: `extcall_static_projected_sound` consumes the original `eval_expr` equality, argument typing/evaluation facts, static call typing facts, and a driver IH of the form `!env0 st0 res0 st0'. ... eval_expr cx (THE drv) st0 = ... ==> well_typed_expr env0 (THE drv) ==> ...`. The boundary probe must check that this IH can be obtained in a compact branch-local context after the concrete static prefix has been split. Failure signs: goals with a large generated optional-driver prefix before `run_ext_call = SOME ...` is fixed; needing to solve many prefix-equality side goals independently; using `AllCaseEqs()` or broad `gvs` to mine the IH from the top-level Resume context; or writing long generated-prefix adapter theorems.

#### Code structure
All edits belong in `semantics/prop/vyperTypeStmtSoundnessScript.sml` and task-local notes under `semantics/prop` if needed. Keep existing helper theorems in the same script; do not introduce new theories or edit files outside `semantics/prop`. Prefer adding small `Resume eval_all_type_sound_mutual[...]` subcomponents/suspends at the ExtCall static boundary over large inlined tactic blocks. Commit task-local changes unsigned (`git commit --no-gpg-sign`) after coherent progress; do not stage unrelated untracked files such as legacy/temp artifacts.

### C0.1: Audit and baseline-check the current ExtCall proof state under an active component
- Kind: `proof_audit`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: Risk 1 because this is a bounded source/build audit with no proof design choices. It exists to convert the prior blocked no-frontier state into checked current evidence under an active executable component.
- Carries progress/evidence from: TO_type_system_rewrite-20260601T220715Z_m4275_t001

#### Progress note
The previous holbuild attempt was blocked only by the terminal PLAN gate. This leaf authorizes the same baseline check now that an executable component exists.

#### Summary
- Run the focused baseline build for `vyperTypeStmtSoundnessTheory` before edits.
- Confirm the remaining ExtCall `cheat`/`suspend` locations in `vyperTypeStmtSoundnessScript.sml`.
- Confirm that existing proved helpers `extcall_static_projected_sound`, `extcall_static_projected_state_well_typed`, and `run_ext_call_accounts_well_typed` are available in the same theory.
- Record any unexpected source drift in task-local notes and stop if it changes the proof target.

#### Statement
Task-local audit: under an active PLAN component, verify the current source baseline and identify the exact ExtCall proof obligations remaining in `semantics/prop/vyperTypeStmtSoundnessScript.sml`.

#### Approach
Run a focused `holbuild` target for `vyperTypeStmtSoundnessTheory` before editing. Then inspect the ExtCall Resume block around `Expr_Call_ExtCall_result_static_success` and `Expr_Call_ExtCall_result_nonstatic` and the local helper theorem statements. If the source no longer matches the expected shape, escalate rather than guessing.

#### Not to try
Do not treat a successful baseline build as proof completion; existing cheats/suspends may be intentional. Do not edit or commit unrelated task-memory or untracked files during this audit.

### C0.2: Create a branch-local static `run_ext_call SOME` boundary probe
- Kind: `proof_boundary_probe`
- Risk: 2
- Work priority: 10
- Work units: 2
- Rationale: Risk 2 because it is a deliberately small proof-boundary refactor, not a full proof: it only checks whether the authorized linear path reaches a compact concrete `run_ext_call SOME` continuation without the old generated-prefix fanout. Prior evidence makes this a necessary checkpoint, but the work itself is mechanically bounded.
- Dependencies: C0.1
- Checkpoint: yes
- Supersedes: E0217
- Progress transition: `refinement`
- Carries progress/evidence from: TO_type_system_rewrite-20260601T220715Z_m4232_t001

#### Progress note
E0217 remains valid negative evidence for the old boundary. This component refines that failed attempt by moving the proof boundary to a branch-local success continuation and making the absence of prefix fanout the checkpoint result.

#### Summary
- Refactor only the static ExtCall success Resume enough to expose a concrete `run_ext_call = SOME (success, returnData, accounts', tStorage')` branch.
- Keep calldata error, empty-code error, and `run_ext_call = NONE` branches discharged immediately as they already are or by equivalent local rewrites.
- Do not specialize the generated optional-driver IH until the concrete SOME branch is the single active success continuation.
- Checkpoint with the exact live assumptions/goals if the boundary is compact; stop if it recreates the old 9-goal/generated-prefix fanout.

#### Statement
Boundary probe in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`: after static argument typing, calldata success, nonempty code, and `run_ext_call ... = SOME (...)`, the remaining success proof branch should be a compact single branch suitable for applying `extcall_static_projected_sound`/`extcall_static_projected_state_well_typed` and the branch-local driver IH.

#### Approach
Continue the existing linear proof prefix one monadic operation at a time. Use explicit `Cases_on` for `build_ext_calldata`, empty-code, and `run_ext_call`; close each error case before proceeding, and in the SOME case use `PairCases_on`/boolean success split only after the run result equality is fixed. Add a temporary or permanent `suspend` name only at the concrete SOME/success continuation if needed for checkpoint evidence.

#### Not to try
Do not `gvs[..., AllCaseEqs(), ...]` the whole evaluator prefix. Do not attempt helper application while multiple prefix branches are active. Do not produce or solve a collection of generated-prefix side goals; if that happens, close the component as stuck with evidence.

### C0.3: Prove the static `run_ext_call SOME` ExtCall branch using projected soundness helpers
- Kind: `main_proof_leaf`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Risk 2 because once C0.2 verifies the compact branch boundary, this leaf is a direct application of already-proved local projected helpers plus the generated driver IH. The helper statements match the main mutual postcondition for the static call.
- Dependencies: C0.2
- Carries progress/evidence from: C0.2, extcall_static_projected_sound, extcall_static_projected_state_well_typed

#### Progress note
This leaf depends on the checkpoint evidence that the success branch is compact. If C0.2 is not accepted, this proof leaf should not be attempted.

#### Summary
- In the compact static SOME branch, derive the combined postcondition for the original static ExtCall expression.
- Use `extcall_static_projected_sound` as the primary theorem; use `extcall_static_projected_state_well_typed` only if a separately shaped state-well-typed subgoal appears.
- Supply existing argument-evaluation, expression typing, well-formed return type, `MAP expr_type`, and driver typing assumptions directly.
- Specialize the generated optional-driver IH only inside this branch and only to the theorem’s driver-IH premise shape.

#### Statement
Complete the non-error static ExtCall branch of `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`, proving `state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\ case res of INL tv => expr_result_typed env (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) tv | INR _ => T`.

#### Approach
After C0.2, avoid replaying evaluator internals. Match the current assumptions to the hypotheses of `extcall_static_projected_sound`: original `eval_expr` equality, `well_typed_exprs env es`, `well_typed_opt env drv`, `well_formed_type env.type_defs ret_type`, `MAP expr_type es = BaseT AddressT :: arg_types`, argument success facts, and the generated driver IH. Use `irule`/`drule`/`goal_assum` style so the conclusion unifies; if manual theorem plumbing is required, stop and request a small local bridge lemma with exactly the missing conclusion.

#### Not to try
Do not unfold `evaluate_def` again after reaching the compact SOME branch unless needed to discharge a concrete equality already fixed in assumptions. Do not instantiate `extcall_static_projected_sound` with a long `QSPECL` list or copy full assumptions into `ASSUME`; that means the proof interface is not matching and should be escalated.

### C0.4: Prove or isolate the nonstatic ExtCall branch with the same linear discipline
- Kind: `proof_boundary_probe`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: Risk 2 because the source shows `Expr_Call_ExtCall_result_nonstatic` remains cheated, but it is structurally analogous to the static branch and should use the same branch-local method. The leaf is scoped as prove-or-isolate: if it is not straightforward, the task instruction requires stopping with exact evidence rather than expanding the plan into a large new proof search.
- Dependencies: C0.3
- Checkpoint: yes

#### Progress note
This is included because current source evidence shows `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]: cheat`. It is required only if that cheat is still present after C0.1 audit; if source drift proves it already solved, close this component with carry-forward evidence.

#### Summary
- Inspect and attempt the nonstatic ExtCall branch only after the static branch is complete.
- Follow the same monadic, one-branch-at-a-time discipline: argument success, value argument, calldata, empty-code, `run_ext_call`, state updates, optional driver/tail if applicable.
- Use existing nonstatic ExtCall helpers if present; otherwise add only a small local helper whose statement mirrors the static projected helper and matches the live branch.
- Checkpoint if no matching helper exists or if the branch is not straightforward.

#### Statement
Close `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` if it remains a cheat, proving the same combined expression postcondition for `Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv`.

#### Approach
First grep/read for existing nonstatic projected helper theorems near the static helpers; use them if their conclusions match the mutual postcondition. If no such helper exists, do not invent a broad adapter over the generated prefix; add at most one local projected helper with hypotheses mirroring the live nonstatic branch and prove it by the same linear evaluator split. If that helper is not mechanical, close the component as a checkpoint problem with the exact missing interface.

#### Not to try
Do not let this become a whole call-soundness redesign. Do not edit semantics definitions, and do not import or move proofs outside `semantics/prop`. Do not continue if the proof requires broad prefix simplification or many generated side-goals.

### C0.5: Final proof-integrity build, task-plan update, and unsigned commit
- Kind: `integration_audit`
- Risk: 1
- Work priority: 40
- Work units: 1
- Rationale: Risk 1 because it is build/audit/recordkeeping after the proof leaves are closed. It does not introduce new mathematical obligations.
- Dependencies: C0.4
- Supersedes: prior terminal blocked-report completion claim
- Carries progress/evidence from: C0.1, C0.2, C0.3, C0.4

#### Progress note
This final audit should distinguish real proof completion from the earlier cheated-baseline build evidence.

#### Summary
- Run focused `holbuild` for `vyperTypeStmtSoundnessTheory` and any task-required aggregate target if already customary in the branch.
- Grep within `semantics/prop` for remaining `cheat`/relevant `suspend` occurrences in the ExtCall mutual proof area.
- Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and/or `STATE_type_system_rewrite.md` only with concise factual progress.
- Commit only relevant tracked task-local files with `--no-gpg-sign`.

#### Statement
Final task-scoped integration: the ExtCall branch obligations addressed by this subtree build without the old cheats, task-local progress notes are accurate, and the commit is unsigned.

#### Approach
Run the same focused build used in C0.1, then audit for remaining cheats in `vyperTypeStmtSoundnessScript.sml` around `eval_all_type_sound_mutual[Expr_Call_ExtCall...]`. If the nonstatic branch remains intentionally unresolved because C0.4 escalated, do not claim completion. Commit only proof/source and task-note changes that belong to this subtree, using `git commit --no-gpg-sign`.

#### Not to try
Do not stage unrelated untracked legacy/temp files. Do not report task completion merely because a cheated baseline builds. Do not run broad repository cleanup or fix unrelated cheats outside this ExtCall scope.
