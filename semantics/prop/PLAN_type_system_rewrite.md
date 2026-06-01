# PLAN

## Structured Components

### C0: Complete the task-scoped type-system rewrite obligations in semantics/prop
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: All remaining task-scoped source cheats are known and localized: ExtCall_result INL in statement soundness, RawCallTarget statement soundness, and raw_call_return_type_well_formed in builtins. Prior ExtCall INR/equality-helper work is build-clean and carries forward; the new plan removes tactical subchildren and schedules only durable obligations with explicit dependencies.
- Required for completion: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0097, E0098, E0099, TO_type_system_rewrite-20260601T081233Z_m2148_t001, TO_type_system_rewrite-20260601T081233Z_m2212_t001, TO_type_system_rewrite-20260601T081233Z_m2219_t002
- Invalidates prior progress/evidence: C0@over-decomposed, C0.4.1, C0.4.2, C0.4.3, C0.4.4, C0.4.5, C0.5@premature-audit

#### Progress note
This is a shallow rebase of the task plan. The completed C0.3/C0.3.3.4 ExtCall argument-error/INR work remains valid source progress and should not be redone. E0098's helper `extcall_static_args_runtime_typed_nonempty` also carries forward as ordinary local infrastructure, but the failed tactical C0.4 split is invalidated. E0099 is accepted as a scheduler/dependency failure, not as evidence against the theorem.

#### Summary
Flatten the remaining work into durable task obligations. Completed ExtCall argument-error/INR work carries forward and is no longer represented by deep executable children. Remaining source cheats are exactly the ExtCall_result INL success branch, RawCallTarget branch, and `raw_call_return_type_well_formed`. Prove the builtins helper before RawCallTarget; prove ExtCall_result independently; then run one final task-local audit/update/unsigned commit. Do not edit outside `semantics/prop` or semantics/evaluator definitions.

#### Approach
Execute the flat leaves in dependency/priority order. If the ExtCall INL or RawCallTarget branch stops being straightforward, close the component as stuck and return for strategy rather than adding deeper tactical descendants. Use holbuild targets named in each leaf and run grep-based cheat audits only after the relevant proof leaf has completed.

#### Not to try
Do not recreate the old C0.4.1-C0.4.5 tactical split or add descendants for every monadic operation. Do not schedule an audit before its proof obligation has removed the corresponding cheat. Do not use broad `simp`/`gvs`/`AllCaseEqs()` over the generated optional-driver prefix in ExtCall_result, and do not recover the driver premise from the top-level Resume context with generated-prefix adapter plumbing.

#### Argument
The task is complete when every task-scoped cheat in `semantics/prop` that blocks the type-system rewrite is removed and the relevant theories build. ExtCall_result is already split at the semantic boundary `eval_exprs cx es st`: the INR argument-error branch is proved by rewriting with `eval_extcall_args_error_any_call_ty_result_eq`; only the INL argument-success branch remains. That remaining branch should follow the maintainer-approved linear monadic path: use the expression-list IH to obtain runtime-typed argument values and preservation for `args_st`, use ExtCall argument-shape lemmas to extract target/amount, close prefix error exits immediately from the concrete evaluator equations, and invoke the existing ExtCall tail/continuation lemmas only after the success continuation is concrete. RawCallTarget is downstream of the builtins return-type well-formedness fact, so the arithmetic/type helper is scheduled first. Final validation greps only the task-scoped source files and builds the relevant theories.

#### Definition design
No evaluator, semantics, or typing definitions may change. The proof interface is by local boundary lemmas, not by broad simplification through generated mutual-induction prefixes. For ExtCall_result, use existing local helpers such as `eval_extcall_args_error_any_call_ty_result_eq`, `extcall_static_args_runtime_typed_dest`, `extcall_static_args_runtime_typed_nonempty`, `extcall_nonstatic_args_runtime_typed_dest`, `run_ext_call_accounts_well_typed`, and `extcall_success_continuation_sound` / conditional-driver variants. The generated optional-driver IH is not a global simplifier fact; if it is needed, specialize it only inside a concrete success continuation. For RawCallTarget, first provide the missing well-formed return-type boundary theorem so the branch proof does not unfold raw-call return-type arithmetic repeatedly.

#### Code structure
All edits stay under `semantics/prop`. Statement-soundness edits go in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, in the local helper section near ExtCall lemmas and the suspended `eval_all_type_sound_mutual` resumes. The builtins helper proof stays at `raw_call_return_type_well_formed` in `semantics/prop/vyperTypeBuiltinsScript.sml`. Do not edit evaluator/semantics definitions and do not edit outside `semantics/prop`. Commit completed progress with unsigned git commits only; do not GPG-sign.

### C0.1: Prove `raw_call_return_type_well_formed` in the builtins theory
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: The theorem is already present and most cases are discharged before the single cheat. The remaining obligation is local arithmetic/type-shape reasoning about `raw_call_return_type`; it is independent of ExtCall_result and is a strict prerequisite for a clean RawCallTarget proof.
- Checkpoint: yes
- Progress transition: `refinement`
- Invalidates prior progress/evidence: C0.8

#### Progress note
This replaces old C0.8 under the flattened plan with the same obligation and no changed statement.

#### Summary
Remove the cheat in `semantics/prop/vyperTypeBuiltinsScript.sml` at `raw_call_return_type_well_formed`. Keep the theorem statement unchanged. Prove the remaining arithmetic/type-slot case locally. Build the relevant builtins theory after the proof. This proof must stay inside `semantics/prop`.

#### Statement
`Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)`

#### Approach
Continue from the existing proof skeleton after `Cases_on flags` and rewriting `raw_call_return_type_def`, `well_formed_type_def`, `evaluate_type_def`, and `type_slot_size_def`. The existing `word_size_le` lemma is the intended arithmetic boundary; use it to control the `word_size n` branch and close the remaining slot-size/numeric side condition with targeted arithmetic, not by changing definitions. After replacing the cheat, build the theory that contains `vyperTypeBuiltinsScript.sml`.

#### Not to try
Do not change `raw_call_return_type`, `type_slot_size`, or ABI-size definitions. Do not move this proof outside `semantics/prop`. Do not leave the arithmetic case as a new helper unless it is a genuinely reusable one-line numeric lemma; the expected proof is local.

### C0.2: Close the ExtCall_result INL success branch without generated-prefix cleanup
- Kind: `proof_branch`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: The branch is maintainer-authorized for a careful linear proof, and the needed semantic boundary lemmas already exist. E0098 shows the risk is not semantic falsity but proof-interface misuse; the flat plan explicitly forbids generated-prefix simplification and treats any non-straightforward obstruction as a stop condition.
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0097, E0098, TO_type_system_rewrite-20260601T081233Z_m2212_t001
- Invalidates prior progress/evidence: C0.4@old-linear-leaf, C0.4.1, C0.4.2, C0.4.3, C0.4.4, C0.4.5

#### Progress note
This replaces the old multi-child C0.4 tactical split with one durable proof obligation: remove the remaining INL cheat in the ExtCall_result Resume branch. E0097's INR proof and E0098's local helper carry forward; E0098's failed generated-prefix approach does not.

#### Summary
Replace the `>- cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` for `args_res = INL vs`. Keep the already-proved INR branch intact. Use expression-list IH facts, ExtCall runtime-typed argument destructors, and existing success-continuation lemmas. Split the evaluator prefix one operation at a time and close error exits immediately. Build `vyperTypeStmtSoundnessTheory` when the cheat is removed.

#### Description
This leaf deliberately does not prescribe one child per prefix operation. The durable boundary is the semantic branch: ExtCall argument evaluation succeeded, so the proof must establish the call postcondition for all static/nonstatic ExtCall prefix outcomes. The generated optional-driver IH may be stored or left unintroduced while prefix cases are split, but it must not be a simplifier-visible assumption during error exits.

#### Statement
In `semantics/prop/vyperTypeStmtSoundnessScript.sml`, complete the `args_res = INL vs` branch of:

`Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]:`

for `eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st')`, proving the usual state preservation, environment consistency, accounts well-typedness, no-TypeError, and result-typing postcondition.

#### Approach
After unfolding `well_typed_expr` once and applying the `eval_exprs` IH, keep the existing INR branch proof unchanged and work only in the INL branch. Derive `exprs_runtime_typed env es vs`; split static/nonstatic using the well-typed ExtCall shape; use `extcall_static_args_runtime_typed_nonempty`, `extcall_static_args_runtime_typed_dest`, and `extcall_nonstatic_args_runtime_typed_dest` instead of unfolding runtime typing in the Resume context. Then unfold one evaluator prefix operation at a time (`build_ext_calldata`, target/code checks, `run_ext_call`, revert flag, account/transient updates); each error result should close immediately as a non-TypeError runtime error with preserved state facts. In the unique success continuation, use `run_ext_call_accounts_well_typed` plus `extcall_success_continuation_sound` or `extcall_success_continuation_sound_cond_driver_ih`, specializing the optional-driver IH only after `returnData = [] /\ IS_SOME drv` is the concrete tail branch.

#### Not to try
Do not use broad `simp`, `gvs`, or `AllCaseEqs()` while the generated optional-driver IH/prefix is present; E0098 timed out on that path. Do not build a long adapter theorem to recover the driver premise from the top-level Resume context. Do not reprove argument-runtime destructors by unfolding `exprs_runtime_typed_def` inside the live branch. Do not split this leaf into tactical descendants unless a new durable helper theorem with a stable statement is genuinely needed; if the proof is not straightforward, stop and report stuck.

### C0.3: Prove the RawCallTarget expression-call soundness branch
- Kind: `proof_branch`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: RawCallTarget is a remaining suspended call-constructor branch in the same statement-soundness proof. With `raw_call_return_type_well_formed` available, the branch should follow the already-completed call/builtin branches by direct unfolding, argument IH use, and result typing from builtins facts.
- Dependencies: C0.1
- Checkpoint: yes
- Progress transition: `refinement`
- Invalidates prior progress/evidence: C0.7

#### Progress note
This replaces old C0.7 with the same RawCallTarget obligation, now explicitly dependent on the builtins return-type well-formedness helper.

#### Summary
Replace the `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`. Use the existing RawCallTarget evaluator/typing branch shape and the builtins well-formedness theorem from C0.1. Follow nearby completed branches such as Send/RawLog/RawRevert for proof style. Build `vyperTypeStmtSoundnessTheory` after the proof. Stop if a missing semantic helper appears.

#### Statement
In `semantics/prop/vyperTypeStmtSoundnessScript.sml`, complete:

`Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:`

proving the expression-call type-soundness postcondition for `Call ty (RawCallTarget flags) es drv`.

#### Approach
Use the relevant `well_typed_expr_def` branch and `evaluate_def` branch for RawCallTarget, as the neighboring call resumes do. Apply the expression-list IH to the evaluated arguments, close immediate type-check/error exits from `no_type_error_result_def`, and use C0.1's `raw_call_return_type_well_formed` where the return type must be shown well formed. Match the proof style of `Expr_Call_Send`/`RawLog` rather than introducing new semantics abstractions.

#### Not to try
Do not edit raw-call evaluator definitions or weaken the typing rule. Do not unfold the full raw-call return-type arithmetic in this branch; use `raw_call_return_type_well_formed`. Do not continue if the branch requires a broad new generated-prefix adapter or a nonlocal helper outside `semantics/prop`.

### C0.4: Audit ExtCall_result, RawCallTarget, and builtins cheats after proof leaves
- Kind: `integration_validation`
- Risk: 1
- Work priority: 30
- Work units: 2
- Rationale: Once C0.1-C0.3 are complete, validation is mechanical: build the relevant theories and grep the task-scoped source for remaining real `cheat` commands. This replaces the premature old C0.5 audit with dependencies that force it to run after the proofs.
- Dependencies: C0.1, C0.2, C0.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0099
- Invalidates prior progress/evidence: C0.5@premature-audit

#### Progress note
E0099 showed the audit itself was correct but scheduled too early. This component keeps the audit idea and fixes its dependencies.

#### Summary
Run the task-scoped proof-integrity checks only after all proof leaves are done. Build `vyperTypeStmtSoundnessTheory` and the builtins target. Grep `semantics/prop/*.sml` for real remaining `cheat` commands and confirm the former locations `Expr_Call_ExtCall_result`, `Expr_Call_RawCallTarget`, and `raw_call_return_type_well_formed` are clean. Comments mentioning historical cheats are not failures unless they contain executable `cheat`.

#### Statement
Validation obligation: no executable `cheat` remains at the task-scoped locations `vyperTypeStmtSoundnessScript.sml:Expr_Call_ExtCall_result`, `vyperTypeStmtSoundnessScript.sml:Expr_Call_RawCallTarget`, or `vyperTypeBuiltinsScript.sml:raw_call_return_type_well_formed`, and the relevant HOL theories build.

#### Approach
Run the same targeted grep that found the three remaining cheats, then inspect any hits to distinguish comments from executable proof commands. Build `vyperTypeStmtSoundnessTheory`; also build the theory target affected by `vyperTypeBuiltinsScript.sml` if not already rebuilt as a dependency. If a new executable cheat appears in `semantics/prop` that is directly task-scoped, stop for strategist review rather than silently expanding scope.

#### Not to try
Do not run this audit before C0.1-C0.3 complete. Do not declare task completion merely because `holbuild` succeeds; previous evidence showed build-clean source can still contain intentional cheats. Do not edit unrelated files to silence grep hits in comments.

### C0.5: Update task-local plan/state and make the final unsigned commit
- Kind: `finalization`
- Risk: 1
- Work priority: 40
- Work units: 2
- Rationale: After proof and audit components, only task hygiene remains: update the task-local plan/state as requested and commit without GPG signing. This is mechanical and within the task file's explicit instructions.
- Dependencies: C0.4
- Progress transition: `replacement`
- Invalidates prior progress/evidence: C0.6@old-finalization

#### Progress note
This replaces the old final-validation component after flattening the plan.

#### Summary
Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and any task-local handoff/state file that must reflect completed progress. Ensure no edits outside `semantics/prop` are included. Run final status/audit checks. Commit the completed work with GPG signing explicitly disabled. Report completion only after the unsigned commit succeeds.

#### Statement
Final task obligation: task-local documentation is current, proof-integrity checks pass, and the final commit is made without GPG signing.

#### Approach
Review `git status` before committing and include only `semantics/prop` changes. Update the plan/state document to mention the completed ExtCall_result, RawCallTarget, and builtins helper proofs. Use an unsigned commit command such as `git -c commit.gpgsign=false commit ...`; if tooling requires signing or prompts for a password, stop and report the tooling issue.

#### Not to try
Do not commit files outside `semantics/prop`. Do not use a normal commit command if repository config may GPG-sign by default. Do not end the session as complete before the final audit and unsigned commit are both done.
