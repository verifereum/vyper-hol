# PLAN

## Structured Components

### C0: Complete the task-scoped type-system rewrite obligations in semantics/prop
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: C0.2 is now decomposed into branch-local Risk-2 proof leaves; existing completed C0.1 and blocked downstream siblings are preserved. No whole-task strategy issue is shown by E0102.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0, E0102

#### Progress note
C0 remains the same top-level obligation; E0102 is carried as negative evidence that forced the local C0.2 repair.

#### Summary
Top-level task remains the same. C0.1 is already proved and carried by the existing plan. C0.2 is repaired locally by abandoning the forbidden helper shortcut and using a linear branch-local ExtCall proof. Downstream C0.3-C0.5 remain preserved and blocked until the ExtCall_result checkpoint closes.

#### Argument
The task-scoped proof obligations are discharged by completing the remaining suspended call branches and then validating the script. E0102 only invalidates the local C0.2 shortcut path: it shows that `extcall_expr_sound_from_generated_ih` exposes the generated ExtCall prefix and violates the maintainer constraints. The replacement C0.2 proof follows the evaluator prefix directly and uses the already-proved continuation lemma once the post-`run_ext_call` tail is reached.

#### Definition design
No evaluator or semantic definitions may be changed. Proof architecture changes stay in `semantics/prop`. The C0.2 interface is: destruct successful ExtCall arguments with the existing runtime-typed lemmas, use `run_ext_call_accounts_well_typed` for the account side effect, and use `extcall_success_continuation_sound_cond_driver_ih` for the final account/transient-update/return-data tail.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml` unless an already task-local proof helper in `semantics/prop` is strictly needed. Preserve omitted siblings in the plan. Do not edit evaluator definitions or files outside `semantics/prop`.

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

### C0.2: Close the ExtCall_result INL success branch by a branch-local linear proof
- Kind: `proof_branch`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The failed shortcut path is abandoned. This is standard proof work if the proof follows the ExtCall evaluator prefix one operation at a time and invokes `extcall_success_continuation_sound_cond_driver_ih` only at the concrete success continuation.
- Dependencies: C0.1
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2, E0102
- Invalidates prior progress/evidence: C0.2@failed-helper-shortcut

#### Progress note
E0102 is accepted as negative evidence and carried forward to forbid the shortcut helper. The theorem obligation is unchanged; only the proof interface/strategy is replaced.

#### Summary
Replace the failed `extcall_expr_sound_from_generated_ih` strategy for `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`. Keep the known-good argument-error branch. In `args_res = INL vs`, rewrite the call-type equality (`v15 = ret_type`), split static/nonstatic, and step linearly through the monadic ExtCall prefix. Close error cases immediately; in the only external-call success path use `extcall_success_continuation_sound_cond_driver_ih`. Discharge that lemma's conditional driver-IH premise from the generated optional-driver IH only after all prefix equations are concrete, preferably with `drule_all` rather than a manual `qspecl` list.

#### Description
E0102 showed that targeted call-type rewriting fixes only the superficial mismatch; applying `extcall_expr_sound_from_generated_ih` still leaves a huge generated-prefix premise and violates the maintainer's no-shortcut constraint. The repaired proof keeps prefix equations as ordinary assumptions until the continuation point, then uses the tail lemma whose statement matches the remaining computation.

#### Statement
Complete the `INL` branch at `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, replacing the `cheat` while preserving the already-working `INR` argument-error branch.

#### Approach
Work in the existing Resume proof. After `Cases_on args_res`, use the expression-list IH facts already obtained by `first_x_assum drule_all`; rewrite the unfolded typing equality so the call is `Call ret_type ...`. Split `Cases_on is_static'`; simplify/case-split only the next evaluator operation (`check`, lifts, calldata, accounts, code check, transient, `run_ext_call`, success check, updates). At the tail, `irule extcall_success_continuation_sound_cond_driver_ih`; for its conditional IH, assume `returnData = [] /\ IS_SOME drv` and use the generated optional-driver IH against the concrete prefix assumptions.

#### Not to try
Do not apply `extcall_expr_sound_from_generated_ih`; E0102 shows it leaves forbidden generated-prefix obligations. Do not use broad `gvs[AllCaseEqs()]` or whole-prefix cleanup. Do not add a long generic adapter theorem for `extcall_generated_driver_ih_def`.

#### Argument
After unfolding `well_typed_expr`, `eval_exprs` either returns an error or a runtime-typed list. The error branch is already solved by `eval_extcall_args_error_any_call_ty_result_eq`. In the success branch, argument typing and the static/nonstatic shape premise provide the target address and, in the nonstatic branch, the transfer amount. Prefix failures yield immediate runtime errors with vacuous result-typing obligations. On `run_ext_call` success, `run_ext_call_accounts_well_typed` supplies typed returned accounts, and the remaining account/transient update plus return-data/driver tail is exactly the computation covered by `extcall_success_continuation_sound_cond_driver_ih`.

#### Definition design
No new semantic definition is required. The proof interface should expose only the next prefix operation and the final continuation lemma; if the final tail no longer matches the displayed `do _ <- assert T; update_accounts; update_transient; if ...` computation, the prefix was simplified too broadly or at the wrong time.

#### Code structure
Edit only `semantics/prop/vyperTypeStmtSoundnessScript.sml`. If proof length requires factoring, prefer local `suspend`/`Resume` branches in the same script rather than cross-file abstractions. Keep helper use local to the ExtCall helper block already present above the Resume proof.

### C0.2.1: Rebuild the ExtCall_result Resume skeleton without the shortcut helper
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: This local proof-script refactor preserves the known argument-error branch and sets up controlled static/nonstatic success branches.
- Dependencies: C0.1
- Progress transition: `replacement`
- Carries progress/evidence from: E0102
- Invalidates prior progress/evidence: C0.2@failed-helper-shortcut

#### Progress note
The failed episode showed the old skeleton immediately encouraged the forbidden helper; this leaf replaces that setup.

#### Summary
Replace the `>- cheat` placeholder with a structured `INL vs` skeleton. Preserve the existing `INR` branch unless mechanical changes are unavoidable. Name the args-IH consequences, rewrite `v15 = ret_type`, split `is_static'`, and keep the generated optional-driver IH available. Do not perform global prefix cleanup.

#### Statement
Set up the `INL vs` branch so each static/nonstatic subgoal has `exprs_runtime_typed env es vs`, the relevant `MAP expr_type es = ...` premise, `well_typed_opt env drv`, `well_formed_type env.type_defs ret_type`, `!e. drv = SOME e ==> expr_type e = ret_type`, and the generated optional-driver IH still present.

#### Approach
Use the result of the expression-list IH from the existing `first_x_assum drule_all`. After `rewrite_tac[Once well_typed_expr_def]`, rewrite the call-result type equality to `ret_type` before considering any call-specific lemma. Derive target/value destructor facts with the existing runtime-typed helper theorem before simplifying the evaluator prefix.

#### Not to try
Do not invoke `irule extcall_expr_sound_from_generated_ih`. Do not consume or clear the generated optional-driver IH before the final continuation point.

### C0.2.2: Close the static ExtCall prefix and tail
- Kind: `proof_branch`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The static branch is a linear sequence of target extraction, calldata construction, account/code/transient operations, external call with `NONE`, and the common tail.
- Dependencies: C0.2.1
- Carries progress/evidence from: E0102

#### Progress note
Concrete static branch of the replacement strategy.

#### Summary
In the `is_static'` branch, step through the ExtCall prefix one operation at a time. Close target/address/calldata/code/run/revert failures immediately. On external-call success, prove `accounts_well_typed accounts'` and invoke `extcall_success_continuation_sound_cond_driver_ih` for the tail.

#### Statement
Static success branch: from `exprs_runtime_typed env es vs` and `MAP expr_type es = BaseT AddressT :: arg_types`, prove the soundness postcondition for `eval_expr cx (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) st = (res,st')`.

#### Approach
Use `extcall_static_args_runtime_typed_dest` and nonemptiness before simplifying. Case split locally on `build_ext_calldata`, target code emptiness, `run_ext_call`, and `success`; close failures with `return_def`, `raise_def`, and `no_type_error_result_def`. In the success tuple branch, `drule_all run_ext_call_accounts_well_typed`, then apply `extcall_success_continuation_sound_cond_driver_ih`; discharge its driver premise from the generated optional-driver IH using the concrete prefix assumptions and `drule_all`.

#### Not to try
Do not unfold or abstract `extcall_generated_driver_ih_def`. Do not simplify the nonstatic value-extraction path in this branch except as reduced by `is_static'=T`.

### C0.2.3: Close the nonstatic ExtCall prefix and tail
- Kind: `proof_branch`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: This mirrors the static branch with the additional amount extraction supplied by the existing nonstatic argument helper.
- Dependencies: C0.2.1
- Carries progress/evidence from: E0102

#### Progress note
Concrete nonstatic branch of the replacement strategy.

#### Summary
In the `~is_static'` branch, step through target and value extraction before calldata. Close each immediate runtime-error case locally. On external-call success, use the same returned-account typing and continuation-tail strategy as the static branch.

#### Statement
Nonstatic success branch: from `exprs_runtime_typed env es vs` and `MAP expr_type es = BaseT AddressT :: BaseT (UintT 256) :: arg_types`, prove the soundness postcondition for `eval_expr cx (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) st = (res,st')`.

#### Approach
Use `extcall_nonstatic_args_runtime_typed_dest` for `target_addr` and `amount`, plus simple list nonemptiness for `vs` and `TL vs`. Then simplify only the next operation and split on calldata/code/run/revert cases as in C0.2.2. At the final success branch, apply `extcall_success_continuation_sound_cond_driver_ih` and obtain its conditional driver IH from the generated optional-driver IH by branch-local `drule_all`, not a hand-written instantiation list.

#### Not to try
Do not try to factor static and nonstatic through a new large abstraction unless this leaf fails; the branch-by-branch proof is the maintainer-approved path.

### C0.2.4: Validate the completed ExtCall_result branch remains task-local and cheat-free
- Kind: `integration_validation`
- Risk: 1
- Work priority: 30
- Work units: 1
- Rationale: After both success branches are filled, validation is mechanical.
- Dependencies: C0.2.2, C0.2.3
- Checkpoint: yes

#### Progress note
Provides the positive closure evidence that E0102 lacked.

#### Summary
Build `vyperTypeStmtSoundnessTheory`. Grep/inspect the targeted `Expr_Call_ExtCall_result` Resume block and confirm the former `INL` branch has no `cheat`. Confirm edits stayed inside `semantics/prop`.

#### Statement
The relevant theory builds, and the `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` block has no `cheat` in the former `args_res = INL` branch.

#### Approach
Use the same task-local build style as E0102. Inspect only task-scoped source for this validation. If success requires broad generated-prefix cleanup or edits outside `semantics/prop`, stop and escalate rather than closing.

#### Not to try
Do not proceed to C0.3 until this checkpoint is accepted.

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
