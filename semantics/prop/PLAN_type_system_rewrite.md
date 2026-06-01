# PLAN

## Structured Components

### C0: Type-system rewrite proof completion is terminally blocked at static ExtCall under current contract
- Kind: `blocked_task_gate`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Task completion requires zero reachable cheats in the task-scoped type-system rewrite, but `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` in `semantics/prop/vyperTypeStmtSoundnessScript.sml` remains an explicit intentional `cheat`. Accepted prior evidence says the theorem has not been shown false; the blocker is proof architecture: both the compact helper-premise route and the maintainer-authorized careful branch-by-branch route reached the generated optional-driver IH mismatch, where completing the proof required broad generated-prefix simplification, `AllCaseEqs()` cleanup, or long adapter plumbing forbidden by the maintainer clarification and by the task's 'stop if not straightforward' instruction. No evaluator/semantics definition change is allowed and no new maintainer-approved boundary architecture is currently available, so there is no low-risk proof frontier to authorize.
- Required for completion: yes
- Supersedes: C0, C0.2, C0.2.1, C0.2.1.3, C0.2.1.3.3, C0.2.1.4, C0.2.2, C0.2.3, C0.3, C0.4, C0.5
- Progress transition: `replacement`
- Carries progress/evidence from: E0144, E0149, E0150, E0155, TO_type_system_rewrite-20260601T220715Z_m3138_t001, TO_type_system_rewrite-20260601T220715Z_m3161_t002, TO_type_system_rewrite-20260601T220715Z_m3162_t001
- Invalidates prior progress/evidence: old downstream ready leaves under C0.2.1.4, old downstream ready leaves under C0.2.2, old downstream ready leaves under C0.2.3, old RawCallTarget subtree C0.3, old final audit/finalization leaves C0.4-C0.5

#### Progress note
This replacement carries forward the accepted blocked-stop evidence and invalidates only the executable scheduling of downstream leaves. It does not invalidate historical proved helper theorems; it says they are irrelevant to task completion until the required static ExtCall gate has a new approved architecture.

#### Summary
- The task is blocked, not complete and not mathematically disproved.
- The required static ExtCall Resume still contains an explicit `cheat` at `Expr_Call_ExtCall_result_static`.
- Prior accepted attempts exhausted the allowed straightforward proof shapes; the remaining generated-IH recovery would require forbidden broad simplification or long prefix plumbing.
- Downstream nonstatic ExtCall, RawCallTarget, wrapper, and final zero-cheat audit work is not authorized because it cannot make the task complete while this required gate remains open.
- The executor should stop/report the blocked state and must not edit/build/prove until a new architecture or changed scope is explicitly approved.

#### Description
This component replaces the previous mixed C0 subtree, which had historical done leaves and downstream ready-looking leaves despite a required high-risk blocker. The only task-scoped truthful plan state is a terminal proof-architecture block at the static ExtCall Resume. If the user later authorizes a new proof boundary inside `semantics/prop`, the strategist should replace this C0 subtree with new low-risk probes before any proof-script edits or builds.

#### Approach
Do not begin proof work under this component. The executor's next action is to report the blocked outcome to the operator, preserving the evidence that the build can succeed only on an intentional-cheat baseline and that proof-integrity completion is not satisfied. If the operator provides a new approved architecture, call the plan oracle again to replace this subtree before editing.

#### Not to try
Do not retry `mp_tac driver_ih >> simp[]`, broad `gvs`, `AllCaseEqs()`, `drule_all`/`metis_tac` recovery from the top-level Resume context, or any long generated-prefix adapter theorem. Do not work on nonstatic ExtCall, RawCallTarget, wrapper, or final audit components while the static ExtCall cheat remains. Do not describe the task as zero-cheat complete merely because `holbuild` succeeds on the cheated baseline.

#### Argument
The overall task obligation is a proof-integrity obligation: all reachable task-scoped cheats in the new type-system soundness stack must be removed. The static ExtCall branch is required because it is a direct suspended case of `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`. The existing evaluator-generated proof context exposes the optional-driver IH only behind a generated monadic prefix. Prior attempts showed that, at the success continuation, the needed compact driver premise cannot be recovered by the allowed straightforward local splits without falling back to forbidden broad generated-prefix simplification or brittle adapter plumbing. Therefore proving other branches cannot discharge the task: the static cheat remains a necessary blocker.

#### Definition design
No definition redesign is authorized in this plan. The failure sign for any future redesign is exactly the current proof-interface mismatch: consumers must not have to reconstruct a compact driver premise from the generated full-prefix Resume context by broad simplification. A future approved architecture would need a new boundary theorem/suspension interface inside `semantics/prop` whose assumptions are already branch-local at the single concrete ExtCall success continuation; it must be probed before downstream proof work. Evaluator/semantics definitions outside `semantics/prop` remain off-limits.

#### Code structure
No file edits are authorized by this blocked plan except task-memory/reporting updates if the harness requires them. Keep all future possible proof-architecture work within `semantics/prop`; do not edit evaluator/semantics definitions or files outside that directory. If committing task-memory changes, use explicit paths, leave known untracked legacy/tmp files unstaged, and commit with `git commit --no-gpg-sign`.

### C0.1: Accepted source/evidence audit for the static ExtCall block
- Kind: `blocked_report`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This is a carry-forward documentation/status component, not new proof work. The relevant facts have already been checked: the static ExtCall Resume is explicitly cheated, prior permitted proof attempts stopped for proof-interface reasons, and builds that succeeded did so on the intentional-cheat baseline.
- Supersedes: C0.2.1.3.3.4
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0155, TO_type_system_rewrite-20260601T220715Z_m3138_t001, TO_type_system_rewrite-20260601T220715Z_m3137_t004

#### Progress note
This preserves the valid audit/status evidence from the previous C0 subtree while removing it from the executable frontier.

#### Summary
- Carries forward the accepted audit that `Expr_Call_ExtCall_result_static` is still cheated.
- Records that prior `holbuild` success is not proof completion because it includes the intentional cheat.
- Records that known untracked legacy/tmp files are not part of task progress.
- No executor work remains here.

#### Description
Use this component only as evidence context for the blocked task report. It is not a beginable proof leaf and should not trigger edits or builds.

#### Approach
No action. If asked to summarize state, cite the explicit cheat and accepted blocked episodes rather than re-running proof search.

#### Not to try
Do not convert this audit into a proof attempt, and do not use a successful build of the cheated source as completion evidence.

### C0.2: User/maintainer intervention required before any new proof frontier
- Kind: `user_intervention_gate`
- Risk: 3
- Work priority: 10
- Work units: 0
- Rationale: No low-risk proof component can be honestly scheduled without a new approved proof boundary or changed scope. The current maintainer clarification allowed a careful linear branch-by-branch proof, but accepted evidence reports that this exact route was tried and still required forbidden generated-prefix recovery. Inventing another tactical leaf would violate the task instruction to stop when the proof/design is not straightforward.
- Dependencies: C0.1
- Supersedes: C0.2.1.3.3, C0.2.1.3.4, C0.2.1.4, C0.2.2, C0.2.3, C0.3, C0.4, C0.5
- Progress transition: `replacement`
- Carries progress/evidence from: E0144, E0149, E0150, E0155
- Invalidates prior progress/evidence: scheduled downstream proof leaves from the previous C0 subtree

#### Progress note
This component makes explicit that the previous ready-looking descendants are not executable under the current contract; they may be reintroduced only after the static ExtCall gate is redesigned and de-risked.

#### Summary
- Required next event is external: approve a new static ExtCall proof architecture, relax/change task scope, or accept the blocked outcome.
- Until then, the executor must not edit proofs, run speculative builds, or work on downstream cheats.
- If a new architecture is approved, replace this C0 subtree with concrete low-risk probes before editing.
- This is a proof-architecture stop, not a counterexample to the theorem.

#### Description
The allowed future architecture must avoid recovering the optional-driver premise from the top-level generated Resume context. It should introduce a new branch-local proof interface or theorem boundary inside `semantics/prop` and prove small probes that show the driver premise is available only after the concrete success-continuation branch has been reached. Without that approval, the correct terminal action is to report blocked.

#### Approach
Stop and report. If the user explicitly authorizes a new approach, call the strategist first; do not self-design a proof script. The new plan must start with low-risk probes for the replacement boundary, not with editing the cheated Resume directly.

#### Not to try
Do not schedule downstream nonstatic ExtCall, RawCallTarget, public-wrapper, or final zero-cheat audit work as a workaround. Do not introduce evaluator/semantics definition changes or edits outside `semantics/prop`. Do not attempt another tactical variation of the generated-prefix recovery path.

### C0.2.1: Emit terminal task-blocked report for the operator
- Kind: `blocked_report`
- Risk: 3
- Work priority: 0
- Work units: 1
- Rationale: Derived from child component C0.2.1.3.3 risk 3. The current accepted state is intentionally blocked, not proof-complete: E0144/E0149 showed that both the helper-premise consumer route and the maintainer-approved direct branch-by-branch route reach a point where specializing the generated optional-driver IH requires broad generated-prefix simplification and times out. E0150 documented and reviewed the reverted explicit `cheat` stop-state. E0151 correctly reports that the prior C0.2.1.3.3.5 proof-unblock documentation leaf is false and must be removed.
- Dependencies: C0.1
- Checkpoint: yes
- Carries progress/evidence from: episode:E0155, TO_type_system_rewrite-20260601T220715Z_m3140_t001, TO_type_system_rewrite-20260601T220715Z_m3145_t001, TO_type_system_rewrite-20260601T220715Z_m3146_t002

#### Progress note
New terminal leaf created solely to make the accepted blocked outcome explicit and actionable. It does not prove any theorem and does not authorize further proof work.

#### Summary
- Record/report that task proof-integrity completion is blocked, not complete.
- Mention the exact remaining required intentional cheat: static ExtCall Resume in `vyperTypeStmtSoundnessScript.sml`.
- Mention accepted evidence E0144/E0149/E0150/E0155 and commit `92769fb6b`.
- State that no downstream nonstatic ExtCall, RawCallTarget, wrapper, or final zero-cheat audit proof work is authorized in this run.
- Leave pre-existing untracked legacy/tmp files unstaged.

#### Description
Prepare the final task-scoped blocked handoff/outcome. This may be an end-session summary and, if the harness requires a file update, a minimal task-local state/dossier update under `semantics/prop`. The report must be explicit that `holbuild` succeeded only on an intentional-cheat baseline and that the zero-cheat completion criterion is not satisfied.

#### Statement
No HOL theorem. Required report content:
```text
BLOCKED: `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` remains an intentional explicit cheat. Accepted evidence E0144/E0149/E0150/E0155 shows permitted straightforward proof routes were exhausted; no authorized proof frontier remains. The task cannot be reported complete because zero reachable cheats is not satisfied.
```

#### Approach
First confirm `git status` shows only the known pre-existing untracked legacy/tmp files or task-local report edits. If a documentation/state file must be updated, keep it under `semantics/prop`, stage only the relevant tracked file(s), and commit with `git commit --no-gpg-sign` only if there is a real tracked report update. Then end the session with a blocked outcome, not complete.

#### Not to try
Do not edit proof scripts to make a last attempt. Do not run downstream proof components. Do not use `git add -A`; do not stage `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`. Do not describe the task as complete or zero-cheat clean.

### C0.2.1.1: Carry forward ExtCall helper-stack audit
- Kind: `proof_boundary_audit`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: The audit/proved helper stack remains valid; E0121 only invalidates the Resume-facing placement of the boundary.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.1, E0119

#### Progress note
No new work; preserves accepted helper-audit progress.

#### Summary
- Keep the proved ExtCall helper stack.
- `run_ext_call_accounts_well_typed` and `extcall_success_continuation_sound_cond_driver_ih` remain intended interfaces.
- No source changes required.

### C0.2.1.2: Remove the failed static by-subgoal attempt before retrying
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: The dirty proof shape from E0121 is misleading and should not be repaired in place.
- Dependencies: C0.2.1.1
- Supersedes: C0.2.1.2
- Progress transition: `replacement`
- Invalidates prior progress/evidence: E0121

#### Progress note
Replaces old C0.2.1.2 with cleanup; E0121 counts only as negative evidence.

#### Summary
- In the static Resume, remove the failed local assertion of the full post-update tail postcondition if present.
- Restore the success branch to a clean linear prefix-split state with one precise tail goal or one explicit cheat at that point.
- Ensure no `ACCEPT_TAC driver_ih` remains for the conditional premise and no obsolete `by` wrapper remains.

#### Approach
Keep clean prefix splits and the `accounts_well_typed` derivation if present. Remove only the failed proof block that tried to prove the whole tail postcondition in backquotes; C0.2.1.3 will apply the continuation theorem directly to the actual goal.

#### Not to try
Do not patch the old `by` assertion with more `simp`, `gvs`, or generated prefix equations.

### C0.2.1.3: ExtCall static proof block
- Kind: `proof_group`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1.3.3.4 risk 3. After the one-step projection fix, the direct linear proof still requires broad simplification of the generated full-prefix `driver_ih` and times out. This violates the component's not-to-try guard and the maintainer stop rule that the proof should be entirely straightforward.
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2.1.3

#### Progress note
Ancestor included only to connect the updated C0.2.1.3.3 subtree.

#### Summary
Parent carried forward for schema validity. Its only local revision is that C0.2.1.3.3 now has an executable proof leaf for the static Resume.

### C0.2.1.3.1: Retain ExtCall continuation projection lemmas
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already proved in E0128 and still useful inside the new projected helper, especially `extcall_success_continuation_state_well_typed`. E0129 only showed these lemmas should not be applied directly at the old Resume tail edit point.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.3.1, E0128

#### Progress note
The proved infrastructure remains sound and relevant; only the consumer boundary changes.

#### Summary
No new proof work. Keep the existing local continuation lemmas, including `extcall_success_continuation_sound_cond_driver_ih` and `extcall_success_continuation_state_well_typed`. They remain valid infrastructure for the helper that owns the linear static ExtCall success-tail proof. This component is carried forward from E0128.

#### Approach
Audit only if needed: confirm the lemmas still build and are located before the new projected helper. Do not rewrite them unless the new helper exposes a genuine statement mismatch.

#### Not to try
Do not use these lemmas as a direct fix at the old post-`PairCases_on x'` Resume point; the necessary tail equality is not exposed there in a matchable form.

### C0.2.1.3.2: Prove projected static ExtCall state helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The helper statement matches the already-projected Resume obligation and avoids relying on unavailable full-postcondition context. The internal proof is the maintainer-approved linear monadic ExtCall proof, with the driver IH specialized only in the concrete success continuation branch.
- Dependencies: C0.2.1.3.1
- Checkpoint: yes
- Supersedes: C0.2.1.3.2
- Progress transition: `replacement`
- Carries progress/evidence from: E0129, C0.2.1.3.1
- Invalidates prior progress/evidence: C0.2.1.3.2

#### Progress note
Replaces the failed proof-ordering leaf with a boundary lemma designed for the actual projected goal discovered in E0129. Prior proved continuation lemmas remain dependencies.

#### Summary
Add a local theorem before the Resume blocks that concludes `state_well_typed st'` for a static ExtCall call after argument evaluation has succeeded. Assumptions should mirror the stable facts available in `Expr_Call_ExtCall_result_static`: original call evaluation equality, argument evaluation equality, `state_well_typed args_st`, `env_consistent env cx args_st`, `accounts_well_typed args_st.accounts`, `exprs_runtime_typed env es vs`, `well_typed_opt env drv`, `well_formed_type env.type_defs ret_type`, static `MAP expr_type es = BaseT AddressT::arg_types`, return-driver type condition, and the original optional-driver IH. The proof unfolds the static evaluator linearly and closes error cases immediately. In the final success tail, derive `accounts_well_typed accounts'` from `run_ext_call_accounts_well_typed` and apply `extcall_success_continuation_state_well_typed`.

#### Statement
Suggested shape (adjust variable names to source):
```sml
Theorem extcall_static_projected_state_well_typed[local]:
  !env cx st res st' args_st vs func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    well_typed_exprs env es /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    MAP expr_type es = BaseT AddressT::arg_types /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    eval_exprs cx es st = (INL vs,args_st) /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ exprs_runtime_typed env es vs /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T))
    ==> state_well_typed st'
```
If the actual generated IH is conjunctive with a place-expression clause, quantify/assume that exact stronger shape and project the expression clause needed by `extcall_success_continuation_state_well_typed`.

#### Approach
Start from the call evaluation equality, unfold `Once evaluate_def` and only the monadic primitives needed for the static branch. Rewrite with `eval_exprs cx es st = (INL vs,args_st)`, destruct target address/calldata/account-code/run result one operation at a time, and close each error branch by simplification to the existing well-typed intermediate state. In the success branch, prove `accounts_well_typed accounts'` using `run_ext_call_accounts_well_typed`; then `irule extcall_success_continuation_state_well_typed`, provide `runtime_consistent env cx args_st` from `env_consistent/state_well_typed/accounts_well_typed/context` facts as in nearby lemmas, and pass a conditional driver-IH proof that only specializes the original driver IH after `returnData = [] /\ IS_SOME drv` is known.

#### Not to try
Do not phrase this helper with the huge generated prefix implication seen in E0129; that reproduces the mismatch. Do not use `AllCaseEqs()` or broad global `gvs` to mine the driver premise. Do not manually instantiate the continuation theorem with a long list of generated prefix variables from the Resume; the helper should own those variables by ordinary case splits.

### C0.2.1.3.3: Static ExtCall Resume blocked stop-state under straightforward-proof constraint
- Kind: `blocked_report`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: The current accepted state is intentionally blocked, not proof-complete: E0144/E0149 showed that both the helper-premise consumer route and the maintainer-approved direct branch-by-branch route reach a point where specializing the generated optional-driver IH requires broad generated-prefix simplification and times out. E0150 documented and reviewed the reverted explicit `cheat` stop-state. E0151 correctly reports that the prior C0.2.1.3.3.5 proof-unblock documentation leaf is false and must be removed.
- Checkpoint: yes
- Supersedes: C0.2.1.3.3.3, C0.2.1.3.3.5
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.3.3.1, C0.2.1.3.3.2, C0.2.1.3.3.3, C0.2.1.3.3.4, E0142, E0146, E0147, E0150, E0151
- Invalidates prior progress/evidence: C0.2.1.3.3.5

#### Progress note
This replaces the stale direct-driver proof-completion/unblock subtree with the reviewed stop-state. Progress from the proved helper, cleanup, historical blocked reports, and E0150 documentation remains valid. The C0.2.1.3.3.5 leaf is invalidated because it asked for false proof-completion documentation after the accepted blocked state.

#### Summary
- Static `Expr_Call_ExtCall_result_static` remains intentionally at the explicit `cheat` placeholder.
- The theorem is not declared false, but the permitted straightforward proof routes have been exhausted under the maintainer clarification.
- Stable progress retained: the after-update continuation helper, cleanup of failed experiments, and blocked-status documentation.
- No downstream nonstatic ExtCall work is authorized from this subtree.
- The stale C0.2.1.3.3.5 proof-unblock documentation leaf is removed/invalidated.

#### Description
This subtree now records the accepted stop-state for static ExtCall, rather than scheduling further proof-completion documentation. The executor should not try to prove the static Resume, should not construct long generated-prefix adapter theorems, and should not document the obligation as unblocked. The only remaining operational action tied to this subtree is preserving the already reviewed E0150 documentation checkpoint in git if the working tree/build state is still appropriate.

#### Approach
Treat this subtree as blocked pending a new proof architecture or user/maintainer direction. If committing reviewed progress, inspect `git status` and `git diff`, stage only task-owned tracked changes under `semantics/prop`, and do not stage legacy/tmp untracked files. Do not edit evaluator/semantics definitions or files outside `semantics/prop`.

#### Not to try
Do not revive the C0.2.1.3.3.5 premise that the static ExtCall proof was completed or unblocked. Do not use broad `simp`/`gvs`, whole-prefix `AllCaseEqs()`, huge `metis_tac`, or long generated-prefix adapter theorems to recover the driver premise from the top-level Resume context. Do not proceed to nonstatic ExtCall work from this blocked static state.

#### Argument
The accepted evidence establishes a proof-architecture stop, not a mathematical refutation. The static ExtCall Resume's generated optional-driver IH is guarded by the full monadic ExtCall prefix. The previously proved after-update continuation helper requires a compact conditional driver-IH premise, but attempts to derive that premise from the generated context require simplifying/replaying the full generated prefix and time out. The direct linear branch-by-branch attempt avoided early broad cleanup, but in the success continuation branch it still needed the same forbidden generated-prefix simplification to specialize `driver_ih`. Therefore the only sound local strategy is to preserve the explicit cheat and document the blocked state until a genuinely new architecture is approved.

#### Definition design
No definition changes are authorized. The failure is not in evaluator semantics but in the proof interface between the generated mutual-recursion IH and the desired continuation helper. Any future architecture must provide a small boundary interface that can be consumed in the concrete success continuation without replaying the entire generated ExtCall prefix; until such an interface is approved and probed, this subtree remains blocked.

#### Code structure
All relevant source/documentation changes must remain under `semantics/prop`. The source `semantics/prop/vyperTypeStmtSoundnessScript.sml` should continue to contain explicit `cheat` placeholders for `Expr_Call_ExtCall_result_static` and `Expr_Call_ExtCall_result_nonstatic` in the current blocked state. `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` is the place to record the blocked status and retained stable progress. Do not commit unrelated untracked legacy/tmp files.

### C0.2.1.3.3.1: Retain after-state-update ExtCall continuation helper with conditional driver IH
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Already proved and reviewed in E0142/E0145. The helper remains a valid theorem and useful background, even though E0144/E0149 showed it is not the right central consumer interface for completing the static Resume from the generated IH.
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.3.3.1, E0142, E0145

#### Progress note
Carried forward unchanged as stable proved infrastructure. It does not unblock the static Resume by itself.

#### Summary
- Keep the proved `extcall_after_state_update_tail_sound_cond_driver_ih` helper.
- It remains sound and reviewed.
- It should not be treated as a completed consumer proof for the static Resume.
- No executor work remains on this leaf.

#### Statement
Retain the existing proved helper theorem `extcall_after_state_update_tail_sound_cond_driver_ih` in `semantics/prop`.

#### Approach
No action unless a build audit reveals accidental regression. The helper is historical stable infrastructure and should remain in source.

#### Not to try
Do not attempt to derive its conditional driver-IH premise from the generated static Resume context as a way to finish ExtCall; that route is the blocked E0144/E0149 path.

### C0.2.1.3.3.2: Cleaned failed static Resume consumer experiment
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: Already completed and reviewed in E0146: partial failed consumer proof edits were removed while preserving the proved helper.
- Dependencies: C0.2.1.3.3.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.3.3.2, E0146

#### Progress note
Carried forward as completed cleanup; no further cleanup is scheduled here.

#### Summary
- Failed proof experiment cleanup remains valid.
- The source should not contain the abandoned consumer attempt.
- The explicit static Resume cheat is intentional in the stop-state.
- No executor work remains on this leaf.

#### Approach
No action unless the abandoned failed proof text reappears. A normal source audit/build is sufficient if touched accidentally.

#### Not to try
Do not restore the failed helper-consumer proof attempt.

### C0.2.1.3.3.3: Historical blocked design report for generated-IH mismatch
- Kind: `blocked_report`
- Risk: 1
- Work priority: 20
- Work units: 0
- Rationale: Already completed in E0147 and superseded by the more precise E0150 stop-state. It remains valid historical documentation of the generated-IH mismatch.
- Dependencies: C0.2.1.3.3.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.3.3.3, E0147

#### Progress note
Carried forward as historical documentation. The operative current status is C0.2.1.3.3.4/E0150.

#### Summary
- Records the earlier generated-IH proof-interface mismatch.
- Superseded operationally by the E0150 stop-state but still accurate history.
- No executor work remains on this leaf.

#### Approach
No action. Preserve only if useful for the task plan's history; do not treat it as an authorization for renewed proof attempts.

#### Not to try
Do not use this older report to argue that all future architectures are impossible; it only blocks the attempted generated-prefix simplification route.

### C0.2.1.3.3.4: Accepted stop-state for static ExtCall Resume cheat
- Kind: `blocked_report`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: E0150 was reviewed and accepted: the source has the explicit `Expr_Call_ExtCall_result_static` cheat, the plan documentation records the E0144/E0149 blocked proof-architecture status, and `holbuild` completed on the reverted source. This leaf is the correct current static ExtCall status.
- Dependencies: C0.2.1.3.3.3
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.3.3.4, E0150

#### Progress note
Carried forward as the reviewed current stop-state. It replaces any expectation that static ExtCall was proved or unblocked.

#### Summary
- Preserve the reviewed E0150 blocked static ExtCall state.
- `Expr_Call_ExtCall_result_static` remains an explicit `cheat`.
- Documentation records why permitted straightforward proof attempts stopped.
- If still clean, the executor may commit this stable task-owned checkpoint without staging unrelated files.

#### Statement
Current source state: `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]: cheat QED` remains intentional pending new architecture.

#### Approach
Before committing, run `git status` and inspect tracked diffs. Stage only relevant tracked files under `semantics/prop`; do not use `git add -A`; do not GPG sign the commit. If the build state has changed or unrelated diffs are present, stop and report rather than mixing changes.

#### Not to try
Do not alter the Resume cheat or document the static ExtCall obligation as proved/unblocked. Do not proceed to `Expr_Call_ExtCall_result_nonstatic` while static ExtCall is blocked.

### C0.2.1.3.4: Audit static ExtCall state branch build and remaining cheats
- Kind: `proof_audit`
- Risk: 1
- Work priority: 30
- Work units: 1
- Rationale: After the helper and Resume refactor, validation is mechanical: target theory builds and the static state-well-typed cheat is gone. Nonstatic ExtCall remains separate.
- Dependencies: C0.2.1.3.3
- Checkpoint: yes
- Supersedes: C0.2.1.3.3
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.3.3

#### Progress note
Replaces the previous audit leaf only to update dependencies and scope after the helper-based repair.

#### Summary
Run the target build for `vyperTypeStmtSoundnessTheory`. Confirm the explicit cheat in the static ExtCall success state branch has been removed. Confirm no files outside `semantics/prop` were edited. Do not treat the separate nonstatic ExtCall cheat as part of this component.

#### Approach
Use `holbuild` on the target theory after the edit. Inspect the static Resume region around the old line 17455 to ensure there is no remaining `cheat` for the static success state branch. If the helper proof required broad generated-prefix reconstruction, stop and escalate rather than committing.

#### Not to try
Do not start proving the nonstatic ExtCall branch in this audit. Do not make cleanup edits outside `semantics/prop`.

### C0.2.1.4: Close nonstatic ExtCall result through linear success-continuation discharge
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: E0139 raises this subtree's old direct-consumer strategy to a mismatch, but the maintainer clarification explicitly authorizes the replacement: split the nonstatic ExtCall prefix linearly and invoke the existing success-continuation boundary only at the concrete success branch. The already-proved nonempty and projected-state lemmas remain useful reference/support, but the final leaf no longer depends on direct top-level application of the projected lemma.
- Supersedes: C0.2.1.4
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.4.1, C0.2.1.4.2, E0139

#### Progress note
Replaces the prior parent guidance that expected a short projected-state lemma consumer. C0.2.1.4.1 and C0.2.1.4.2 remain closed and carried forward; E0139 is carried as negative evidence against the old final-leaf interface.

#### Summary
- Nonstatic ExtCall result remains the required proof obligation.
- C0.2.1.4.1 and C0.2.1.4.2 are retained as proved support/reference lemmas.
- The old short consumer of `extcall_nonstatic_projected_state_well_typed` is abandoned.
- The final Resume must step through the nonstatic evaluator prefix one operation at a time.
- The generated optional-driver IH is used only after reaching the concrete success-continuation branch.

#### Argument
The successful-arguments nonstatic ExtCall evaluation has a monadic prefix: argument decoding, nonstatic value extraction, calldata construction, account/code checks, transient-storage fetch, `run_ext_call`, success check, account/transient updates, then either optional driver evaluation or ABI return decoding. State well-typedness is immediate in early error branches because evaluation returns before state-destructive success updates, and in the final branch it is exactly the guarantee of `extcall_success_continuation_state_well_typed`. The generated mutual-recursion IH is not an unconditional theorem at the top of the Resume; it is guarded by the generated prefix facts. Therefore the proof must first split the prefix until those facts are concrete assumptions, then discharge the conditional driver premise of `extcall_success_continuation_state_well_typed` from the generated IH.

#### Definition design
No evaluator or semantics definitions may change. The usable boundary at the success tail is `extcall_success_continuation_state_well_typed`, whose driver-IH premise is conditional on `returnData = [] /\ IS_SOME drv`; this matches the point where the optional driver is actually evaluated. `extcall_nonstatic_projected_state_well_typed` remains a valid proved lemma but is not the right consumer interface for the suspended Resume because it requires a compact unconditional driver premise before the generated prefix guard has been discharged. Failure sign: if the proof needs a long generated-prefix adapter theorem, a long `qspecl_then` list over prefix variables, or whole-prefix `AllCaseEqs()` cleanup, stop and escalate.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Keep existing local helper theorems in place. Replace only the body of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]`; do not edit evaluator/semantics definitions and do not edit outside `semantics/prop`. The proof should be structurally similar to the proof of `extcall_nonstatic_projected_state_well_typed` around lines 9953--10016, but the final success branch should consume the generated Resume IH rather than requiring the compact premise of that helper.

### C0.2.1.4.1: Carry forward the nonstatic runtime-typed argument nonempty helper
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: Already proved and still directly supports the linear proof by establishing the value argument exists for the nonstatic `TL vs` access.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.4.1, E0137

#### Progress note
No change from the proved component; retained under the replaced parent subtree.

#### Summary
`extcall_nonstatic_args_runtime_typed_nonempty` is proved and carried forward. Use it after deriving the nonstatic argument runtime-typing destruct facts.

### C0.2.1.4.2: Carry forward the nonstatic projected-state boundary lemma
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 20
- Work units: 0
- Rationale: Already proved. Although it is no longer the direct final Resume consumer, its proof is a reliable template for the permitted linear nonstatic evaluator split and its helper facts remain available.
- Dependencies: C0.2.1.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.4.2, E0138

#### Progress note
Carried forward as proved support/reference. E0139 invalidates only the top-level consumer use, not the lemma itself.

#### Summary
`extcall_nonstatic_projected_state_well_typed` is proved and retained. Do not use it directly at the initial Resume goal; use its proof shape as a guide.

### C0.2.1.4.3: Resume the nonstatic ExtCall result proof by linear prefix splitting
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: The previous Risk 2 rating was wrong for the direct projected-lemma consumer. The replacement approach is low-risk because it follows a proved local proof script (`extcall_nonstatic_projected_state_well_typed`) and uses `extcall_success_continuation_state_well_typed`, whose conditional driver premise matches the generated IH only at the success branch.
- Dependencies: C0.2.1.4.1, C0.2.1.4.2
- Checkpoint: yes
- Supersedes: C0.2.1.4.3
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.4.1, C0.2.1.4.2, E0139

#### Progress note
The obligation remains the same Resume cheat, but E0139 replaces the proof route. Do not count the failed direct `irule`/`drule_all` attempts as progress except as negative evidence guiding this replacement.

#### Summary
- Close `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]`.
- Do not apply `extcall_nonstatic_projected_state_well_typed` directly at the initial `state_well_typed st'` goal.
- Unfold the nonstatic ExtCall evaluator linearly, mirroring the proved helper at lines 9953--10016.
- Close error branches immediately and keep only one success path active.
- In the final success continuation, use `extcall_success_continuation_state_well_typed` and discharge its conditional driver premise from the generated prefix-guarded IH.

#### Description
The failed episode shows the compact boundary lemma's premise does not match the suspended Resume context. The replacement proof should keep the generated optional-driver IH saved, split the ExtCall prefix until the success continuation is concrete, and only then specialize/match the generated IH. This is exactly the careful branch-by-branch proof style permitted by the maintainer clarification.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  (* prove the nonstatic ExtCall result branch's `state_well_typed st'` goal *)

#### Approach
Begin with `rpt gen_tac >> strip_tac`, save the generated optional-driver IH with `pop_last_assum`, simplify the `if F` MAP fact to the nonstatic shape, and name the successful `eval_exprs cx es st = (INL vs,args_st)` branch. Then follow `extcall_nonstatic_projected_state_well_typed`: derive `extcall_nonstatic_args_runtime_typed_dest` and nonempty facts, move the call evaluation to the goal, unfold `Once evaluate_def` plus `bind_def`, `ignore_bind_def`, `check_def`, `assert_def`, `return_def`, `raise_def`, `lift_option_type_def`, `lift_option_def`, `get_accounts_def`, `get_transient_storage_def`, `update_accounts_def`, `update_transient_def`, and rewrite with the known `eval_exprs`. Split `build_ext_calldata`, empty-code check, `run_ext_call`, and the success flag; close each failing branch immediately. At the success tail, prove `accounts_well_typed accounts'` using `run_ext_call_accounts_well_typed`, establish `runtime_consistent env cx args_st`, then `irule extcall_success_continuation_state_well_typed`; for its conditional driver-IH premise, strip `returnData = [] /\ IS_SOME drv` and use the saved generated IH by matching its conclusion, solving the generated prefix antecedent from the local split equations by simplification.

#### Not to try
Do not retry `irule extcall_nonstatic_projected_state_well_typed` or `drule_all extcall_nonstatic_projected_state_well_typed` at the initial Resume goal; E0139 shows the compact premise is unavailable there. Do not introduce broad generated-prefix adapter theorems, do not use whole-prefix `gvs`/`AllCaseEqs()` cleanup to recover the driver premise, and do not manually instantiate the generated IH with a long list of prefix variables. If the final driver-IH discharge cannot be done by matching the generated IH conclusion and simplifying the already-split prefix facts, stop and escalate with that exact subgoal.

### C0.2.1.5: Remove obsolete ExtCall compact-boundary artifacts after both branches build
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 40
- Work units: 1
- Rationale: Stale artifacts suggesting the invalid compact/generated-prefix approach should be removed after both branches build.
- Dependencies: C0.2.1.4
- Supersedes: C0.2.1.4
- Progress transition: `replacement`

#### Progress note
Retains the old cleanup intent but schedules it after the new branch proofs.

#### Summary
- Remove or quarantine unused ExtCall artifacts encoding the invalidated compact strategy.
- Keep successful local tail theorems and branch proofs.
- Build after cleanup.

#### Approach
Search only within `semantics/prop`. Delete misleading unused helper statements/comments after both static and nonstatic branches build.

#### Not to try
Do not clean up before branch proofs are stable.

### C0.2.2: Nonstatic ExtCall_result branch via conditional continuation helper
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The episode shows the nonstatic prefix split is straightforward and the only mismatch is the proof interface at the success tail. Existing local theorem `extcall_success_continuation_sound_cond_driver_ih` has exactly the right interface: it needs the optional-driver IH only under `returnData = [] /\ IS_SOME drv`, matching the generated prefix after the branch has been split. This avoids broad simplification and avoids a generated-prefix adapter theorem.
- Supersedes: C0.2.2
- Progress transition: `replacement`
- Carries progress/evidence from: E0134
- Invalidates prior progress/evidence: C0.2.2@old-unconditional-tail

#### Progress note
E0134's prefix-splitting work remains valid evidence, but its final unconditional-helper tail is the wrong interface. This replacement carries forward the established successful prefix path and invalidates only the old instruction to invoke `extcall_success_continuation_sound` directly.

#### Summary
- Replace the old direct `extcall_success_continuation_sound` tail with the conditional helper route.
- Keep the accepted linear nonstatic ExtCall prefix split from E0134: argument typing, calldata, account-code check, `run_ext_call ... (SOME amount)`, revert/success.
- In the single success branch, prove only the conditional driver premise required by `extcall_success_continuation_sound_cond_driver_ih`.
- Derive that conditional premise by `strip_tac` on `returnData = [] /\ IS_SOME drv`, then `mp_tac driver_ih >> simp[...]` using the already-split prefix facts; do not `qspecl` the generated prefix manually.
- The old leaf's unconditional-helper approach is invalidated; the prefix progress from E0134 still supports the new proof shape.

#### Description
This subtree closes `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` without changing semantics or files outside `semantics/prop`. The key repair is not more prefix splitting; it is using the existing conditional continuation lemma at the success tail so that the generated optional-driver IH is consumed only under the exact branch condition where it is valid.

#### Approach
Use the same branch-local linear proof skeleton from E0134 up to the success case after `Cases_on x'0`. In the success case, do not invoke `extcall_success_continuation_sound`; invoke `extcall_success_continuation_sound_cond_driver_ih` (or the state projection if the current subgoal is only `state_well_typed st'`). For its driver premise, assert `returnData = [] /\ IS_SOME drv ==> !env0 st0 res0 st0'. ...` locally by stripping the condition and then pushing the saved `driver_ih` theorem with `mp_tac driver_ih >> simp[...]`, relying on the already-present prefix equalities rather than enumerating generated variables.

#### Not to try
Do not try to recover an unconditional optional-driver IH from the suspended branch context. Do not use broad `gvs[AllCaseEqs()]` or whole-prefix simplification to make the generated prefix disappear. Do not write a long adapter theorem whose statement reproduces the generated ExtCall prefix. Do not manually `Q.SPECL` the generated prefix variable list; E0134 shows that is brittle and unnecessary if the saved `driver_ih` is pushed back to the goal after the prefix facts are in context.

#### Argument
The nonstatic ExtCall evaluator first evaluates arguments and, in the successful argument case, requires an address and value argument. The already-proved `extcall_nonstatic_args_runtime_typed_dest` gives `target_addr` and `amount`, after which the evaluator's monadic prefix is deterministic: build calldata from `TL (TL vs)`, check target code, run the external call with `SOME amount`, then either close error/revert cases immediately or enter the success continuation. The success continuation updates accounts and transient storage and then either evaluates the optional driver when `returnData = [] /\ IS_SOME drv`, or ABI-decodes `returnData`. The theorem `extcall_success_continuation_sound_cond_driver_ih` is designed for exactly this point: the ABI-decode path needs no driver IH, while the driver path needs only the generated driver IH under the same branch condition. Therefore the proof is true without manufacturing a global unconditional IH.

#### Definition design
No definition changes are permitted or needed. The proof interface is the local helper stack already in `vyperTypeStmtSoundnessScript.sml`: `extcall_nonstatic_args_runtime_typed_dest` for destructing typed nonstatic arguments, `run_ext_call_accounts_well_typed` for returned accounts, `update_accounts_transient_runtime_consistent`/`runtime_consistent_def` for the updated state, and especially `extcall_success_continuation_sound_cond_driver_ih` for the continuation. Failure sign: if the proof again requires copying or adapting the whole generated monadic prefix into a theorem statement, stop; the helper is being applied too early or the saved `driver_ih` is not being pushed with the prefix facts in scope.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Do not edit evaluator definitions or files outside `semantics/prop`. The old `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` is replaced by the linear branch proof. Any tiny local assertion for the conditional driver premise should live inside the success branch; do not add a global generated-prefix adapter theorem.

### C0.2.2.1: Probe the branch-local conditional driver premise
- Kind: `proof_probe`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: This is the exact stuck point from E0134, narrowed to a branch-local assertion. It should be low risk because the generated `driver_ih` antecedent is precisely the prefix facts that are already assumptions in the success branch; pushing the saved theorem with `mp_tac driver_ih >> simp[...]` lets HOL instantiate the generated variables instead of requiring manual `qspecl`.
- Checkpoint: yes
- Carries progress/evidence from: E0134

#### Progress note
New probe extracted from the exact E0134 stuck point; carries forward the successful prefix state that makes the conditional assertion meaningful.

#### Summary
- Edit only the nonstatic success branch in the Resume proof.
- After the `run_ext_call ... (SOME amount)` success split and account-typing fact, add a local assertion of the conditional driver IH.
- Prove it by `strip_tac` on `returnData = [] /\ IS_SOME drv`, then use the saved `driver_ih` with `mp_tac driver_ih >> simp[...]` while all generated prefix equalities are still in context.
- Do not enumerate the generated prefix variables manually.
- Checkpoint here because this is the repaired interface that de-risks the rest of the branch.

#### Description
The deliverable is not a standalone theorem; it is a successful local proof fragment inside the nonstatic Resume success case showing the premise shape required by `extcall_success_continuation_sound_cond_driver_ih`. If the current goal is already a state-only projection, the same local assertion should be sufficient for `extcall_success_continuation_state_well_typed`.

#### Statement
Local assertion inside `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` success branch:
```sml
returnData = [] /\ IS_SOME drv ==>
  !env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\
    context_well_typed cx /\ accounts_well_typed st0.accounts /\
    functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
    (well_typed_expr env0 (THE drv) ==>
     state_well_typed st0' /\ env_consistent env0 cx st0' /\
     accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
     case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)
```

#### Approach
Keep `driver_ih` saved by the existing `pop_last_assum (fn driver_ih => ...)`. At the success tail, before applying the continuation helper, prove the assertion with `strip_tac`; then use `mp_tac driver_ih` followed by `simp[...]` including the branch condition and the prefix definitions/equalities already exposed (`bind_def`, `return_def`, `assert_def`, `update_accounts_def`, `update_transient_def` as needed). If `simp` leaves only the desired quantified IH, accept it; if it leaves prefix obligations, add only the specific rewrite/fact for that already-split prefix operation.

#### Not to try
Do not call `first_x_assum drule_all` blindly; E0134 indicates it may pick or shape the wrong implication. Do not use explicit `Q.SPECL` over all generated variables. Do not move this into a reusable global lemma with the whole generated prefix in its statement.

### C0.2.2.2: Close and audit the nonstatic ExtCall_result Resume branch
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: Once the conditional driver premise is available, the rest is a standard application of the existing continuation helper plus already-proved ExtCall facts. Error and revert branches were reported straightforward in E0134.
- Dependencies: C0.2.2.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0134
- Invalidates prior progress/evidence: C0.2.2@old-unconditional-tail

#### Progress note
This leaf refines the old C0.2.2 proof attempt by preserving the linear split and changing only the success-tail interface.

#### Summary
- Complete the nonstatic Resume proof using the C0.2.2.1 conditional driver premise.
- Use `extcall_success_continuation_sound_cond_driver_ih` for full continuation obligations, or `extcall_success_continuation_state_well_typed` if the resumed subgoal is only the state conjunct.
- Supply `accounts_well_typed accounts'` from `run_ext_call_accounts_well_typed` and runtime consistency from the argument-state facts.
- Close calldata/account-code/run failure and revert cases immediately with the local monadic rewrites.
- Final audit: `holbuild` target succeeds and the `Expr_Call_ExtCall_result_nonstatic` cheat is gone.

#### Description
This component finishes the task-scoped theorem branch after the repaired driver-premise probe succeeds. It should be a direct continuation of the E0134 proof skeleton, with the tail helper changed from unconditional to conditional.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` in `semantics/prop/vyperTypeStmtSoundnessScript.sml` has no `cheat` and the target theory builds.

#### Approach
In the final success branch, invoke the conditional continuation helper at the point where the evaluator has just performed `assert success`, `update_accounts`, and `update_transient`, with `accounts' = x'2`, base state `args_st`, `returnData = x'1`, and transient storage `x'3` (or the actual names produced by the split). Prove helper side conditions from `runtime_consistent_def`, `functions_well_typed`, `well_typed_opt`, `well_formed_type`, `(!e. drv = SOME e ==> expr_type e = ret_type)`, and the local conditional driver premise from C0.2.2.1. Use `rewrite_tac[GSYM no_type_error_result_def]` only if needed to align the postcondition goal, as in the E0134 skeleton.

#### Not to try
Do not revert to `extcall_success_continuation_sound` unless an unconditional driver IH is already directly in context. Do not broaden the proof to the whole `Expr_Call_ExtCall_result` parent theorem. Do not change semantics definitions or evaluator behavior.

### C0.2.3: Validate ExtCall_result integration has no stale cheats or blocked descendants
- Kind: `integration_validation`
- Risk: 1
- Work priority: 20
- Work units: 2
- Rationale: After the two branch proofs, validation is mechanical: the local cheats should be gone and the theory should build from the restored baseline.
- Dependencies: C0.2.1, C0.2.2
- Supersedes: C0.2.2@previous
- Progress transition: `reclassified`
- Carries progress/evidence from: C0.2.2@previous, TO_type_system_rewrite-20260601T081233Z_m2390_t001

#### Progress note
The previous validation component is moved from C0.2.2 to C0.2.3 because C0.2 now has explicit static and nonstatic proof leaves before validation.

#### Summary
- Search `vyperTypeStmtSoundnessScript.sml` for the two ExtCall_result suspended-branch cheats and remove/replace any stale proof fragments.
- Build `vyperTypeStmtSoundnessTheory` after C0.2.1 and C0.2.2.
- Confirm the outer `Expr_Call_ExtCall_result` Resume still handles the argument-error branch and delegates only to the proved static/nonstatic branches.
- Confirm no forbidden broad generated-prefix adapter theorem was added for ExtCall.
- Record the build result and any remaining task-scoped cheats before moving to downstream components.

#### Description
This is an audit/build leaf, not a new proof design. It closes C0.2 only if the static and nonstatic branch proofs are real, the theory builds, and no stale suspended ExtCall_result placeholder remains.

#### Statement
Build/audit obligation: `holbuild` target `vyperTypeStmtSoundnessTheory` succeeds and the ExtCall_result static/nonstatic `cheat` placeholders are gone.

#### Approach
Use targeted grep/search in `semantics/prop/vyperTypeStmtSoundnessScript.sml` for `Expr_Call_ExtCall_result_static`, `Expr_Call_ExtCall_result_nonstatic`, and nearby `cheat` occurrences. Then run the task-approved build target. If the build fails in unrelated dirty-state code, stop and report with the exact failure rather than editing outside this C0.2 scope.

#### Not to try
Do not run broad cleanup or edit outside `semantics/prop`. Do not treat a successful build with remaining local `cheat` placeholders in the ExtCall_result branches as closure. Do not proceed to C0.3/RawCallTarget until this validation is complete.

### C0.3: Prove RawCallTarget expression-call soundness through local tail boundaries
- Kind: `proof_branch`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: E0106 isolated the problem: the Resume context is clean and the theorem is not suspected false, but the monadic RawCallTarget tail combines argument destructors, external-call side effects, flag-dependent return values, and result typing. Splitting those obligations into local helpers makes each proof analogous to already-proved neighboring helpers.
- Dependencies: C0.1
- Supersedes: C0.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0106

#### Progress note
E0106 remains useful diagnostic evidence: it proved the Resume is not polluted by ExtCall optional-driver prefix assumptions and identified the missing RawCallTarget tail boundary. The old direct-proof obligation is replaced by this helper-based decomposition.

#### Summary
- Replace the failed direct RawCallTarget proof with local boundary lemmas in `semantics/prop/vyperTypeStmtSoundnessScript.sml`.
- First prove a runtime-typed argument destructor lemma for address/bytes/uint256 raw_call arguments.
- Then prove the flag-dependent returned value has `expr_result_typed` for `Call (raw_call_return_type flags) (RawCallTarget flags) es NONE`.
- Then prove one tail-result helper that owns the monadic chain, uses `run_ext_call_accounts_well_typed` and update preservation, and hides case-thrashing from the Resume.
- Finally the Resume should look like RawLog: unfold the evaluator prefix, apply expression-list IH, discharge argument typing, and invoke the tail helper.

#### Description
The failed episode showed that applying `AllCaseEqs()` and `metis_tac[raw_call_return_type_well_formed]` at the consumer leaves a huge, mixed obligation. This subtree changes the proof interface: RawCallTarget gets the same kind of local tail abstraction already used for RawLog/RawRevert/Selfdestruct, so the main mutual proof branch is only a consumer of the boundary theorem.

#### Approach
Keep all new lemmas local in `vyperTypeStmtSoundnessScript.sml`, near the existing argument/tail helpers around lines 10289-10810. Use the do-form definitions for helper proofs where possible; if the consumer produces the nested case form after prefix splitting, add a `_simp` variant matching that shape rather than redoing semantic proof in the Resume.

#### Not to try
Do not continue broad `gvs[bind_def, AllCaseEqs()]` over the entire RawCallTarget tail in the Resume. Do not `PairCases_on result` before the `lift_option (run_ext_call ...)` branch has been split to bind `result` as an actual pair. Do not encode a long generated-prefix adapter theorem; this branch has only the expression-list IH and does not need the ExtCall optional-driver workaround.

#### Argument
RawCallTarget soundness factors into three independent facts. (1) From `exprs_runtime_typed` and the well-typed raw_call argument shape, the three runtime values have the destructors required by the evaluator: address target, bytes calldata, and nonnegative uint amount. (2) External-call side effects preserve account well-typedness by `run_ext_call_accounts_well_typed`; after `update_accounts` and `update_transient`, `update_accounts_transient_runtime_consistent` reconstructs `runtime_consistent`, hence final state/env/accounts conjuncts. (3) The returned value is exactly one of the four branches of `raw_call_return_type`: `NoneV`, `BytesV (TAKE n returnData)`, `BoolV success`, or `ArrayV (TupleV [...])`; `raw_call_return_type_well_formed` plus direct evaluation/value-typing definitions prove `expr_result_typed`. The tail helper packages these facts so the mutual proof only handles evaluator prefix and expression-list IH.

#### Definition design
No evaluator or semantics definitions should change. The proof interface should consist of local theorems with conclusions matching the consumer: argument destructors, returned value typing, and a tail-result theorem whose conclusion is the full postcondition `state_well_typed ∧ env_consistent ∧ accounts_well_typed ∧ no TypeError ∧ expr_result_typed`. A failed/hard proof that repeats the whole RawCallTarget monadic prefix in the Resume is evidence that the helper statement does not match the consumer shape and should be adjusted locally.

#### Code structure
Place `raw_call_args_runtime_typed_dest` beside `send_args_runtime_typed_dest` / `raw_log_args_runtime_typed_dest`. Place `raw_call_return_value_typed` and `raw_call_tail_result_sound` / `_simp` near existing tail helpers before the RawLog/RawRevert section. Replace only the `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` body at line ~17557. Stay within `semantics/prop`.

### C0.3.1: Derive RawCallTarget runtime argument destructors
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: This is the RawCallTarget analogue of already-proved `send_args_runtime_typed_dest` and `raw_log_args_runtime_typed_dest`; it is list-shape and value-typing inversion only.
- Carries progress/evidence from: E0106

#### Progress note
Added because E0106 showed destructor facts were part of the large mixed tail goal rather than available as a boundary lemma.

#### Summary
- Prove the typed raw_call argument list yields all three evaluator destructors.
- Assumptions match the well-typed RawCallTarget branch: length 3, address at index 0, bytes at index 1, uint256 at index 2.
- This closes target/data/value TypeError branches before the external call tail.
- Use `exprs_runtime_typed_def`, `LIST_REL_EL_EQN`, `evaluate_type_def`, and `value_has_type_def` as in nearby argument helpers.

#### Statement
Theorem raw_call_args_runtime_typed_dest[local]:
  exprs_runtime_typed env es vs /\
  LENGTH es = 3 /\
  HD (MAP expr_type es) = BaseT AddressT /\
  EL 1 (MAP expr_type es) = BaseT (BytesT bd) /\
  EL 2 (MAP expr_type es) = BaseT (UintT 256) ==>
  ?target_addr calldata amount.
    dest_AddressV (HD vs) = SOME target_addr /\
    dest_BytesV (EL 1 vs) = SOME calldata /\
    dest_NumV (EL 2 vs) = SOME amount

#### Approach
Follow `raw_log_args_runtime_typed_dest`, but handle the third element like `send_args_runtime_typed_dest`. After rewriting `exprs_runtime_typed_def`, obtain `LENGTH vs = LENGTH es` and elementwise `evaluate_type` / `value_has_type` facts; case-split three-element `es`, `tvs`, and `vs` as needed. For the uint case, use the same `0 <= i` to `Num i` conversion pattern as `send_args_runtime_typed_dest`.

#### Not to try
Do not unfold the RawCallTarget evaluator here. This lemma is only about typed runtime argument values and destructors; keeping it evaluator-free is what makes it reusable in the tail helper.

### C0.3.2: Prove flag-dependent RawCallTarget return value typing
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: The proof is finite case analysis over `flags.rcf_revert_on_failure` and `flags.rcf_max_outsize = 0`, using `raw_call_return_type_well_formed` and direct value-typing definitions.
- Dependencies: C0.1
- Carries progress/evidence from: E0106

#### Progress note
Added to isolate the flag-dependent part of the 9 leftover goals from E0106.

#### Summary
- Package the four return-shape branches of raw_call into one local typing helper.
- Conclude `expr_result_typed` for `Call (raw_call_return_type flags) (RawCallTarget flags) es NONE`.
- Cover `NoneV`, dynamic bytes, `BoolV`, and tuple/array result shapes.
- Remove flag/type arithmetic from the tail and Resume proofs.

#### Statement
Prove one or more local theorems, with the main consumer-facing conclusion of this shape:

  flags.rcf_max_outsize < dimword(:256) ==>
  expr_result_typed env
    (Call (raw_call_return_type flags) (RawCallTarget flags) es NONE)
    (Value
      (if flags.rcf_revert_on_failure then
         if flags.rcf_max_outsize = 0 then NoneV
         else BytesV (TAKE flags.rcf_max_outsize returnData)
       else if flags.rcf_max_outsize = 0 then BoolV success
       else ArrayV (TupleV [BoolV success;
                            BytesV (TAKE flags.rcf_max_outsize returnData)])))

#### Approach
Case-split `flags`, then the two tests exposed by `raw_call_return_type_def`. Rewrite `expr_result_typed_def`, `expr_runtime_typed_def`, `expr_type_def`, `toplevel_value_typed_def`, `value_has_type_def`, `evaluate_type_def`, `raw_call_return_type_def`, `materialise_def`, and `is_HashMapRef_def`; use `raw_call_return_type_well_formed` for the well-formed/evaluate-type side condition if direct rewriting leaves it. Keep this lemma independent of state and monadic bind definitions.

#### Not to try
Do not prove this inside `raw_call_tail_result_sound` by one huge `metis_tac`; E0106 showed that mixing return typing with side effects and monadic cleanup leaves unreadable goals.

### C0.3.3: Prove the RawCallTarget monadic tail result boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: This is the missing proof interface identified by E0106. It can consume C0.3.1, C0.3.2, `run_ext_call_accounts_well_typed`, and `update_accounts_transient_runtime_consistent`; all TypeError sources are explicit in the tail.
- Dependencies: C0.3.1, C0.3.2
- Checkpoint: yes
- Carries progress/evidence from: E0106

#### Progress note
This is the direct repair requested by the E0106 missing-helper diagnosis.

#### Summary
- Prove a local `raw_call_tail_result_sound` or `_simp` theorem whose conclusion is the full RawCallTarget postcondition.
- The helper owns all bind/case splitting after successful `eval_exprs`.
- Close destructor/check/lift-option error cases immediately and keep one success path active.
- Use `run_ext_call_accounts_well_typed` for `accounts'` and `update_accounts_transient_runtime_consistent` after updates.
- Use C0.3.2 for the final `expr_result_typed` branch.

#### Statement
The main helper should have this consumer-facing shape (do-form or a `_simp` nested-case variant matching the Resume is acceptable):

Theorem raw_call_tail_result_sound[local]:
  !env cx es vs flags st res st' bd.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    flags.rcf_max_outsize < dimword(:256) /\
    LENGTH es = 3 /\
    HD (MAP expr_type es) = BaseT AddressT /\
    EL 1 (MAP expr_type es) = BaseT (BytesT bd) /\
    EL 2 (MAP expr_type es) = BaseT (UintT 256) /\
    ((do
        check (LENGTH vs = 3) "raw_call args";
        target_addr <- lift_option_type (dest_AddressV (HD vs)) "raw_call target";
        calldata <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
        amount <- lift_option_type (dest_NumV (EL 2 vs)) "raw_call value";
        check (~flags.rcf_is_delegate) "raw_call delegate unsupported";
        accounts <- get_accounts;
        tStorage <- get_transient_storage;
        result <- lift_option
          (run_ext_call cx.txn.target target_addr calldata
             (if flags.rcf_is_static then NONE else SOME amount)
             accounts tStorage (vyper_to_tx_params cx.txn))
          "raw_call run failed";
        (\(success,returnData,accounts',tStorage').
           do
             _ <- update_accounts (K accounts');
             _ <- update_transient (K tStorage');
             if flags.rcf_revert_on_failure then
               do
                 _ <- check success "raw_call reverted";
                 if flags.rcf_max_outsize = 0 then return (Value NoneV)
                 else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData)))
               od
             else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
             else return (Value (ArrayV (TupleV [BoolV success;
                                                  BytesV (TAKE flags.rcf_max_outsize returnData)])))
           od) result
      od) st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    case res of
    | INL tv => expr_result_typed env
                  (Call (raw_call_return_type flags) (RawCallTarget flags) es NONE) tv
    | INR _ => T

#### Approach
First apply C0.3.1 to obtain the three successful destructor equations, then push the tail equation through `bind_def`, `ignore_bind_def`, `check_def`, `assert_def`, `raise_def`, `return_def`, `lift_option_type_def`, `get_accounts_def`, `get_transient_storage_def`, `update_accounts_def`, and `update_transient_def` one operation at a time. In the success branch, split `result` only after the `lift_option (run_ext_call ...)` equation exposes it; use `run_ext_call_accounts_well_typed` to get `accounts_well_typed accounts'`, then reconstruct runtime consistency after both updates with `update_accounts_transient_runtime_consistent`. The final returned-value branch should be discharged by C0.3.2; error branches are RuntimeError or non-TypeError once destructors are known.

#### Not to try
Do not use `AllCaseEqs()` over the whole tail as the main proof method. Do not leave `result` hidden inside a nested case expression and then `PairCases_on result`; first split the `lift_option` success branch so the pair is a bound variable. If a do-form helper does not rewrite cleanly at the consumer, add a thin `_simp` theorem with the nested case statement rather than duplicating semantic reasoning in the Resume.

### C0.3.4: Replace the RawCallTarget Resume body with the boundary-helper proof
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: Once C0.3.1-C0.3.3 are available, the Resume proof is the same shape as RawLog: evaluator prefix, expression-list IH, well-typed branch inversion, and one tail-helper application.
- Dependencies: C0.3.3
- Progress transition: `refinement`
- Carries progress/evidence from: E0106

#### Progress note
E0106's context probe carries forward: the Resume has the expected single expression-list IH and no ExtCall optional-driver pollution, so a boundary-helper consumer proof is appropriate.

#### Summary
- Remove the `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`.
- Use the clean Resume context observed in E0106: one `eval_exprs` IH plus the standard expression-result/place conjunct.
- Prove the result conjunct by unfolding `well_typed_expr` and the RawCallTarget evaluator prefix, applying the IH to `eval_exprs`, and invoking the tail helper.
- Prove the place conjunct by rewriting `type_place_expr` / `well_typed_expr` as neighboring call branches do.

#### Statement
Close:

Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  ...
QED

#### Approach
Mirror the proven `Expr_Call_RawLog` Resume structure. Start with `rpt gen_tac >> strip_tac >> conj_tac`; for the expression-result conjunct, move the well-typed assumption into `mp_tac`, rewrite once with `well_typed_expr_def`, then move the evaluator equation into `mp_tac` and rewrite once with `evaluate_def`, `bind_def`, `ignore_bind_def`, `type_check_def`, `assert_def`, `return_def`, `raise_def`, `lift_option_type_def`, and `lift_option_def` only as needed to reach the `eval_exprs` split. After `eval_exprs cx es st = (INL vs,args_st)`, apply the expression-list IH, specialize the RawCallTarget typing facts, and call `raw_call_tail_result_sound` or its `_simp` variant.

#### Not to try
Do not resurrect the failed `metis_tac[raw_call_return_type_well_formed]` at the 9-goal tail. Do not perform broad cleanup over the entire monadic chain in the Resume; all tail splitting belongs in C0.3.3.

### C0.3.5: Build and audit the RawCallTarget branch locally
- Kind: `integration_validation`
- Risk: 1
- Work priority: 40
- Work units: 1
- Rationale: After the helper and Resume proofs, validation is mechanical: build the theory and verify this Resume no longer contains `cheat`.
- Dependencies: C0.3.4

#### Progress note
Added as a mechanical local validation after replacing the C0.3 proof strategy.

#### Summary
- Run the relevant `holbuild` target for `vyperTypeStmtSoundnessTheory`.
- Grep the RawCallTarget Resume region to ensure the `cheat` at line ~17558 is gone.
- Confirm no new edits outside `semantics/prop` were made.
- This component does not replace the later task-wide audit C0.4; it is only the local RawCallTarget closure check.

#### Approach
Use the normal build command already used in prior episodes. If the build fails in a helper proof, report the exact failing helper and goal; do not continue with large consumer-side case-thrashing.

#### Not to try
Do not treat this local audit as permission to skip C0.4, which still audits all task-scoped cheats after C0.1-C0.3.

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
