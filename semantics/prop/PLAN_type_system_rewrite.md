# PLAN

## Structured Components

### C0: Type-system rewrite proof obligations
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Risk now comes from the repaired static ExtCall subtree. The previous C0.4.3 high-risk boundary is replaced by low-risk generated-IH passthrough and concrete-tail leaves; omitted siblings are preserved by merge.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0

#### Progress note
Ancestor included only because dotted PLAN validation requires explicit parents; this update is scoped to C0.4 and preserves omitted siblings.

#### Summary
Ancestor grouping for task-scoped type-system rewrite proof work. This merge updates only the C0.4 static ExtCall subtree. Previously completed work outside C0.4 is not changed.

#### Argument
This ancestor is unchanged except that the static ExtCall branch is no longer treated as a broad high-risk generated-prefix problem. The repaired C0.4 strategy isolates the generated optional-driver premise as an opaque passthrough obligation before the concrete tail proof.

#### Definition design
No evaluator or semantics definitions change. The only updated interface is within the static ExtCall proof boundary under C0.4.

#### Code structure
All edits remain under `semantics/prop`, primarily `vyperTypeStmtSoundnessScript.sml`; omitted sibling subtrees keep their existing code structure.

### C0.1: Baseline audit of reachable residual cheats and authorized edit scope
- Kind: `proof_audit`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: Risk 1: mechanical grep/build audit to establish current source obligations and prevent accidental work outside scope.
- Checkpoint: yes
- Carries progress/evidence from: TO_type_system_rewrite-20260601T220715Z_m4389_t002, TO_type_system_rewrite-20260601T220715Z_m4347_t003

#### Progress note
Carries forward prior baseline evidence only as a starting point; rerun because this replacement C0 now authorizes proof work and final completion depends on the current source state.

#### Summary
- Confirm the currently reachable cheats in fresh-stack `semantics/prop` sources before editing.
- Expected obligations are `raw_call_return_type_well_formed`, `eval_all_type_sound_mutual[Expr_Call_ExtCall]` sub-suspends/cheats, and `eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`.
- Verify no source edits are needed outside `semantics/prop`.
- Build `vyperTypeStmtSoundnessTheory` and/or `vyperSemanticsHolTheory` only as baseline evidence, not as completion while cheats remain.

#### Statement
Audit obligation: source grep plus focused build establishes the exact current remaining reachable cheats under `semantics/prop` before proof edits begin.

#### Approach
Use grep for `cheat`, `CHEAT`, and the named theorem/Resume labels in `semantics/prop/*.sml`, then run a focused holbuild target if permitted by the component gate. Record any discrepancy in `STATE_type_system_rewrite.md` and stop if the residual obligations differ materially from this PLAN.

#### Not to try
Do not treat baseline build success as proof completion. Do not stage pre-existing unrelated untracked files such as legacy learning/temp artifacts.

### C0.2: Remove localized raw_call return-type well-formedness cheat
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 10
- Work units: 2
- Rationale: Risk 1: the current proof is a localized arithmetic proof around `word_size`; it already has supporting lemmas `word_size_le` and `word_size_not_lt_self` immediately above the theorem.
- Dependencies: C0.1

#### Progress note
New proof-completion leaf for the reachable builtins cheat listed in the task plan audit.

#### Summary
- Prove `raw_call_return_type_well_formed` in `vyperTypeBuiltinsScript.sml` without `cheat`.
- Use `Cases_on flags` and unfold `raw_call_return_type_def`, `well_formed_type_def`, `evaluate_type_def`, and `type_slot_size_def`.
- The only nontrivial branch is the max-outsize/word-size arithmetic; use existing `word_size_le` and `word_size_not_lt_self`.
- Build `vyperTypeBuiltinsTheory` or the next dependent focused target afterwards.

#### Statement
```sml
Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)
```

#### Approach
Keep the proof local: destruct `flags`, rewrite the return-type definition, then discharge slot-size side conditions by deriving `word_size n ≤ n`; case split on `word_size n < n`, and in the equality corner use `word_size_not_lt_self`. Avoid introducing a new arithmetic abstraction unless HOL cannot close the final numeric subgoal with `decide_tac`/existing arithmetic simps.

#### Not to try
Do not change `raw_call_return_type_def` or weaken the theorem. Do not move this into statement soundness; it is an independent builtins lemma and should be closed before larger integration work.

### C0.3: ExtCall compact branch-boundary probe from projected helper interface
- Kind: `proof_boundary_probe`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Risk 2: it is a small authorized probe using already-proved local projected helper lemmas; it deliberately checks that the new interface avoids the old generated-prefix fanout before full ExtCall integration.
- Dependencies: C0.1
- Checkpoint: yes
- Supersedes: E0223
- Progress transition: `replacement`
- Carries progress/evidence from: E0223, TO_type_system_rewrite-20260601T220715Z_m4328_t001

#### Progress note
Uses E0223 as negative evidence: the probe is successful only if it reaches/apply a compact projected helper without exposing the 9-goal generated-prefix failure shape.

#### Summary
- In `vyperTypeStmtSoundnessScript.sml`, test the replacement ExtCall proof boundary before removing the main cheat.
- Target the branch after argument evaluation succeeds, using existing `extcall_static_projected_sound` and/or `extcall_nonstatic_projected_state_well_typed` style lemmas.
- The probe should demonstrate one compact call to a projected helper from assumptions `eval_exprs ... = (INL vs,args_st)`, runtime-typed args, well-formed return type, and conditional driver IH.
- Stop/escalate if HOL again exposes generated-prefix fanout or a multi-KiB optional-driver premise before helper application.

#### Statement
Probe output: a small local theorem or temporary proof skeleton showing that a concrete ExtCall success branch can be closed by a projected helper without generated-prefix reconstruction. If kept, it should have a stable theorem name such as `extcall_static_projected_sound_from_resume_assumptions[local]`; if not needed, record the successful proof shape in the main proof edit.

#### Approach
Do not begin at the old `Expr_Call_ExtCall_result_static_success` fanout. Instead, factor the needed assumptions out of the Resume context: after `eval_exprs` succeeds and the `well_typed_expr` ExtCall case has yielded `MAP expr_type`/`well_typed_opt`/return-type facts, call the projected lemma. If the generated mutual IH for `drv` is too broad, pass it only under the projected lemma's conditional driver premise and only in the branch where `returnData = [] ∧ IS_SOME drv`.

#### Not to try
Do not run `AllCaseEqs()` over the whole evaluator prefix. Do not prove generated-prefix adapter theorems. Do not attempt to solve the old 9 generated-prefix goals individually; that is a failed boundary, not a proof obligation.

### C0.4: Static ExtCall proof-boundary repair using generated-IH passthrough then concrete tail
- Kind: `proof_boundary_refactor`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Risk 2: E0241 shows the previous branch-local tail proof exposed a generated optional-driver premise before the concrete tail. That premise is an administrative mutual-induction artifact already present in the Resume context, so close it by direct assumption matching; the remaining tail uses existing local ExtCall lemmas.
- Supersedes: C0.4@previous, C0.4.3@previous, E0241
- Progress transition: `replacement`
- Carries progress/evidence from: C0.4.1, C0.4.2, E0239, E0240
- Invalidates prior progress/evidence: C0.4.3@previous

#### Progress note
Carry forward the prefix/error work. Invalidate only the previous C0.4.3 assumption that the `SOME result` tail is immediately branch-local after `Cases_on run_ext_call`.

#### Summary
Keep the static ExtCall prefix/error subresumes that already build. After `run_ext_call` is split, first close the generated optional-driver premise by direct `MATCH_ACCEPT_TAC`/targeted assumption matching, without stripping or simplifying its prefix. Only then enter the concrete `SOME (success,returnData,accounts',tStorage')` tail. The concrete tail should use existing local boundary lemmas, not broad generated-prefix cleanup.

#### Argument
The static ExtCall proof has two distinct obligations after reaching `run_ext_call`: pass through the generated optional-driver premise required by the mutual induction package, then prove the concrete semantic tail. E0241 shows these were conflated. The generated premise goal has the same long shape as the generated IH assumption already present in the Resume context (the one existing error subresumes discard with `kall_tac`), so it should be accepted opaquely before any tail simplification. Once removed, the `NONE`, revert, non-empty-return/decode, and driver-continuation cases are ordinary monadic tail cases. State/account facts come from `run_ext_call_accounts_well_typed` and tail soundness lemmas; the driver-continuation case specializes the generated premise only once the concrete branch supplies `returnData = []` and `IS_SOME drv`.

#### Definition design
No definitions change. Treat the generated optional-driver premise as an opaque proof-interface artifact. Probe success means the large generated premise goal closes from an existing assumption of the same shape without `gvs[]`, `AllCaseEqs()`, stripping, manual prefix-variable instantiation, or a generated-prefix adapter theorem. Concrete-tail consumers should use `run_ext_call_accounts_well_typed`, `extcall_after_state_update_tail_sound`, and related local ExtCall lemmas instead of unfolding the earlier prefix.

#### Code structure
Edit only `semantics/prop/vyperTypeStmtSoundnessScript.sml`. In `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`, replace the final `cheat` with a structured proof: split `run_ext_call`, immediately discharge the generated-IH passthrough goal, delegate/keep the `NONE` subresume, then handle the concrete `SOME` tail linearly. If a tiny helper is needed, place it near the existing local `extcall_*` helper block; do not add a long theorem restating the generated prefix.

### C0.4.1: Audit continuation-helper interface and current static-success prefix
- Kind: `proof_boundary_probe`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already completed by E0239; retained as carried-forward evidence.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.4.1, E0239

#### Progress note
Still valid because it does not depend on the invalidated tail-locality assumption.

#### Summary
Carried-forward audit of the static ExtCall helper interface and prefix state. No executor work remains.

### C0.4.2: Close static ExtCall prefix error subresumes
- Kind: `mutual_resume_proof`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: Already completed by E0240; the calldata and empty-code error branches remain isolated and valid.
- Dependencies: C0.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.4.2, E0240

#### Progress note
Unaffected by the `run_ext_call` boundary repair.

#### Summary
Carried-forward static ExtCall prefix error branch proofs. No new work remains.

### C0.4.3: Close static ExtCall run/tail after generated-IH passthrough
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: Replaces the prior stuck leaf. With the generated-IH passthrough split out, remaining leaves are small and use existing subresumes/lemmas.
- Dependencies: C0.4.2
- Supersedes: C0.4.3@previous, E0241
- Progress transition: `replacement`
- Invalidates prior progress/evidence: C0.4.3@previous

#### Progress note
E0241 is accepted as valid risk-mismatch evidence and invalidates the old branch-local tail plan.

#### Summary
First close the administrative generated optional-driver premise opaquely. Keep the existing `run_ext_call = NONE` subresume/proof as the failure branch. Then prove the concrete `SOME` tail by tuple/case splitting on `success` and `returnData`, using local tail lemmas rather than generated-prefix simplification.

#### Approach
At the current cheat in `Expr_Call_ExtCall_result_static_success`, do not try to rename the `SOME` branch first. After `Cases_on run_ext_call ...`, close the leading generated-premise goal by direct assumption matching, then continue to option branches. Drive the concrete tail from the saved `(do _ od) args_st = (res,st')` equality.

#### Not to try
Do not use broad `gvs[]`, `AllCaseEqs()`, long generated-prefix adapter theorems, or `rpt strip_tac >> first_x_assum drule_all` on the generated premise; E0241 shows that path is brittle and forbidden.

### C0.4.3.a: Discharge the generated optional-driver premise by direct IH passthrough
- Kind: `proof_boundary_probe`
- Risk: 2
- Work priority: 0
- Work units: 1
- Rationale: The exact assumption shape is long, but E0241 exposes the goal and existing error subresumes confirm the same generated assumption is in context. This is targeted assumption acceptance, not a semantic proof.
- Checkpoint: yes
- Supersedes: E0241

#### Summary
After the `run_ext_call` split, close the large generated optional-driver premise by matching an existing context assumption of the same `!s'' vs ... . _` shape. This checkpoint succeeds only if it closes without `gvs[]`, prefix case cleanup, stripping, or manual instantiation.

#### Statement
In `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`, close the generated premise goal of shape `!s'' vs t ... . <ExtCall prefix conjuncts> /\ returnData = [] /\ IS_SOME drv ==> !env st res st'. ... eval_expr cx (THE drv) st = (res,st') ==> ...` directly from the existing generated-IH assumption.

#### Approach
Use targeted `qpat_x_assum` with a pattern on the final consequent involving `eval_expr cx (THE drv)` and then `MATCH_ACCEPT_TAC`/equivalent to accept the assumption wholesale. If selection is noisy, move or discard unrelated assumptions, but do not strip the generated premise. Build with a deliberate suspend after this passthrough to confirm the concrete tail is next.

#### Not to try
Do not `rpt strip_tac`; do not use `first_x_assum drule_all`; do not simplify the generated prefix.

### C0.4.3.b: Carry forward/verify the `run_ext_call = NONE` static branch
- Kind: `mutual_resume_proof`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: The `Expr_Call_ExtCall_static_run_none` subresume is already present and builds; it is a monadic runtime-error branch.
- Dependencies: C0.4.3.a
- Progress transition: `carry_forward`
- Carries progress/evidence from: Expr_Call_ExtCall_static_run_none, TO_type_system_rewrite-20260602T125148Z_m4555_t001

#### Progress note
Verify it is still referenced correctly after the repaired split; otherwise carry forward the existing proof.

#### Summary
Keep/verify the existing static `run_ext_call = NONE` subresume. It rewrites known prefix facts and yields a runtime error, so no new semantic argument is needed.

#### Approach
Only edit the suspend/reference name if the parent wrapper changes. The proof should remain a local monadic rewrite ending with `no_type_error_result_def`.

#### Not to try
Do not re-prove this branch in the parent by destructing the whole generated prefix.

### C0.4.3.c: Close the concrete `SOME` ExtCall tail
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: After C0.4.3.a removes the administrative premise, the tail follows the existing local proof pattern: destruct tuple/success, close error cases, use `run_ext_call_accounts_well_typed` and `extcall_after_state_update_tail_sound` for success.
- Dependencies: C0.4.3.a, C0.4.3.b
- Checkpoint: yes
- Supersedes: C0.4.3@previous
- Progress transition: `replacement`
- Invalidates prior progress/evidence: C0.4.3@previous

#### Progress note
Repaired executable replacement for the old C0.4.3 success-tail proof.

#### Summary
Prove the `run_ext_call = SOME result` tail after generated-IH passthrough. Rewrite only the saved monadic equality and known prefix facts, destruct `result` into `(success,returnData,accounts',tStorage')`, close `success = F` as runtime error, and prove `success = T` with existing account/state/tail lemmas. Specialize the generated driver premise only in the concrete `returnData = [] /\ IS_SOME drv` subcase.

#### Statement
Complete `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` for the branch `run_ext_call cx.txn.target target_addr x' NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn) = SOME result`.

#### Approach
Follow the static projected proof pattern already in the file: move the saved `(do _ od) args_st = (res,st')` equality, rewrite only local monad/state defs plus the concrete run result, then destruct the result tuple and `success`. For `success = T`, derive `accounts_well_typed accounts'`, establish `runtime_consistent env cx args_st`, rewrite `get_tenv cx = env.type_defs`, and invoke `extcall_after_state_update_tail_sound`.

#### Not to try
Do not simplify the entire post-run state. Do not create a long prefix adapter theorem. Do not instantiate the generated premise before the concrete success branch supplies `returnData = []` and `IS_SOME drv`.

### C0.4.4: Collapse outer static wrapper and remove obsolete static-success scaffolding
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 30
- Work units: 1
- Rationale: Once C0.4.3 closes, cleanup is mechanical and build/audit based.
- Dependencies: C0.4.3.c
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.4@previous

#### Progress note
Same cleanup obligation, refined for the generated-IH passthrough step.

#### Summary
After static success closes, remove obsolete failed-tail scaffolding, keep helpers/subresumes still used, ensure the parent Resume has no cheat, and build `vyperTypeStmtSoundnessTheory`.

#### Approach
Audit only the static ExtCall area of `vyperTypeStmtSoundnessScript.sml`. Do not touch nonstatic ExtCall or files outside `semantics/prop`.

#### Not to try
Do not perform broad repository cleanup or edit unrelated cheats.

### C0.5: Integrate ExtCall nonstatic branch and remove nonstatic cheat
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 50
- Work units: 8
- Rationale: Risk remains 2, but this leaf is not the next component. It depends on the static ExtCall boundary being closed and cleaned, because the nonstatic proof should mirror the finalized static proof shape and must not be attempted while the static branch still has stale inner resumes.
- Dependencies: C0.4.2
- Progress transition: `refinement`
- Carries progress/evidence from: C0.5

#### Progress note
Dependency metadata repaired: C0.5 now waits on concrete leaf `C0.4.2` rather than the non-executable parent `C0.4`. Prior C0.5 proof guidance is otherwise carried forward.

#### Summary
- Do not begin until C0.4.1 and C0.4.2 are done.
- Prove the nonstatic ExtCall branch by mirroring the finalized static projected-helper pattern, with the extra amount argument.
- Use existing nonstatic argument-runtime and projected helper lemmas if present in the script.
- Stop as NEW_DEPENDENCY if the finalized static proof reveals a missing compact helper interface for nonstatic ExtCall.

#### Approach
After static ExtCall is closed, follow the same linear branch discipline for nonstatic ExtCall: argument evaluation, expression-list IH facts, then the relevant projected nonstatic helper. Keep only one success path active and close error cases immediately. If the nonstatic helper interface does not match the finalized static proof boundary, escalate for a helper plan instead of writing theorem plumbing.

#### Not to try
Do not start this before C0.4.2. Do not recover optional-driver or amount premises from a broad generated prefix. Do not use the old static-success blocker as a template.

### C0.6: Close RawCallTarget statement-expression soundness cheat
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: Risk 2: RawCallTarget is a single remaining expression-call branch and should be handled by the same branch-local evaluator discipline; if a missing compact helper appears, this component must stop as NEW_DEPENDENCY rather than producing theorem plumbing.
- Dependencies: C0.2, C0.5
- Checkpoint: yes
- Carries progress/evidence from: C0.2

#### Progress note
New proof-completion leaf for the RawCallTarget cheat; depends on raw-call return-type well-formedness if that fact is needed by the branch typing proof.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` / remove the RawCallTarget cheat.
- Use the same combined postcondition as ExtCall: state/env/accounts preservation, no-TypeError, and result typing together.
- Bring in `raw_call_return_type_well_formed` rather than reproving return-type well-formedness locally.
- Split raw-call evaluator branches linearly and close error cases immediately.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  ...
QED
```

#### Approach
Start by rewriting the relevant `well_typed_expr` call case once to expose typed arguments/flags and `raw_call_return_type` facts. Split argument evaluation and raw-call semantic operations at the point the evaluator branches; use branch facts and `raw_call_return_type_well_formed` for result typing. If the branch needs a reusable theorem, formulate a local RawCall projected helper whose conclusion is exactly the mutual postcondition, analogous to `extcall_*_projected_sound`.

#### Not to try
Do not unfold old retired type-soundness theories or use legacy `vyperTypeSoundnessScript` facts unless they are already imported and clearly fresh-stack compatible. Do not solve RawCall by weakening result typing or changing `raw_call_return_type_def`.

### C0.7: Final fresh-stack proof-integrity build, cheat audit, and task-local status commit
- Kind: `final_audit`
- Risk: 1
- Work priority: 60
- Work units: 2
- Rationale: Risk 1: mechanical build/grep/status verification after all proof leaves are closed.
- Dependencies: C0.6
- Checkpoint: yes

#### Progress note
Final validation leaf for the replacement proof-completion subtree.

#### Summary
- Build the relevant target(s), ending with `vyperSemanticsHolTheory` if feasible under task timing.
- Audit for zero reachable CHEAT warnings and no remaining source `cheat` proofs in fresh-stack imported files.
- Update `TYPE_SYSTEM_REWRITE_PLAN.md` / `STATE_type_system_rewrite.md` with actual completion evidence.
- Commit only task-local changes under `semantics/prop` with `git commit --no-gpg-sign`.

#### Statement
Final audit obligation: `vyperSemanticsHolTheory` builds with no reachable fresh-stack CHEAT warnings and the task-local residual source cheats are gone.

#### Approach
Run focused builds first (`vyperTypeBuiltinsTheory`, `vyperTypeStmtSoundnessTheory`) and then the aggregate target. Use grep/source audit to confirm no `cheat` remains at the planned sites and no CHEAT warning is reachable from `vyperSemanticsHolTheory`. Check `git status` carefully; stage only intended `semantics/prop` tracked files and commit unsigned.

#### Not to try
Do not commit unrelated untracked legacy/temp files. Do not call the session complete if any planned cheat remains, even if the build succeeds.
