# PLAN

## Structured Components

### C0: Task-local proof completion for remaining fresh-stack cheats
- Kind: `proof_completion_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Risk 2 because all executable leaves are either audits, localized arithmetic, or integrations through existing local helper lemmas (`extcall_static_projected_sound`, `extcall_nonstatic_projected_state_well_typed`, `eval_extcall_args_error_*`, `extcall_after_state_update_tail_sound*`). The prior Risk/blocked evidence is addressed by not retrying the current static-success Resume boundary as the primary proof interface; the new proof path first proves/uses compact branch facts and only specializes the optional-driver IH after the success continuation branch is concrete.
- Required for completion: yes
- Supersedes: C0, E0223, E0224, E0225, E0226
- Progress transition: `replacement`
- Carries progress/evidence from: E0223, E0224, E0225, E0226, TO_type_system_rewrite-20260601T220715Z_m4328_t001, TO_type_system_rewrite-20260601T220715Z_m4389_t002, TO_type_system_rewrite-20260601T220715Z_m4347_t003

#### Progress note
Replaces the terminal blocked-report meaning of C0 with an authorized proof-completion subtree because the operator checkpoint requires continued work and the PLAN incorrectly exposed no frontier despite residual reachable cheats. Prior evidence still counts as negative proof-interface evidence: do not retry the failed current-boundary `run_ext_call` fanout or generated-prefix reconstruction. Prior build/cheat audit evidence provides baseline state only, not proof completion.

#### Summary
- Complete exactly the remaining fresh-stack task obligations reachable from `vyperSemanticsHolTheory` inside `semantics/prop`.
- Cover the localized `raw_call_return_type_well_formed` cheat and the statement-soundness cheats at ExtCall/static success, ExtCall/nonstatic result, and RawCallTarget.
- Keep evaluator/semantics definitions unchanged and edit only files under `semantics/prop`.
- The ExtCall route must not solve generated-prefix goals; it must use compact projected helper lemmas and integrate them only after concrete success/error branches are exposed.
- Final completion requires focused builds plus a reachable-cheat audit showing no CHEAT warnings/`cheat` proofs reachable from `vyperSemanticsHolTheory`.

#### Description
This subtree is proof completion, not another blocked-report closure. Its central design is to avoid the failed `Expr_Call_ExtCall_result_static_success` boundary as a source of optional-driver premises. Existing local helper lemmas around lines ~9600--10450 already express the correct compact interface: argument evaluation gives a typed `vs,args_st`; static/nonstatic ExtCall execution is handled by projected lemmas; successful external-call continuation delegates to `extcall_after_state_update_tail_sound` or its conditional-driver-IH variant. The executor should make small, auditable changes in `vyperTypeStmtSoundnessScript.sml` and `vyperTypeBuiltinsScript.sml`, building after each proof cluster. Commit progress unsigned (`git commit --no-gpg-sign`) only after clean task-local proof milestones.

#### Statement
Task-scoped completion obligation: remove all remaining reachable fresh-stack cheats in `semantics/prop` needed for `vyperSemanticsHolTheory` proof integrity, without editing outside `semantics/prop` or changing evaluator/semantics definitions.

#### Approach
Work in audit-first order, then close the small builtins arithmetic cheat, then close ExtCall and RawCallTarget statement-expression proof branches using local projected/boundary lemmas. For ExtCall, the key invariant is the mutual theorem's combined postcondition: state/env/accounts preservation, no-TypeError, and result typing are proved together by each projected branch helper and then supplied to the suspended branch. Specialize the optional-driver IH only inside a concrete branch where `returnData = [] ∧ IS_SOME drv` is the active continuation premise; otherwise use decode-return typing and account-preservation helpers.

#### Not to try
Do not retry E0223's path: post-`Cases_on run_ext_call ...` generated-prefix fanout from `Expr_Call_ExtCall_result_static_success`, broad `simp`/`gvs`/`AllCaseEqs()` over the whole ExtCall prefix, or long generated-prefix adapter theorems. Do not recover driver premises from the top-level generated Resume context. Do not claim completion from a build while source-level `cheat` proofs or CHEAT warnings remain reachable. Do not edit evaluator definitions or any file outside `semantics/prop`.

#### Argument
The proof stack succeeds by maintaining the strongest joint evaluator invariant already encoded in `eval_all_type_sound_mutual`: after evaluation, the resulting state, environment consistency, accounts typing, no-TypeError property, and expression-result typing all hold together. For calls, split first on argument-list evaluation. The `INR` argument-error branch is semantically identical to the argument error; use `eval_extcall_args_error*` helpers rather than unfolding the whole call prefix. The `INL vs` branches should use well-typedness to derive the exact runtime argument shape (`extcall_static_args_runtime_typed_*` or `extcall_nonstatic_args_runtime_typed_*`). Static and nonstatic external-call chains then reduce to the same compact continuation invariant: if the external call succeeds, account typing is preserved by `run_ext_call_accounts_well_typed`, the state update preserves runtime consistency, and the return tail is handled by ABI decoding or the optional driver IH. RawCallTarget should follow the same branch-local pattern: argument/target/return-type facts first, external/raw-call operation next, and continuation/result typing last. The localized builtins arithmetic lemma is independent and should be discharged before statement integration so final audits have one fewer source of CHEAT noise.

#### Definition design
No new evaluator or semantics definitions are authorized. If a proof interface is missing, add only local theorem boundaries in `vyperTypeStmtSoundnessScript.sml` or `vyperTypeBuiltinsScript.sml`. Good ExtCall boundary lemmas have conclusions exactly of the mutual postcondition shape, with hypotheses such as `eval_exprs ... = (INL vs,args_st)`, `exprs_runtime_typed env es vs`, `MAP expr_type es = ...`, and a conditional driver IH guarded by `returnData = [] ∧ IS_SOME drv`. Bad boundaries expose the generated monadic prefix or require manually reconstructing 20+ generated variables. Failure sign: after a branch split, HOL shows multiple generated-prefix goals or a multi-KiB optional-driver implication before a concrete `run_ext_call = SOME (...)` continuation is available; stop and replan instead of proving those goals one-by-one.

#### Code structure
All work stays in `semantics/prop`. Put the arithmetic proof for `raw_call_return_type_well_formed` in `vyperTypeBuiltinsScript.sml` at the existing theorem. Keep ExtCall and RawCallTarget helper lemmas local in `vyperTypeStmtSoundnessScript.sml` near the existing ExtCall helper block (~9600--10450) or immediately before the relevant `Resume` blocks if they are purely integration helpers. Do not introduce new theories or touch old retired proof stack files unless they are already imported by the fresh stack and strictly necessary. Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` / `STATE_type_system_rewrite.md` only to record actual progress and stop conditions, and commit with `--no-gpg-sign` after clean milestones.

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

### C0.4: Integrate ExtCall static branch and remove static-success cheat
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: Risk 2 after C0.3: the static branch has existing local lemmas for target address/nonempty arguments, calldata/empty-code/run-none errors, external-call success account typing, and continuation soundness.
- Dependencies: C0.3
- Checkpoint: yes
- Supersedes: E0223
- Progress transition: `replacement`
- Carries progress/evidence from: C0.3

#### Progress note
Replaces the old blocked static-success leaf with a compact-helper integration path validated by C0.3.

#### Summary
- Replace the `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`.
- Keep the current linear prefix splits for calldata error, empty code, and `run_ext_call = NONE`; close error branches immediately.
- For `run_ext_call = SOME (success, returnData, accounts', tStorage')`, split `success`; reverted/error case is RuntimeError/no-TypeError, success case delegates to `extcall_after_state_update_tail_sound` or `extcall_static_projected_sound`.
- Specialize optional-driver IH only inside the concrete success continuation and only if `returnData = [] ∧ IS_SOME drv`.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]:
  ...
QED
```

#### Approach
Use the current proof through `Cases_on run_ext_call ...`; immediately close `NONE` using the existing `Expr_Call_ExtCall_static_run_none` proof if it remains valid. In the `SOME` case, destruct the tuple and success boolean with `PairCases_on`/`Cases_on`, derive `accounts_well_typed accounts'` via `run_ext_call_accounts_well_typed`, establish `runtime_consistent env cx args_st`, then invoke the tail/continuation helper. Use `extcall_static_projected_sound` if the direct Resume context is still too noisy; its conclusion exactly matches the mutual postcondition.

#### Not to try
Do not leave multiple monadic prefix branches open while applying driver IH. Do not use broad `gvs` to mine the generated optional-driver prefix from the top-level Resume context. If `Cases_on run_ext_call` creates the E0223 9-goal fanout before a compact helper applies, stop and escalate rather than continuing.

### C0.5: Integrate ExtCall nonstatic branch and remove nonstatic cheat
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: Risk 2 because it mirrors the static proof with one additional amount argument; existing helpers `extcall_nonstatic_args_runtime_typed_dest`, `extcall_nonstatic_args_runtime_typed_nonempty`, and nonstatic projected lemmas cover the extra shape facts.
- Dependencies: C0.4
- Checkpoint: yes
- Carries progress/evidence from: C0.4

#### Progress note
New integration leaf for the remaining ExtCall nonstatic suspended result, expected to reuse the static continuation proof pattern.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` / remove the nonstatic ExtCall cheat.
- Derive both target address and amount from runtime-typed arguments.
- Use `build_ext_calldata ... (TL (TL vs))` and `run_ext_call ... (SOME amount)` branch structure.
- Reuse the same continuation helper shape as static after state/account/transient update.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  ...
QED
```

#### Approach
Follow the static proof but use `MAP expr_type es = BaseT AddressT :: BaseT (UintT 256) :: arg_types`, `extcall_nonstatic_args_runtime_typed_dest`, and `extcall_nonstatic_args_runtime_typed_nonempty`. In success branches, destruct `run_ext_call` to obtain `(success, returnData, accounts', tStorage')`, prove account typing, and call the same tail soundness lemma with `is_static = F`. Keep the optional-driver IH conditional and local to the return tail.

#### Not to try
Do not duplicate the entire static proof with generated variable plumbing. Do not unfold more evaluator layers than needed once the projected/tail helper applies.

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
