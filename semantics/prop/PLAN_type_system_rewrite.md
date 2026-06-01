# PLAN

## Structured Components

### C0: Complete the task-scoped type-system rewrite obligations in semantics/prop
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The only current blocker is a scheduler/dependency representation issue, not mathematical uncertainty. The ExtCall helper-interface mismatch from E0084 has a standard low-risk repair via generalized outside-Resume helpers, and all remaining proof work stays inside semantics/prop under the maintainer clarification.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0, E0076, E0077, E0080, E0082, E0083, E0084

#### Progress note
This replacement preserves the current task-scoped C0 strategy and proved helper evidence, but repairs the scheduler by making downstream leaves depend on leaf prerequisites rather than on the C0.3 parent alone.

#### Summary
- Continue the task-scoped type-system rewrite proof inside `semantics/prop` only.
- Preserve the maintainer constraints: no evaluator/semantics definition changes, no files outside `semantics/prop`, unsigned commits only.
- Preserve E0084 as accepted evidence that narrow ExtCall argument-error projection helpers do not match the live `Call v15 ...` Resume goal.
- Execute the accepted repair first: add generalized argument-error helpers over arbitrary outer `Call` annotation.
- Retry the ExtCall Resume shell only after those generalized helpers build.
- Then proceed linearly through the ExtCall success prefix and final optional-driver continuation.

#### Argument
The ExtCall expression proof splits naturally at the first evaluation of the argument expressions. If `eval_exprs cx es st` returns an error (`INR y,args_st`), the evaluator returns immediately with that same result and state; no later ExtCall prefix operation, external call, or optional driver reasoning is relevant. This early-return fact is independent of the outer type annotation on `Call`, so boundary lemmas must quantify an arbitrary `call_ty` while the inner `ExtCall` still carries its `ret_type`. Once the error branch and no-place conjunct are closed by these boundary lemmas, the remaining success branch can be handled linearly through concrete monadic operations: split static/nonstatic arguments, close each failed extraction/check immediately as a non-TypeError result, preserve account/state typing through `run_ext_call`, and specialize the optional-driver IH only in the final unique success-continuation branch.

#### Definition design
No evaluator or semantics definitions may be changed. The proof interface is a family of local boundary lemmas in `vyperTypeStmtSoundnessScript.sml` that hide evaluator unfolding from the generated Resume proof. The critical probe/interface is `eval_extcall_args_error_any_call_ty`: from `eval_exprs cx es st = (INR y,args_st)`, compute one evaluator step for `Call call_ty (ExtCall ... ret_type) es drv` and return `(INR y,args_st)`. Its projections must have conclusions matching split Resume goals directly: state well-typed, environment consistency, account typing, no type error, and expression-result typing/no-obligation for `INR`. Failure signs are: needing to prove `call_ty = ret_type`, using broad `AllCaseEqs()` over the full ExtCall prefix, specializing the optional-driver IH before the final success branch, or writing adapter theorems for generated-prefix assumptions.

#### Code structure
All edits are confined to `semantics/prop`. Put new local ExtCall helper theorems near the existing `eval_extcall_args_error*` helper block in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Keep task progress/state updates in `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and/or `semantics/prop/STATE_type_system_rewrite.md`. Do not edit evaluator/semantics definition files outside this directory. Verify with `holbuild` for `vyperTypeStmtSoundnessTheory` after helper additions and after Resume changes. Commit only task-scoped files and use `git commit --no-gpg-sign`.

### C0.1: Keep task-local plan/state aligned with the narrowed ExtCall clarification
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This documentation component has already been completed and remains valid. It is carried forward only as task-scoped progress evidence and not as new executor work.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1, E0076

#### Summary
- Carry forward the completed documentation update under `semantics/prop`.
- The old broad ExtCall stop gate is superseded by the maintainer clarification.
- The failed generated-prefix adapter approach remains negative evidence.
- No new documentation edit is required for this component unless later proof progress changes the state file.

#### Statement
Completed documentation deliverable: task-local plan/state files no longer treat the old ExtCall stop gate as forbidding all proof action, and instead direct the proof through the small argument-error boundary and linear ExtCall proof plan.

#### Approach
No further work. If touching state files later, preserve this carried-forward conclusion and update only current cursor/progress notes.

#### Not to try
Do not rewrite the whole roadmap or plan unrelated repository cheats. Do not stage untracked scratch/legacy files.

### C0.2: Keep the live argument-error boundary probe for ExtCall
- Kind: `proof_boundary_probe`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: The initial narrow argument-error computation probe has already been proved and remains useful infrastructure; C0.3.4 generalizes its outer annotation.
- Dependencies: C0.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2, E0077

#### Summary
- Carry forward the proved local theorem `eval_extcall_args_error` or equivalent.
- It proves immediate return when `eval_exprs` returns `INR`.
- It does not mention generated optional-driver IHs.
- It supports the generalized helper family but is not sufficient for the live Resume goal by itself.

#### Statement
Existing theorem shape:
```sml
Theorem eval_extcall_args_error[local]:
  eval_exprs cx es st = (INR y,args_st) ==>
  eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
    (INR y,args_st)
```

#### Approach
No further work unless the source no longer contains the theorem. Downstream generalized helpers may copy this proof shape with an independent `call_ty`.

#### Not to try
Do not reopen this as a raw Resume proof. Do not replace it with a generated-prefix adapter theorem.

### C0.3: Close the ExtCall argument-error and place-expression shell using annotation-polymorphic boundaries
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: E0084 identified a helper-interface mismatch, not an unprovable branch. The repair is to add annotation-polymorphic boundary/projection lemmas before retrying the Resume consumer. The scheduler repair is encoded by leaf dependencies and priorities in C0.3.4 -> C0.3.3 -> C0.4.
- Dependencies: C0.2
- Progress transition: `refinement`
- Carries progress/evidence from: C0.3, C0.3.1, C0.3.2, E0082, E0083, E0084

#### Summary
- Preserve C0.3.1 and C0.3.2 as valid but too narrow for direct live Resume use.
- Prove generalized helpers over arbitrary outer `call_ty` in C0.3.4 first.
- Then rewrite the suspended ExtCall result/place Resume shell in C0.3.3.
- Use `conj_tac`, close the place half with `type_place_expr_Call_ExtCall_NONE`, and use generalized projections for argument-error result goals.
- Do not let C0.4 begin until C0.3.3 is complete.

#### Argument
The generated ExtCall branch contains separate obligations for expression result typing and place expression typing. The expression result proof first consumes the expression-list IH for the argument expressions. In the `INR` argument-error branch, the ExtCall expression has already returned, so all state/result preservation facts follow from the generalized early-return helper family. The outer annotation of `Call` is irrelevant to evaluator computation in this branch, which is why the helper must quantify `call_ty`; the live Resume goal's `v15` should instantiate it directly. The place-expression half is semantic dead code for calls and should be closed by the existing `type_place_expr_Call_ExtCall_NONE`, not by evaluator unfolding.

#### Definition design
C0.3 owns the boundary between outside-Resume evaluator facts and the generated mutual-induction Resume. The interface must expose small projection lemmas whose conclusions match the split goals after `conj_tac` and expression-list IH application. The Resume consumer should not unfold the full ExtCall monadic prefix and should not need theorem plumbing or manual adapter implications. If `irule` on a generalized projection does not match `Call v15 (ExtCall ... ret_type)`, the helper statement is still wrong and must be fixed before proceeding.

#### Code structure
Add generalized helper theorems in `semantics/prop/vyperTypeStmtSoundnessScript.sml` adjacent to existing `eval_extcall_args_error*` lemmas. Keep the existing narrow helpers unless they actively confuse the proof; they remain valid infrastructure. The suspended `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` is modified only after C0.3.4 builds cleanly. Verify after C0.3.4 before touching C0.3.3.

### C0.3.1: Carry forward `eval_extcall_args_error_sound` as the full postcondition boundary
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This helper was already proved and committed; it is valid evidence but not the direct live-goal helper because its outer annotation is narrow.
- Dependencies: C0.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.3.1, E0080, E0082

#### Summary
- Carry forward the local theorem `eval_extcall_args_error_sound`.
- It is useful as proof infrastructure and/or a source for projections.
- It should not be reproved unless missing from the source.
- It should not be applied directly to the live `Call v15 ...` Resume goal.

#### Statement
Existing local theorem:
```sml
Theorem eval_extcall_args_error_sound[local]:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ no_type_error_result (INR y) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
```

#### Approach
No work. Downstream generalized helpers may either copy this proof pattern or bypass it via the generalized computation lemma.

#### Not to try
Do not force this theorem onto the live goal by proving `v15 = ret_type` or by broad simplification.

### C0.3.2: Carry forward the narrow conjunct-specific ExtCall argument-error projection helpers
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 5
- Work units: 0
- Rationale: These projections have been proved and remain valid, but E0084 shows their `Call ret_type ...` conclusion is too narrow for the current Resume consumer. They are retained as infrastructure, not scheduled as direct prerequisites for C0.3.3 except through the generalized C0.3.4 repair.
- Dependencies: C0.3.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.3.2, E0083

#### Summary
- Carry forward the proved narrow projection helper family.
- They may guide or source the generalized versions.
- They do not solve the live `Call v15 ...` matching problem.
- No new executor work is required here.

#### Approach
No work. Use these helpers only if their conclusion exactly matches a goal, or as templates for C0.3.4. The live C0.3.3 consumer must use `*_any_call_ty*` variants.

#### Not to try
Do not retry these helpers directly in the live Resume context; prior evidence produced a no-match failure.

### C0.3.3: Rewrite the ExtCall Resume shell to consume generalized projection helpers and close the no-place half
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: Once C0.3.4 is available, the previously failing `irule` should match the live `Call v15 ...` goal directly. The remaining work is a standard linear Resume shell: split result/place conjuncts, use the expression-list IH for argument evaluation, and close argument-error projections with the generalized helpers.
- Dependencies: C0.3.4
- Progress transition: `refinement`
- Carries progress/evidence from: E0084

#### Summary
- Retry `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` only after C0.3.4 builds.
- Start with `conj_tac`; the first goal is expression-result postcondition, the second is place-expression.
- In the result half, unfold only to the first `eval_exprs` split and consume the expression-list IH with `drule_all`.
- In the `eval_exprs = INR ...` branch, apply generalized C0.3.4 projections by direct `irule`.
- Close the place half with `type_place_expr_Call_ExtCall_NONE`.
- Leave later argument-success/success-continuation work to C0.4/C0.5 as needed.

#### Description
This component is the consumer repair for E0084. The source experiment from the failed narrow-helper attempt was reverted, so restart from the intentional-cheat baseline. The goal is not to finish the entire ExtCall success path here unless it falls out mechanically; it is to remove the argument-error/place shell blockage and hand the unique `INL vs` argument-success path to C0.4.

#### Statement
Fill the suspended proof segment:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]:
  ...
```
for the ExtCall expression-result/place conjuncts in `vyperTypeStmtSoundnessScript.sml`, using the C0.3.4 generalized helpers in the `eval_exprs cx es st = (INR y,args_st)` branch.

#### Approach
Use the known prefix: `rpt gen_tac >> strip_tac >> conj_tac`, rewrite the `well_typed_expr` assumption once, move the eval assumption, unfold `evaluate_def`/monadic primitives only to the first `eval_exprs` split, then apply the expression-list IH. In the `INR` branch, each generalized projection should close by `irule` plus existing assumptions. For the second conjunct, expose the `type_place_expr` assumption and close using `type_place_expr_Call_ExtCall_NONE`.

#### Not to try
Do not use the old C0.3.2 narrow helpers in the live goal. Do not use `reverse conj_tac` at the start. Do not use broad `simp`/`gvs`/`AllCaseEqs()` over the generated ExtCall prefix. Do not specialize the optional-driver IH before the single concrete success-continuation branch.

### C0.3.4: Add generalized ExtCall argument-error helpers over arbitrary outer Call annotation
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: The generalized computation lemma is the same one-step evaluator fact as the existing argument-error probe, except it quantifies `call_ty` independently from inner `ret_type`. Projection lemmas are direct rewrites/projections and are exactly the accepted repair for E0084.
- Dependencies: C0.3.1, C0.3.2
- Checkpoint: yes
- Supersedes: E0084 narrow-helper failure
- Progress transition: `refinement`
- Carries progress/evidence from: E0084, C0.3.2

#### Progress note
This is the canonical next executable proof step. It repairs the C0.3.2 helper-interface mismatch without invalidating the proved narrow helpers.

#### Summary
- Add outside-Resume generalized helpers for the ExtCall argument-error branch.
- Quantify `call_ty` independently from `ret_type`.
- Provide projection lemmas for state typing, env consistency, account typing, no type error, and expression-result typing/no-obligation.
- Verify these helpers build before editing the suspended Resume.
- This component must precede C0.3.3 and C0.4.

#### Description
E0084 showed the live goal contains `eval_expr cx (Call v15 (ExtCall is_static' (func_name,arg_types,ret_type)) es drv) st = (res,st')`, while the narrow projection helpers require outer annotation `ret_type`. The generalized family must let `v15` instantiate `call_ty` directly.

#### Statement
Expected theorem family, names may follow local file conventions:
```sml
Theorem eval_extcall_args_error_any_call_ty[local]:
  !cx es st y args_st call_ty ret_type stat func_name arg_types drv.
    eval_exprs cx es st = (INR y,args_st) ==>
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (INR y,args_st)

Theorem eval_extcall_args_error_any_call_ty_state_well_typed[local]:
  !cx env st args_st y res st' call_ty is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call call_ty (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    state_well_typed args_st ==>
    state_well_typed st'
```
Also add analogous generalized projections for `env_consistent env cx st'`, `accounts_well_typed st'.accounts`, `no_type_error_result res`, and:
```sml
case res of
| INL tv => expr_result_typed env (Call call_ty (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
| INR _ => T
```

#### Approach
Prove the computation lemma by copying the proof shape of `eval_extcall_args_error` and changing only the quantified outer annotation. A single `Once evaluate_def` unfold plus monad simplification should expose the early `eval_exprs` return. Prove projections by rewriting with the generalized computation lemma; for no-type-error, use the existing `Cases_on y`/`no_type_error_result_def` pattern. Run `holbuild` after adding only these lemmas.

#### Not to try
Do not prove or assume `call_ty = ret_type`. Do not recover this in the raw Resume context with broad `simp`/`gvs`/`AllCaseEqs()`. Do not create generated-prefix adapter theorems or edit evaluator definitions.

### C0.4: Step through static and nonstatic ExtCall prefix branches up to external-call success
- Kind: `proof_branch`
- Risk: 2
- Work priority: 60
- Work units: 5
- Rationale: This branch is authorized only after C0.3.3 has removed the argument-error/place shell blocker. The work is linear monadic case splitting using existing local destructors and preservation lemmas, with error exits closed immediately.
- Dependencies: C0.3.3
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4

#### Summary
- Begin only after C0.3.3 is complete.
- Work in the single `INL vs` argument-success path.
- Split `is_static` once.
- Static branch: use `extcall_static_args_runtime_typed_dest` for target address and nonempty arguments.
- Nonstatic branch: use `extcall_nonstatic_args_runtime_typed_dest` for target, amount, and required list nonemptiness facts.
- Step one monadic operation at a time through extraction, calldata, accounts, transient storage, `run_ext_call`, tuple split, and revert check.
- Close each failed operation branch immediately.

#### Statement
Internal proof segment of `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`: after argument success, discharge ExtCall prefix error branches before the final return-data continuation, leaving only external-call success/revert-success/update/return-continuation obligations for C0.5 if still suspended.

#### Approach
Use local simplification only for the next operation: `bind_def`, `ignore_bind_def`, `check_def`/`assert_def`, `return_def`, `raise_def`, `lift_option_def`, `get_accounts_def`, `get_transient_storage_def`. Prefer `Cases_on` one operation at a time, then close the error branch with `no_type_error_result_def` or the relevant runtime-error simplification. Derive `accounts_well_typed accounts'` with `run_ext_call_accounts_well_typed` as soon as `run_ext_call` succeeds.

#### Not to try
Do not unfold the whole ExtCall prefix and run `AllCaseEqs()`. Do not keep static/nonstatic or multiple failure branches open in parallel. Do not specialize the optional-driver IH here; it belongs in the final continuation component.

### C0.5: Close the ExtCall success continuation and specialize optional-driver IH only at the final branch
- Kind: `proof_branch`
- Risk: 2
- Work priority: 70
- Work units: 5
- Rationale: Existing local helper infrastructure is intended for this tail; the remaining delicate rule is timing. The generated optional-driver IH is specialized only after all concrete prefix operations have been split and the single success-continuation branch is reached.
- Dependencies: C0.4
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.5

#### Summary
- Work only in the unique success path after C0.4.
- Split the `run_ext_call` result tuple and the revert/success check.
- Preserve state/account/transient typing through the account and transient-storage updates using existing local lemmas.
- Apply `extcall_success_continuation_sound_cond_driver_ih` or the file's corresponding helper at the return-data continuation.
- Specialize the generated optional-driver IH only in this final concrete branch.
- Verify the whole theorem after this checkpoint.

#### Statement
Complete the remaining success-continuation part of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`, including return-data continuation typing and final result/state preservation.

#### Approach
After C0.4 has produced concrete successful prefix facts, instantiate the continuation helper with the actual updated state, accounts, transient storage, return data, and driver condition. Use preservation lemmas before calling the helper so its hypotheses are directly present. Keep the optional-driver IH specialization local to this final branch rather than trying to derive it from the top-level Resume context.

#### Not to try
Do not recover the driver premise by broad simplification from the top-level context. Do not introduce a long generated-prefix adapter theorem. Do not move optional-driver IH specialization earlier to simplify prefix branches.

### C0.6: Verify, update task-local progress notes, and commit the ExtCall proof unsigned
- Kind: `integration_validation`
- Risk: 1
- Work priority: 80
- Work units: 2
- Rationale: This is mechanical validation and task-local handoff after proof components build. The task explicitly requires progress commits and forbids GPG signing.
- Dependencies: C0.5
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.6

#### Summary
- Run the appropriate `holbuild` target for `vyperTypeStmtSoundnessTheory`.
- Update `semantics/prop/STATE_type_system_rewrite.md` and, if useful, `TYPE_SYSTEM_REWRITE_PLAN.md` with the completed ExtCall status.
- Inspect `git status` and stage only files under `semantics/prop`.
- Commit with `git commit --no-gpg-sign`.
- Leave unrelated untracked scratch/legacy files alone unless they are task-owned and intentionally updated.

#### Statement
Integration deliverable: proof builds for the task-scoped target, task-local state is current, and changes under `semantics/prop` are committed unsigned.

#### Approach
Use the same target previously used in state notes: `holbuild` for `vyperTypeStmtSoundnessTheory` with a reasonable timeout. If build fails in an unrelated file outside the task scope, stop and report rather than expanding the plan. Commit only after a clean task-scoped build and status audit.

#### Not to try
Do not edit outside `semantics/prop`. Do not use a signed commit. Do not clean up repository-wide cheats or unrelated untracked files.
