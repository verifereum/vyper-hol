# PLAN

## Structured Components

### C0: AUTHORIZED BOUNDED PROBE: ExtCall linear proof-only refactor
- Kind: `proof_architecture_probe`
- Risk: 3
- Work priority: 0
- Work units: 1
- Rationale: Maintainer clarification supplies a narrowed unblocking path. Edits remain limited to `semantics/prop`, evaluator/semantics definitions must not change, but proof-architecture refactoring is allowed. Prior evidence still rules out recovering the optional-driver IH from the unsplit top-level generated ExtCall prefix. The authorized probe is instead a careful linear proof of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`: step through the monadic ExtCall chain one operation at a time, close error branches immediately, keep one main success path active, and specialize the generated optional-driver IH only after reaching a single concrete success-continuation branch with the prefix already split/discharged.
- Required for completion: yes
- Checkpoint: yes
- Supersedes: C0, C0.1, C0.2, C0.3, C0.4, C0.5, C0.6
- Progress transition: `replacement`
- Carries progress/evidence from: E0029, TO_type_system_rewrite-20260531T201607Z_m0886_t001, TO_type_system_rewrite-20260531T201607Z_m0862_t001, TO_type_system_rewrite-20260531T201607Z_m0864_t001, TO_type_system_rewrite-20260531T201607Z_m0883_t001, E0026, E0027, E0028
- Invalidates prior progress/evidence: prior C0 external-precondition stop gate and any instruction that no ExtCall proof work is executable absent a source/suspend-boundary redesign

#### Progress note
This replaces the C0 stop gate with a bounded executable proof probe based on maintainer clarification. It carries forward the accepted blocker evidence from E0029, but narrows the prohibition: top-level generated-prefix recovery remains forbidden, while local driver-IH specialization in a fully split concrete success branch is now authorized.

#### Summary
- Required frontier for the fresh type-system rewrite; the task cannot complete while `Expr_Call_ExtCall` remains cheated.
- Remaining task-owned obligations include `Expr_Call_ExtCall`, `Expr_Call_RawCallTarget`, `raw_call_return_type_well_formed`, status/plan updates, unsigned commit discipline, and final zero-cheat validation.
- Accepted evidence E0029 still rules out broad generated-prefix simplification/adapters from the top-level Resume context.
- Maintainer clarification authorizes a proof-only, branch-by-branch ExtCall attempt inside `semantics/prop`, with semantics/evaluator definitions unchanged.
- The driver IH may be specialized only locally after reaching a concrete ExtCall success-continuation branch where the prefix operations have already been split/discharged.

#### Description
This component has one executable frontier: a proof-only refactor of the existing `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`. The current proof interface still does not expose a compact optional-driver premise at the top level, so the proof must avoid trying to manufacture one there. Instead, it should follow the evaluator structure in small focused steps, split and close each monadic branch immediately, and postpone any use of the generated optional-driver IH until the concrete post-call continuation branch where its generated prefix premises have become ordinary branch facts.

#### Statement
Authorized C0 probe:

```text
Attempt a proof-only linear refactor of `eval_all_type_sound_mutual[Expr_Call_ExtCall]` under `semantics/prop`. Do not change evaluator/semantics definitions. Do not recover the optional-driver IH from the unsplit top-level generated prefix. Instead, step through the ExtCall monadic chain in focused branches, close error cases immediately, and specialize the generated optional-driver IH only in the concrete success-continuation branch after the prefix has been discharged.
```

If this succeeds, continue in order with `Expr_Call_RawCallTarget`, `raw_call_return_type_well_formed`, task plan/status updates plus unsigned commit, and final zero-cheat validation of `vyperSemanticsHolTheory`. If the proof again requires broad generated-prefix simplification or full-prefix adapter plumbing, stop and re-plan with exact evidence.

#### Approach
Start in `semantics/prop/vyperTypeStmtSoundnessScript.sml` at `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`. Close the `type_place_expr` half first. For the expression-soundness half, unfold static typing and `evaluate` only as needed, split `eval_exprs`, immediately apply the argument IH in both success/error branches, and then step through each ExtCall check/lift/build/run/update operation one at a time. Each error branch should be discharged before continuing. On the main success path, use existing ExtCall tail helpers and preservation lemmas. If `returnData = []` and `IS_SOME drv`, specialize the generated optional-driver IH only in that focused branch, after the prefix premises are concrete. Use focused `holbuild build vyperTypeStmtSoundnessTheory` feedback after small edits.

#### Not to try
Do not retry `asm "driver_ih" mp_tac >> simp[]`, broad `gvs`, broad generated-prefix simplification, or `AllCaseEqs()` cleanup from the unsplit top-level Resume context. Do not manually specialize the generated optional-driver IH with long `qspecl_then` lists over unsplit ExtCall temporaries or rebuild the whole prefix with ASSUME/MATCH_MP/ACCEPT_TAC/CONJ plumbing. Do not add helper theorems whose assumptions merely package the full generated prefix. Do not recreate or rely on the removed tautological compact bridge. Do not proceed to RawCallTarget, `raw_call_return_type_well_formed`, wrapper/final validation, or commits until the ExtCall probe either succeeds or is explicitly re-planned.

#### Argument
The intended ExtCall soundness argument has two phases. First, evaluate the argument list and external-call plumbing while preserving state/accounts/runtime consistency and ruling out TypeErrors in non-driver branches. Second, if the external call succeeds with empty return data and a driver expression is present, invoke recursive expression soundness for `THE drv` on the post-`update_accounts`/`update_transient` state. Existing tail infrastructure such as `extcall_success_continuation_sound`, `extcall_success_continuation_sound_cond_driver_ih`, `extcall_after_state_update_tail_sound`, and `runtime_consistent_get_tenv` is useful only once phase two receives a compact driver premise. E0029 shows the current mutual `Resume` boundary does not expose that compact premise; the only driver fact is conditional on the whole phase-one generated prefix. Therefore the blocker is the boundary between the generated induction principle and the intended continuation lemma, not a missing value/state lemma.

#### Proof-interface target
The ideal continuation input remains a compact driver premise of the shape

```sml
returnData = [] /\ IS_SOME drv ==>
  !env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\
    context_well_typed cx /\ accounts_well_typed st0.accounts /\
    functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
    well_typed_expr env0 (THE drv) ==>
      state_well_typed st0' /\ env_consistent env0 cx st0' /\
      accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
      case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T
```

However, the authorized probe need not produce this as a standalone theorem from the top-level context. It may prove the needed driver fact locally in the final success branch by specializing the generated IH after the monadic prefix has been split. Failure sign: the only way forward is still to simplify or package a giant generated implication over unsplit ExtCall temporaries.

#### Code structure
Do not edit outside `semantics/prop`. Do not change evaluator/semantics definitions. The expected source file for the probe is primarily `vyperTypeStmtSoundnessScript.sml`; nearby helper theories under `semantics/prop` may be refactored only if that keeps the proof architecture cleaner and semantics unchanged. Keep `Expr_Call_RawCallTarget` and `raw_call_return_type_well_formed` out of scope until ExtCall either succeeds or is re-planned. Any future commit after authorized progress must use `git commit --no-gpg-sign`.
