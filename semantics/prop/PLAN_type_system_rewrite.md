# PLAN

## Structured Components

### C0: BLOCKED: ExtCall proof-boundary redesign external precondition
- Kind: `external_precondition_gate`
- Risk: 4
- Work priority: 0
- Work units: 0
- Rationale: No new concrete redesign was supplied with this checkpoint. Accepted bottom-up evidence E0029 shows the previous Risk-2 local boundary probe was misclassified: inside `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`, the optional-driver recursive IH is available only as a giant generated implication guarded by the whole ExtCall evaluator prefix (`eval_exprs`, checks/lifts, `build_ext_calldata`, `run_ext_call`, `update_accounts`, `update_transient`). Continuing under the current source/theorem boundary would require exactly the broad simplification, long generated-variable specialization, or ASSUME/MATCH_MP/CONJ plumbing forbidden by the task's straightforward-proof constraint. Thus there is no low-risk executable frontier until an external source/suspend-boundary/theorem-architecture redesign is supplied.
- Required for completion: yes
- Checkpoint: yes
- Supersedes: C0, C0.1, C0.2, C0.3, C0.4, C0.5, C0.6
- Progress transition: `replacement`
- Carries progress/evidence from: E0029, TO_type_system_rewrite-20260531T201607Z_m0886_t001, TO_type_system_rewrite-20260531T201607Z_m0862_t001, TO_type_system_rewrite-20260531T201607Z_m0864_t001, TO_type_system_rewrite-20260531T201607Z_m0883_t001, E0026, E0027, E0028
- Invalidates prior progress/evidence: prior C0.1 Risk-2 proof_interface_probe classification, prior downstream C0.2-C0.6 executable schedule while ExtCall remains blocked

#### Progress note
This is a deliberate reaffirmation/replacement of the C0 stop gate, not a new proof roadmap. It carries forward the accepted blocker evidence and the evidence that the source was restored to the stable cheated baseline and the plan/status blocker was recorded. The current escalation adds no new redesign, so prior executable downstream planning remains invalid while ExtCall is unresolved.

#### Summary
- Required stop gate for the fresh type-system rewrite; the task cannot complete while `Expr_Call_ExtCall` remains cheated.
- Remaining task-owned obligations include `Expr_Call_ExtCall`, `Expr_Call_RawCallTarget`, `raw_call_return_type_well_formed`, status/plan updates, unsigned commit discipline, and final zero-cheat validation, but all proof work is blocked by this ExtCall proof-interface problem.
- Accepted evidence E0029 shows the only authorized local boundary probe failed and source was reverted to the stable cheated baseline.
- No HOL proof edits, holbuild-as-proof-work, EVAL probes, RawCallTarget work, builtin cleanup, wrapper/final validation, or commits are authorized under this gate.
- To resume, a maintainer/user must provide a concrete redesign that exposes the optional-driver recursive soundness premise in compact form before the generated ExtCall prefix is accumulated, or explicitly approve a different theorem/source architecture.

#### Description
This component deliberately has no executable child frontier. The current proof interface for `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]` is structurally wrong for the task contract: the recursive call for the optional driver expression is available only as a generated full-prefix implication, not as the compact continuation premise consumed by the existing ExtCall tail lemmas. The prior C0.1 probe attempted the authorized local proof-boundary test and failed with the prohibited shape plus simplification timeouts. Since the current checkpoint provides no new redesign, the correct task-scoped action is to stop/report blocked with external-precondition evidence, not to continue proving siblings or invent another adapter around the same full prefix.

#### Statement
Blocking condition for task completion:

```text
A concrete ExtCall proof-interface/suspend-boundary redesign must be supplied before proof work resumes. The redesign must make the optional-driver expression soundness IH available in compact form at the ExtCall success-continuation use site, without recovering it by simplifying or packaging the full generated ExtCall monadic prefix.
```

After such a redesign is supplied, replace C0 with low-risk executable components covering, in order: the redesigned ExtCall boundary probe, the `Expr_Call_ExtCall` Resume, `Expr_Call_RawCallTarget`, `raw_call_return_type_well_formed`, task plan/status updates plus unsigned commit, and final zero-cheat validation of `vyperSemanticsHolTheory`.

#### Approach
Executor action is procedural: if C0 is still the active PLAN and no concrete external redesign has been supplied, end/report `blocked` with kind `external_precondition` and cite query_plan/dossier evidence. If a redesign is supplied by the user/maintainer, do not edit immediately; call the plan oracle in replace mode for C0 so the redesign can be converted into explicit Risk-1/2 probes and proof obligations. Preserve the stable cheated baseline and do not run holbuild as proof work while blocked.

#### Not to try
Do not retry `asm "driver_ih" mp_tac >> simp[]`, broad `gvs`, broad generated-prefix simplification, or `AllCaseEqs()` cleanup. Do not manually specialize the generated optional-driver IH with long `qspecl_then` lists over ExtCall temporaries or rebuild assumptions with ASSUME/MATCH_MP/ACCEPT_TAC/CONJ plumbing. Do not add helper theorems whose assumptions merely package the full generated prefix. Do not recreate or rely on the removed tautological compact bridge. Do not proceed to RawCallTarget, `raw_call_return_type_well_formed`, wrapper/final validation, source edits, commits, or EVAL/build probes while this gate is active.

#### Argument
The intended ExtCall soundness argument has two phases. First, evaluate the argument list and external-call plumbing while preserving state/accounts/runtime consistency and ruling out TypeErrors in non-driver branches. Second, if the external call succeeds with empty return data and a driver expression is present, invoke recursive expression soundness for `THE drv` on the post-`update_accounts`/`update_transient` state. Existing tail infrastructure such as `extcall_success_continuation_sound`, `extcall_success_continuation_sound_cond_driver_ih`, `extcall_after_state_update_tail_sound`, and `runtime_consistent_get_tenv` is useful only once phase two receives a compact driver premise. E0029 shows the current mutual `Resume` boundary does not expose that compact premise; the only driver fact is conditional on the whole phase-one generated prefix. Therefore the blocker is the boundary between the generated induction principle and the intended continuation lemma, not a missing value/state lemma.

#### Definition design
Required future redesign interface: create or change a source/suspend boundary so the ExtCall success-continuation proof receives a premise of the compact shape

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

A redesign is acceptable only if a bounded probe inside/near `Expr_Call_ExtCall` can apply the tail lemma without exposing or reconstructing the full `eval_exprs`/`check`/`lift_option`/`build_ext_calldata`/`run_ext_call`/update prefix. Failure sign: the proof context still contains a giant generated implication over ExtCall temporaries as the only driver fact.

#### Code structure
Do not edit outside `semantics/prop`. Until an external redesign exists, keep `vyperTypeStmtSoundnessScript.sml` at the honest cheated baseline for `Expr_Call_ExtCall` and `Expr_Call_RawCallTarget`; keep `TYPE_SYSTEM_REWRITE_PLAN.md` and `STATE_type_system_rewrite.md` recording the blocker. A future approved redesign should be localized to the fresh stack, primarily `vyperTypeStmtSoundnessScript.sml` and possibly nearby helper theories under `semantics/prop` if a genuine source-level boundary lemma is introduced. Any future commit after authorized progress must use `git commit --no-gpg-sign`.
