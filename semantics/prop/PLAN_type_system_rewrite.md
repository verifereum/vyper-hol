# PLAN

## Structured Components

### C0: Build and CHEAT-audit the current fresh-stack baseline
- Kind: `source_audit`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: Mechanical holbuild/audit step; it records current source reality before proof edits and prevents work against stale handover notes.
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
Preserves the previous baseline/audit component. It is not a proof obligation itself, but downstream components must use its current list of reachable CHEAT warnings as coverage evidence.

#### Summary
Run `holbuild build vyperTypeStatePreservationTheory` and `holbuild build vyperSemanticsHolTheory` or the closest permitted audit commands. Record every reachable `cheat`/unfinished `suspend` in the fresh stack. Use this only to refine exact work sites; do not expand scope to retired theories unless they are imported by `vyperSemanticsHolTheory`.

#### Description
The task’s source of truth is current SML source, with frozen public behavior only at the final wrapper surface. This component establishes the concrete remaining warnings and confirms whether the For_cons source already contains the helper-based patch or still has the old existential tail.

#### Statement
No theorem statement. Output is an audit list of reachable CHEAT/suspend warnings and first failing holbuild target, if any.

#### Approach
Use `holbuild`, not direct HOL. Prefer `vyperTypeStatePreservationTheory` first because the handover-focused assignment proof lives there, then `vyperSemanticsHolTheory` for full reachability. If current source differs from handover notes, treat source/audit as authoritative and close already-fixed leaves with evidence instead of re-editing.

#### Not to try
Do not start broad repository cleanup from grep output alone. Suspends in old retired theories or non-imported experiments are notes only unless the audit shows they are reachable from `vyperSemanticsHolTheory`.

### C1: Assignment-target state preservation and joint soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The strengthened assignment interfaces already exist in source and the remaining work is split by evaluator branch. The hardest top-level storage cases are isolated to exact branch helpers rather than a new induction architecture.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1, TYPE_SYSTEM_REWRITE_PLAN assignment update 2026-05-13

#### Progress note
Carries forward the strengthened `assign_target_sound_mutual` architecture; no prior proof progress is invalidated. The old high-risk gate is replaced by branch-local low-risk leaves.

#### Summary
Finish the reachable assignment-target proofs in `vyperTypeStatePreservationScript.sml`. Do not weaken `assign_target_sound_mutual` or drop `assign_operation_matches_target_shape` / `assign_target_assignable_context`. Prove branch helpers that exactly match evaluator branches, then discharge compatibility wrappers in `vyperTypeAssignSoundnessScript.sml`.

#### Approach
Work branch-by-branch, closing each branch immediately after splitting on the evaluator result. Follow the proven `TopLevelVar` storage `Value` branch style from the handover: exact helper, narrow branch, then final no-TypeError/preservation theorem. Use C3 lemmas as theorem dependencies but do not re-prove the update-binop path inside this component.

#### Not to try
Do not weaken the strengthened side conditions to make callers easier. Do not use broad `gvs[..., AllCaseEqs()]` across the whole `TopLevelVar` proof and then try to repair dozens of goals; this was identified as unworkable.

#### Argument
The assignment proof is by the existing mutual recursion over `assign_target` and `assign_targets`. The invariant is joint/all-result where needed: state/accounts typing are preserved and TypeError is excluded under runtime target typing, runtime operation typing, shape matching, and assignable context. For top-level targets, `assign_target_assignable_context` supplies the static module/declaration/layout facts that prevent lookup/storage/hashmap shape errors from becoming TypeError; `target_runtime_typed` supplies the leaf type for recursive subscript assignment. Tuple/list targets consume the list IH and target/value assignability relation elementwise.

#### Definition design
Use the current definitions as proof interfaces, not rewrite targets. `assign_operation_matches_target_shape` prevents applying append/pop/update to the wrong target shape. `assign_target_assignable_context` is the runtime writability/context boundary: scoped assignability, top-level module existence, declaration shape, storage slot/hashmap slot availability, and nonempty hashmap subscript path. `target_assignment_values_assignable` is the tuple/list boundary and should supply both runtime typedness and assignability/context facts for each component. Failure sign: if a branch needs to inspect unrelated evaluator cases, add a small branch helper matching the semantic branch instead of broad `AllCaseEqs()` cleanup.

#### Code structure
Primary edits belong in `semantics/prop/vyperTypeStatePreservationScript.sml`, near existing storage/top-level helpers and the `Resume assign_target_sound_mutual[...]` blocks. Compatibility corollaries belong in `semantics/prop/vyperTypeAssignSoundnessScript.sml` only after the mutual theorem is cheat-free. Do not move static env-extension facts into this file; keep environment weakening in the existing env theories.

### C1.1: Finish preservation-only assignment branches
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: These branches only require state/accounts preservation and are direct consumers of existing update/storage preservation lemmas.
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.1

#### Progress note
Same obligation as prior preservation branch component, now authorized as a leaf.

#### Summary
Remove remaining preservation-only suspends/cheats for assignment target recursion if the C0 audit reports them reachable. Use `sound_ScopedVar` as the local model and mirror the evaluator recursion for top-level, immutable, tuple target, and target-list cons branches.

#### Statement
Current-source preservation mutual theorem(s) in `vyperTypeStatePreservationScript.sml` around the first assignment-target mutual proof, including suspended cases named `TopLevelVar`, `ImmutableVar`, `TupleTargetV`, and `assign_targets_cons` if still present.

#### Approach
Unfold only the relevant `assign_target`/`assign_targets` branch and use existing preservation lemmas for `set_var`, storage read/write, immutable operations, and recursive subscript assignment. For tuple/list targets, induct through the existing mutual IH rather than starting a new list induction outside the theorem.

#### Not to try
Do not prove a separate preservation theorem by re-inducting over targets. Do not touch no-TypeError branches here except where the source theorem combines them.

### C1.2: Prove `assign_target_sound_mutual[sound_TopLevelVar]` HashMapRef branch
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: The handover identifies the exact branch and required facts; the proof should be a focused helper plus local branch discharge.
- Dependencies: C0
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.2, TYPE_SYSTEM_REWRITE_PLAN lines 271-292

#### Progress note
Refines the old `TopLevelVar` high-risk case into the single HashMapRef branch with a branch-helper boundary.

#### Summary
Close the `lookup_global ... = INL (HashMapRef is_transient base_slot kt vt)` branch in `sound_TopLevelVar`. Add a narrowly stated helper if needed before editing the large `Resume` proof. The helper should bridge top-level hashmap declaration/context facts to recursive subscript no-TypeError/preservation after the hashmap prefix.

#### Statement
Inside `Theorem assign_target_sound_mutual`, `Resume assign_target_sound_mutual[sound_TopLevelVar]`: prove the `HashMapRef` semantic branch without `cheat`. Any helper must preserve the current theorem’s strengthened hypotheses, especially `assign_target_assignable_context cx gv st` and `assign_operation_matches_target_shape gv op`.

#### Approach
First isolate the branch by `lookup_global`. Use `assign_target_assignable_context` to obtain nonempty `sbs` and slot/declaration availability. Use `top_level_HashMap_decl` or equivalent lookup consistency to connect the returned `HashMapRef` with `HashMapT kt vt`, then use the strengthened `target_path_step_type` key invariant to traverse the hashmap prefix and call `assign_subscripts_no_type_error_runtime_typed` on the value-type suffix.

#### Not to try
Do not attempt the branch inside a large unexplained `AllCaseEqs()` split. Do not treat hashmap key evaluation as an untyped runtime fact; the strengthened `target_path_step_type` is the intended source of key well-typedness.

### C1.3: Prove `assign_target_sound_mutual[sound_TopLevelVar]` ArrayRef branch
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: ArrayRef is localized to storage-array assignment operations and can be split into append/pop versus ordinary element/path update.
- Dependencies: C0
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.2, TYPE_SYSTEM_REWRITE_PLAN lines 293-300

#### Progress note
Splits the previous combined top-level residual into the ArrayRef branch after HashMapRef.

#### Summary
Close the `ArrayRef` top-level branch in `sound_TopLevelVar`. Handle storage-array `AppendOp`/`PopOp` separately from ordinary subscript assignment. Reuse existing array traversal and storage write/read no-TypeError helpers rather than unfolding storage internals in the mutual proof.

#### Statement
Inside `Theorem assign_target_sound_mutual`, `Resume assign_target_sound_mutual[sound_TopLevelVar]`: prove the `ArrayRef` semantic branch without `cheat`.

#### Approach
Split on the assignment operation before destructing storage details. For append/pop use `assign_operation_runtime_typed` shape facts to get dynamic-array requirements. For ordinary element/path assignment, resolve the array element/reference, establish the recursive leaf type, invoke `assign_subscripts_no_type_error_runtime_typed`, and finish with the storage write no-TypeError/value typing helper.

#### Not to try
Do not conflate `ArrayRef` with the already-proved storage `Value` branch; array references have distinct append/pop and element-resolution paths. Do not bypass operation-shape side conditions.

### C1.4: Finish `sound_ImmutableVar` and `sound_TupleTargetV` branches
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: Both branches are structurally simpler than top-level storage: immutable assignment is ruled out by assignability/context, and tuple targets follow the existing target-list relation.
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.2

#### Progress note
Keeps the two named TASK residuals together because they are small non-storage branches of the same mutual theorem.

#### Summary
Remove cheats from `sound_ImmutableVar` and `sound_TupleTargetV` in `assign_target_sound_mutual`. Immutable writes should be impossible or no-TypeError by context; tuple target assignment should delegate to the target-list mutual conjunct.

#### Statement
`Resume assign_target_sound_mutual[sound_ImmutableVar]` and `Resume assign_target_sound_mutual[sound_TupleTargetV]` in current source.

#### Approach
For `ImmutableVar`, unfold the assignment target evaluator enough to expose the impossible writable assignment/context contradiction or the non-TypeError lookup path. For `TupleTargetV`, use the mutual theorem’s target-list conjunct and `target_assignment_values_assignable` to supply per-element value typing and assignability.

#### Not to try
Do not introduce a special-purpose tuple assignment induction outside the mutual theorem. Do not weaken immutable assignability assumptions; immutable writes must be ruled out by the existing context predicate.

### C1.5: Finish `sound_assign_targets_cons` target-list branch
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: The cons case follows the recursive structure of `assign_targets`; the IHs correspond to head target and tail target-list assignments.
- Dependencies: C0, C1.4
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.2

#### Progress note
Covers the TASK-named `sound_assign_targets_cons` residual.

#### Summary
Remove the cheat from the cons case of the assignment target-list soundness conjunct. Split on head assignment result, then tail assignment result, preserving all-result state/account invariants and excluding TypeError in each branch.

#### Statement
`Resume assign_target_sound_mutual[sound_assign_targets_cons]` in current source.

#### Approach
Use the head-target IH under the head value/type/assignability facts, then use the tail-list IH on the post-head state. The context predicate for target lists should be consumed elementwise; if missing in the local context, prove a small projection lemma for `target_assignment_values_assignable` rather than destructing the full typing relation repeatedly.

#### Not to try
Do not assume the state is unchanged after the head assignment. Assignment soundness is all-result precisely because partial updates may occur before later failure.

### C1.6: Refresh assignment compatibility wrappers
- Kind: `proof`
- Risk: 1
- Work priority: 50
- Work units: 3
- Rationale: Once the mutual theorem has no local cheats, these wrapper theorems are direct projections/corollaries.
- Dependencies: C1.2, C1.3, C1.4, C1.5
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.3

#### Progress note
Same wrapper obligation as before; no architecture change.

#### Summary
Prove or repair `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error` in `vyperTypeAssignSoundnessScript.sml` as compatibility corollaries. They should not drive internal proof structure.

#### Statement
Current-source theorems in `semantics/prop/vyperTypeAssignSoundnessScript.sml`: `assign_target_no_type_error`, `assign_target_update_no_type_error`, `assign_target_append_no_type_error`.

#### Approach
Import/use the appropriate conjunct of `assign_target_sound_mutual`; instantiate operation and side conditions, then project `no_type_error_eval` or result no-TypeError. If a wrapper lacks a hypothesis now required by the strengthened theorem, either derive it from existing wrapper premises or make it a compatibility theorem for the corrected stronger internal theorem, updating only callers permitted by the task.

#### Not to try
Do not duplicate target evaluator case analysis in these wrappers. Do not keep old weaker wrappers with cheats if their callers actually need the stronger side conditions.

### C2: Statement soundness For-cons repair path
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The overall For-cons repair architecture remains valid; only the scheduler gate needs refinement so the helper subtree completes before the caller patch.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0547, E0549

#### Progress note
Refines the prior C2 plan after TO_type_system_rewrite-20260520T182357Z_m34610_t001/11 showed the scheduler selected C2.0.2.3 too early. Prior proof evidence is preserved.

#### Summary
Statement soundness repair remains focused on the For-cons exception tail. Keep the helper-first architecture: prove reusable suffix helpers, then patch the core theorem. The current update fixes dependency metadata that let the caller patch appear before the needed helper artifacts. No mathematical obligation is changed.

#### Approach
Proceed through the C2.0.2 helper chain before any caller proof patch. This component only refines scheduling and carries forward prior proof progress.

#### Not to try
Do not begin the core For-cons patch while the helper region is still broken or while `for_cons_non_loop_exception_suffix` is unproved. Do not solve this by editing unrelated statement-soundness branches.

#### Argument
The For-cons branch should be repaired by isolating the propagated non-loop exception suffix as a local helper boundary before touching the evaluator mutual proof. The body IH supplies no-TypeError and return-exception typing for the body result; pushed/pop-scope helper assumptions supply the final invariants. Once the suffix lemma exists, the core theorem branch should instantiate it directly instead of destructing exceptions in the caller.

#### Definition design
No new definitions are introduced in C2. The proof interface is theorem-based: children under C2.0.2 establish For-cons helper lemmas with conclusions matching the caller's final conjunction. Failure signs are attempts to duplicate evaluator case analysis or to re-enter the old `Cases_on y`/`suspend` proof shape in the core theorem before the suffix boundary is closed.

#### Code structure
All edits in this subtree are local to `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Helper lemmas go near the existing `for_cons_*` helper block; the core mutual theorem patch is a later component and must not be edited before the helper boundary closes.

### C2.0: For-cons helper and caller repair staging
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: This parent remains the staging node for helper-first For-cons repair. The only change is making the child dependency chain explicit enough for scheduling.
- Progress transition: `refinement`
- Carries progress/evidence from: E0547, E0549

#### Progress note
Scheduler-only refinement; existing mathematical strategy and prior closure evidence are carried forward.

#### Summary
Stage the For-cons repair so helper lemmas are completed before the core theorem patch. Carry forward the proved ReturnException suffix helper. Require the non-loop suffix helper child to close before `eval_for_cons_type_sound_core` is edited.

#### Approach
Use terminal child dependencies rather than relying on grouping-node progress. The actual artifact needed by the caller is the theorem proved by C2.0.2.2.2.

#### Not to try
Do not assume a dependency on the C2.0.2 grouping node blocks C2.0.2.3; the schedule evidence shows it does not.

#### Argument
The caller proof has a hostile validation context for exact-looking endpoints. Moving the body-IH specialization and popped-scope assembly into helpers avoids this context. Therefore the staging invariant is: all helper artifacts must be available before the core theorem branch is patched.

#### Definition design
No definitions. Boundary theorems should package existential return-typing evidence and expose the final suffix conjunction directly to the caller.

#### Code structure
Keep helper theorem edits in the local helper block and keep caller edits in the later C2.0.2.3 component. Do not mix cleanup/projection/suffix work with the core mutual theorem patch.

### C2.0.1: Carry forward the case-shaped ReturnException weakening corollary
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This support lemma/corollary was already proved before the failed caller patch and remains the mathematical kernel: it converts the body-IH case package for `INR (ReturnException v)` into return typing in the outer environment.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0541, C2.0.1@old

#### Progress note
No new executor work is intended here. Retain the proved case-shaped weakening result and use it inside the new consumer lemma when convenient.

#### Summary
- Keep the already proved ReturnException weakening support fact.
- It justifies weakening from an environment extending `extend_local env id ty F` back to `env` for ReturnException typing.
- It is support for the new consumer lemma, not a place for further caller tactics.

#### Statement
Use the existing proved case-shaped corollary in `vyperTypeStmtSoundnessScript.sml`; if the current source name is available, prefer `for_cons_body_result_return_exception_typed_case_spec` or the earlier E0541 equivalent.

#### Approach
No proof work unless the source was damaged by failed edits. If necessary, restore the already proved lemma exactly as it replayed before E0542's caller suffix attempts.

#### Not to try
Do not re-open the large `eval_for_cons_type_sound_core` proof from this component. Do not try to strengthen or rename this support lemma unless the new consumer lemma genuinely cannot use it.

### C2.0.2: For-cons non-loop exception helper sequence
- Kind: `boundary_lemma_group`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The previous mathematical decomposition remains sound: prove the For-cons helper boundary before patching the core theorem. This refinement only makes the scheduling gate explicit so the helper children complete before the downstream proof patch begins.
- Progress transition: `refinement`
- Carries progress/evidence from: E0547, E0549

#### Progress note
Refines the prior C2.0.2 plan after scheduler evidence TO_type_system_rewrite-20260520T182357Z_m34610_t001/11 showed C2.0.2.3 was incorrectly next. Prior proof progress for C2.0.2.1 and the C2.0.2.2 decomposition is preserved.

#### Summary
Local For-cons exception-tail work remains a helper-first sequence. The proved ReturnException suffix helper is carried forward. The repaired non-loop suffix boundary is decomposed into cleanup, packaged projection, and suffix assembly. Only after the suffix assembly checkpoint closes may the core theorem patch begin.

#### Approach
Execute the helper-child chain in order: cleanup, packaged projection, suffix assembly. Treat C2.0.2.3 as blocked until C2.0.2.2.2 is proved and reviewed because the core proof requires the concrete theorem artifact `for_cons_non_loop_exception_suffix`, not merely the grouping intention.

#### Not to try
Do not begin C2.0.2.3 while the helper region is still broken or while `for_cons_non_loop_exception_suffix` is unproved. Do not rely on a dependency on the grouping node C2.0.2 to gate a descendant proof patch; use the terminal child dependency explicitly.

#### Argument
The final For-cons propagated non-loop exception branch should not be solved by splitting the exception inside `eval_for_cons_type_sound_core`. The body IH already gives, for the concrete body evaluation returning `INR exn`, both `no_type_error_result (INR exn)` and an environment under which `return_exception_typed` holds. The popped-scope assumptions already give the final state/accounts/env invariants after leaving the loop scope. Therefore the proof boundary is: package the body-IH exception projection, assemble `for_cons_non_loop_exception_suffix`, then invoke that lemma in the core proof. The dependency chain must be terminal-child based because the grouping component `C2.0.2.2` has no direct proof artifact; its child `C2.0.2.2.2` is the actual lemma needed downstream.

#### Definition design
No new definitions are introduced. The proof interface is theorem-based: `for_cons_body_ih_exception_projection` must expose the body-IH facts without destructing the existential in the caller, and `for_cons_non_loop_exception_suffix` must expose the exact final conjunction shape needed by the core For-cons branch. A failure sign is any proof attempt that re-enters the old endpoint-validation pattern with exact assumptions after `mp_tac`/`strip_tac`; in that case the projection interface should be adjusted rather than patching the core theorem.

#### Code structure
All work in this subtree is local to `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Place projection/suffix helpers in the helper block near the existing `for_cons_body_ih_*` and `for_cons_return_exception_suffix` theorems. Do not edit `eval_for_cons_type_sound_core` until `C2.0.2.2.2` is closed. The downstream core patch remains in C2.0.2.3 and should only call the completed suffix helper.

### C2.0.2.1: Carry forward proved ReturnException branch-suffix helper
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0545 proved this helper and E0546 confirms it remains present and useful after correcting the final case shape to `unit + exception`. No additional executor work is needed unless later edits accidentally break it.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.0.2.1, E0545

#### Progress note
This is carried forward unchanged as the ReturnException subcase engine for the new non-loop-exception suffix lemma.

#### Summary
- Keep the proved `for_cons_return_exception_suffix` theorem.
- It should have final case type `unit + exception`, matching the core theorem residual.
- The new non-loop helper will use it internally for `ReturnException v`.
- Do not try to apply this helper directly at the old caller residual again.

#### Statement
Existing theorem to preserve:
```sml
Theorem for_cons_return_exception_suffix:
  !env env_after cx id ty ret_ty body stp st_body v.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    state_well_typed stp /\
    accounts_well_typed stp.accounts /\
    env_consistent (extend_local env id ty F) cx stp /\
    eval_stmts cx body stp = (INR (ReturnException v), st_body) /\
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body stp0 = (res_body, st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL u => env_consistent env_after cx st_body0
        | INR exn =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn)) ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR (ReturnException v)) /\
    (case (INR (ReturnException v) : unit + exception) of
     | INL _ => T
     | INR exn => return_exception_typed env ret_ty exn)
```

#### Approach
No proof work should be performed for this component unless the source has regressed. If regression occurs, restore the E0545 shape and proof before attempting downstream components.

#### Not to try
Do not reintroduce identity/projection helper variants for `return_exception_typed`; they did not address the caller-context problem.

### C2.0.2.2: Repair and prove For-cons non-loop-exception suffix boundary
- Kind: `boundary_lemma_group`
- Risk: 2
- Work priority: 22
- Work units: 0
- Rationale: The logical facts are present in the body IH and popped-scope assumptions; E0549 shows the old proof interface, not the statement, was brittle. Factoring a packaged projection theorem before suffix assembly makes the remaining work standard.
- Supersedes: C2.0.2.2@E0546, C2.0.2.2@E0548, C2.0.2.2@E0549
- Progress transition: `replacement`
- Carries progress/evidence from: E0549, E0548, E0546
- Invalidates prior progress/evidence: old C2.0.2.2 leaf strategy: inline/body-IH specialization followed by exact endpoint acceptance

#### Progress note
E0549 is accepted as design evidence: prior proof attempts do not close this component, but they identify the interface to avoid.

#### Summary
Replace the failed single helper proof with a three-step local repair. First clean the broken helper region left by E0549. Then prove a body-IH projection lemma that keeps the exception existential packaged. Finally prove `for_cons_non_loop_exception_suffix` from that projection, the popped invariants, and the existing ReturnException weakening helper.

#### Description
This component remains the boundary needed before patching the downstream `eval_for_cons_type_sound_core` suspend. It owns only helper theorems around `for_cons_body_ih_*` and `for_cons_non_loop_exception_suffix` in `semantics/prop/vyperTypeStmtSoundnessScript.sml`; do not edit the core mutual theorem here.

#### Statement
Target helper family in `semantics/prop/vyperTypeStmtSoundnessScript.sml`: a new `for_cons_body_ih_exception_projection` theorem followed by the existing intended `for_cons_non_loop_exception_suffix` statement, with the suffix proof using the projection lemma rather than inline body-IH specialization.

#### Approach
The body IH yields a conjunction for exactly `(stp, INR exn, st_body)`; the projection lemma should instantiate that IH and keep the existential packaged in the theorem conclusion. In the suffix helper, split the final conjunction first; assumptions solve the popped invariant conjuncts, the projection solves no-TypeError, and exception case analysis plus the existing ReturnException helper solves the return-typing conjunct.

#### Not to try
Do not repeat the E0546/E0548/E0549 shape: `mp_tac` the body IH, `strip_tac`, `gvs[]`, then solve an exact-looking endpoint with `first_assum ACCEPT_TAC`, `qpat_assum ACCEPT_TAC`, or a local `by` block. Do not use unparenthesized `Cases_on exn >> ...`. Do not edit `eval_for_cons_type_sound_core` or the old `suspend "ReturnException_tail"` in this component.

#### Argument
For the For-cons non-loop-exception tail, the recursive body IH is stronger than needed. Specialized to the actual body evaluation `(stp, INR exn, st_body)`, it yields no type error for `INR exn` and, for an exception result, an existential environment extending the loop-body environment in which the exception is return-typed. The suffix theorem additionally assumes that popping the loop scope has restored `state_well_typed`, `accounts_well_typed`, and `env_consistent env cx`; therefore only no-TypeError and outer-env return typing need proof. Continue and Break are excluded; ordinary non-return exceptions are handled by definitions; ReturnException is weakened back to `env` by the existing return-specific helper path.

#### Definition design
No semantic definitions should change. The proof interface change is to introduce a projection lemma whose conclusion keeps the body-IH exception facts packaged, especially the existential `env_exn`, instead of opening the existential and then trying to close exact assumptions. If the executor sees a fresh free `env_exn` from destructing the body-IH existential before the theorem boundary, that is a failure sign.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near the existing For-cons helper block after `for_cons_return_exception_suffix` and before the downstream `eval_for_cons_type_sound_core`. Place the new projection lemma before `for_cons_non_loop_exception_suffix`.

### C2.0.2.2.0: Clean up failed C2.0.2.2 helper edits
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: This is mechanical source hygiene: remove or overwrite the partial failed proof text left by E0549 so the next helper statements start from a known clean region.
- Carries progress/evidence from: E0549
- Invalidates prior progress/evidence: partial failed source around for_cons_body_ih_no_type_error_result / for_cons_non_loop_exception_suffix from E0549

#### Progress note
The cleanup preserves successful preceding helpers and discards only unproved/broken tactics introduced during stuck attempts.

#### Summary
Restore the helper block after `for_cons_return_exception_suffix` to a clean state. Keep all already-proved preceding theorems. Remove failed proof fragments for `for_cons_body_ih_no_type_error_result` and the modified `for_cons_non_loop_exception_suffix` if they do not build. Verify no obsolete failed theorem remains before adding the new projection lemma.

#### Description
The source is currently partial/broken around line ~1693. This component is not a semantic refactor; it only prevents stale failed tactics from confusing the projection proof.

#### Approach
Edit only the local helper region in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. It is acceptable that the theory still fails later until the new helper components are completed, but there should be no leftover failed proof fragment from E0549 in this region.

#### Not to try
Do not delete successful earlier helper theorems such as `for_cons_body_ih_return_exception_typed` or `for_cons_return_exception_suffix`. Do not move to the downstream core theorem as part of cleanup.

### C2.0.2.2.1: Prove packaged body-IH exception projection for For-cons
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 2
- Rationale: This is a direct specialization of the body IH at the actual evaluation triple. Keeping the existential packaged avoids the exact-endpoint validation pattern that defeated the no-TypeError-only projection.
- Dependencies: C2.0.2.2.0
- Checkpoint: yes
- Supersedes: failed for_cons_body_ih_no_type_error_result from E0549
- Progress transition: `replacement`
- Carries progress/evidence from: E0549
- Invalidates prior progress/evidence: standalone no-TypeError-only projection proof that destructed the body-IH result

#### Progress note
This replaces the failed no-TypeError-only projection with a stronger packaged projection that downstream code can consume without reopening the body IH.

#### Summary
Prove `for_cons_body_ih_exception_projection`. It specializes the body IH once and returns both `no_type_error_result (INR exn)` and the exception existential. The existential must remain in the conclusion, not be destructed into the proof context before the theorem boundary. This checkpoint validates the repaired interface.

#### Description
The theorem should be placed after the existing return-specific body-IH helper/`for_cons_return_exception_suffix` block. It intentionally has all antecedents in the same shape as the body IH consumer so callers can use it without recreating the fragile `mp_tac` endpoint pattern.

#### Statement
```sml
Theorem for_cons_body_ih_exception_projection:
  !env env_after cx id ty ret_ty body stp st_body exn.
    state_well_typed stp /\
    accounts_well_typed stp.accounts /\
    env_consistent (extend_local env id ty F) cx stp /\
    eval_stmts cx body stp = (INR exn, st_body) /\
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body stp0 = (res_body, st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL u => env_consistent env_after cx st_body0
        | INR exn0 =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn0)) ==>
    no_type_error_result (INR exn) /\
    ?env_exn.
      env_extends (extend_local env id ty F) env_exn /\
      env_consistent env_exn cx st_body /\
      return_exception_typed env_exn ret_ty exn
```

#### Approach
Use the universally quantified body-IH assumption with the four actual antecedents. A robust proof should specialize the IH, simplify the `case` for `INR exn`, and immediately project the no-TypeError conjunct and the existential conjunct. If opening the existential, use its witness immediately for the theorem's existential conclusion; do not leave an exact assumption/goal endpoint as the final proof step.

#### Not to try
Do not prove only `no_type_error_result (INR exn)` by destructing the full IH result and ending at an exact assumption; that is precisely the E0549 failure. Do not introduce a free `env_exn` in hypotheses unless it is immediately used as the witness for the theorem's existential conclusion.

### C2.0.2.2.2: Prove full non-loop-exception suffix helper using the projection
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Once the packaged projection lemma exists, the suffix theorem is small assembly: assumptions solve popped invariants, the projection solves no-TypeError, and exception cases plus the existing ReturnException helper solve return typing.
- Dependencies: C2.0.2.2.1
- Checkpoint: yes
- Supersedes: old for_cons_non_loop_exception_suffix proof attempt from E0548/E0549
- Progress transition: `replacement`
- Carries progress/evidence from: E0548, E0549
- Invalidates prior progress/evidence: inline body-IH specialization inside for_cons_non_loop_exception_suffix

#### Progress note
This keeps the intended helper theorem but changes its implementation dependency to the packaged projection lemma, so downstream C2.0.2.3 can use the same boundary idea without re-entering the old brittle proof context.

#### Summary
Prove `for_cons_non_loop_exception_suffix` after `for_cons_body_ih_exception_projection`. Split the final conjunction explicitly. Use assumptions for popped state/accounts/env, the projection lemma for no-TypeError, and safe parenthesized exception case analysis for return typing. This closes the C2.0.2.2 boundary and unblocks the downstream core-theorem patch.

#### Description
The theorem statement should remain equivalent to the previous intended suffix helper from source/plan: it consumes popped-scope invariants, original body preconditions, actual body evaluation, and body IH, and concludes popped invariants, no-TypeError for the propagated exception, and return typing at `env`.

#### Statement
Use the existing intended statement of `for_cons_non_loop_exception_suffix` in the source/plan:

```sml
Theorem for_cons_non_loop_exception_suffix:
  !env env_after cx id ty ret_ty body stp st_body exn.
    exn <> ContinueException /\
    exn <> BreakException /\
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    state_well_typed stp /\
    accounts_well_typed stp.accounts /\
    env_consistent (extend_local env id ty F) cx stp /\
    eval_stmts cx body stp = (INR exn, st_body) /\
    (!stp0 res_body st_body0. ...body IH as in the projection lemma...) ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
```

#### Approach
After `rpt gen_tac >> strip_tac`, isolate each output conjunct with explicit conjunction splitting. For no-TypeError, apply `for_cons_body_ih_exception_projection` and project its first conjunct. For the final return-typing conjunct, simplify the sum case, then perform carefully scoped `Cases_on exn`; Continue/Break close by contradiction hypotheses, ReturnException uses `for_cons_body_ih_return_exception_typed`, and non-return exception constructors should close from `return_exception_typed_def` plus `no_type_error_result_def` as appropriate.

#### Not to try
Do not put `>>` after `Cases_on exn` unless each branch is parenthesized; E0548 showed this leaks impossible Continue/Break branches into ordinary exception proof paths. Do not use a local `by` proof for no-TypeError against the whole final conjunction. Do not touch or remove the downstream `suspend "ReturnException_tail"` yet; that is owned by the next component.

### C2.0.2.3: Patch `eval_for_cons_type_sound_core` to call the non-loop suffix lemma
- Kind: `proof_patch`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: This proof patch is standard only after the terminal suffix helper child has produced `for_cons_non_loop_exception_suffix`. The explicit dependency fixes the scheduler error without changing the mathematical obligation.
- Dependencies: C2.0.2.2.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C2.0.2.3

#### Progress note
Refines only the dependency/priority metadata for the existing C2.0.2.3 obligation. No source-level proof progress for C2.0.2.3 has occurred, so there is no invalidated proof evidence.

#### Summary
Patch the final propagated non-loop exception branch in `eval_for_cons_type_sound_core`. This component is blocked until `C2.0.2.2.2` proves the suffix helper. Once unblocked, instantiate `for_cons_non_loop_exception_suffix` with the propagated exception and delete the old `suspend "ReturnException_tail"` path. Keep normal/continue/break branches unchanged.

#### Statement
Target theorem remains the existing source theorem:
```sml
Theorem eval_for_cons_type_sound_core:
  evaluate_type env.type_defs ty = SOME tyv /\
  EVERY (value_has_type tyv) (v::vs) /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  ... /\
  eval_for cx tyv id body (v::vs) st = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ env_consistent env cx st' /\
  no_type_error_result res /\
  case res of
  | INR exn => return_exception_typed env ret_ty exn
  | INL _ => T
```

#### Approach
After the existing proof derives `loop_res = INR y`, rewrites `st_after`, and obtains the final equation `(res,st') = (INR y, st_body with scopes := TL st_body.scopes)`, instantiate `for_cons_non_loop_exception_suffix` with `exn = y`. Supply `y <> ContinueException` and `y <> BreakException` from the preceding branch splits and pass the body-IH/evaluation/state assumptions directly. The proof should be a local replacement of the failing suspended branch.

#### Not to try
Do not split `Cases_on y` in the core theorem. Do not call `for_cons_return_exception_suffix` directly from the core theorem. Do not begin this component before C2.0.2.2.2 is proved; doing so would violate the helper-first strategy and re-enter the known brittle caller context.

### C2.0.2.4: Clean up obsolete For-cons ReturnException scaffolding after the core proof builds
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 30
- Work units: 1
- Rationale: After the wider suffix lemma and core patch build, removing unused failed scaffolding is mechanical and prevents the next executor from following the abandoned strategy.
- Dependencies: C2.0.2.3
- Supersedes: C2.0.2.3@prior
- Progress transition: `replacement`
- Invalidates prior progress/evidence: C2.0.2.3@prior

#### Progress note
The prior cleanup leaf is replaced by this cleanup after the new patch, because the set of obsolete scaffolding is now determined by the non-loop suffix refactor.

#### Summary
- Remove the failed `suspend "ReturnException_tail"` and any unused helper/projection experiments introduced for the old direct patch.
- Keep `for_cons_return_exception_suffix` and `for_cons_non_loop_exception_suffix` if both are used.
- Build `vyperTypeStmtSoundnessTheory` after cleanup.
- Do not perform broad formatting or unrelated statement-soundness cleanup.

#### Approach
Search locally around the For-cons helper block and `eval_for_cons_type_sound_core` for unused identity/projection lemmas or commented/failed proof fragments from the direct ReturnException strategy. Delete only code that is unused after the successful build; if a helper is still referenced by the new non-loop suffix theorem, keep it.

#### Not to try
Do not remove general For-cons decomposition lemmas or scope-pop preservation helpers. Do not touch assignment/builtin/call obligations in this cleanup component.

### C2.1: Derive assignment statement side conditions for AnnAssign/Assign/AugAssign
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: The TASK lists the missing side conditions and their intended sources; this is a standard consumer proof once assignment target soundness is available.
- Dependencies: C1.6, C3.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C2.1, TYPE_SYSTEM_REWRITE_PLAN lines 236-258

#### Progress note
Refines the previous statement-assignment repair component into the exact strengthened-side-condition work.

#### Summary
Repair `eval_all_type_sound_mutual[AnnAssign]`, `[Assign]`, and `[AugAssign]` after strengthened assignment preservation. Derive `assign_operation_matches_target_shape gv op` and `assign_target_assignable_context cx gv st` from statement typing/evaluated target facts, and feed them into assignment soundness.

#### Statement
Current-source resumed branches of `eval_all_type_sound_mutual` for `AnnAssign`, `Assign`, and `AugAssign` in `vyperTypeStmtSoundnessScript.sml`.

#### Approach
For ordinary assignment, operation shape is the plain assignment constructor and should simplify from the definition. For `AugAssign`, derive update-operation shape from target kind and static operator typing. For `AnnAssign`, use `assignable_type` plus `assignable_type_evaluate_not_NoneTV` / `assignable_type_not_NoneT` to replace old non-None side-condition cheats.

#### Not to try
Do not call assignment soundness with missing side conditions and patch by weakening it. Do not use old local non-None cheats now subsumed by `assignable_type`.

### C2.2: Feed tuple/list assignment values through `target_assignment_values_assignable`
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: Tuple/list assignment is an elementwise projection of an existing relation, not a new evaluator proof.
- Dependencies: C2.1
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C2.1

#### Progress note
Covers the tuple/list part of the task’s statement-level assignment obligations.

#### Summary
For tuple/list assignment branches in statement soundness, use `target_assignment_values_assignable` to supply typedness, assignability, and context side conditions to target-list assignment soundness. Add projection lemmas if the relation is awkward to destruct in the large theorem.

#### Statement
Tuple/list assignment subcases inside the current `AnnAssign`/`Assign` statement proof branches, plus any small projection lemmas for `target_assignment_values_assignable`.

#### Approach
Prove small projections such as head target runtime typed, head assignable context, head value type, and tail relation preservation if repeated destructing is brittle. Then the large statement proof should split only on evaluated target/value list shapes and invoke the target-list conjunct of `assign_target_sound_mutual`.

#### Not to try
Do not manually rebuild per-element assignability from expression typing in every tuple/list branch. Do not assume list lengths by arithmetic alone; use the relation’s length/zip facts.

### C2.3: Close non-assignment statement mutual residuals reported by audit
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 8
- Rationale: After the explicit For_cons and assignment repairs, any remaining statement cheats are localized resumed evaluator branches with existing IHs.
- Dependencies: C2.0, C2.2, C4.4
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C2.4

#### Progress note
This is scoped only to C0-reported reachable residuals in `vyperTypeStmtSoundnessScript.sml`; it is not a license for broad statement refactoring.

#### Summary
Remove any remaining reachable cheats/suspends inside `eval_all_type_sound_mutual` not covered by C2.0-C2.2. Expected cases are loop/control-flow or expression/builtin consumer branches, each closed by existing mutual IH and subsystem soundness lemmas.

#### Statement
Any C0-reported reachable `cheat`/unfinished `suspend` in `semantics/prop/vyperTypeStmtSoundnessScript.sml` within `eval_all_type_sound_mutual` or its strict helper lemmas, excluding assignment branches already covered above.

#### Approach
For each residual, first identify the evaluator branch and the exact IH conjunct needed. If an existential/env-extension package appears, create a small boundary helper consuming the whole IH result rather than reconstructing it inside the large theorem. Build after each branch or small cluster.

#### Not to try
Do not solve multiple suspended branches with one giant `gvs[AllCaseEqs()]`. Do not add downstream call-wrapper dependencies to statement soundness.

### C3: Update-binop and assignment-subscript runtime-typed path
- Kind: `proof_group`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: The inherited cheats form a localized dependency chain from binop no-TypeError through update assignment leaf and recursive subscript preservation.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C3

#### Progress note
Replaces the old high-risk inherited path gate with an explicit linear chain of low-risk theorem families.

#### Summary
Prove the known inherited update-binop path: `well_typed_binop_no_type_error`, `well_typed_update_binop_no_type_error`, `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`. Keep the work localized to builtin/binop and assignment-subscript lemmas.

#### Approach
Prove bottom-up: binop, update-binop, leaf assignment operation, then structural/recursion induction over subscript assignment. Use the induction principles generated for recursive functions where available.

#### Not to try
Do not treat the inherited cheats as statement-level issues. Do not duplicate all binop cases inside `assign_subscripts`; delegate to the binop/update leaf theorem.

#### Argument
Update assignment reaches a leaf operation that evaluates a typed binary operation on the old leaf value and RHS value. The binop theorem excludes TypeError for statically well-typed operands; the update-binop theorem packages that for assignment update operations. Recursive subscript assignment preserves no-TypeError and type by induction over the subscript path: prefix traversal preserves the leaf type, the leaf operation is sound, and the result is reinserted into a value of the original type.

#### Definition design
The proof interface should remain: static binop typing + runtime operand typing -> no TypeError/success type; assignment operation runtime typed + leaf typed -> operation no TypeError/success type; target path typed + root value typed -> recursive subscript no TypeError/preservation. If a recursive subscript proof needs an operation-specific fact, add it at the leaf-operation boundary, not by special-casing every subscript constructor.

#### Code structure
Binop lemmas belong in `vyperTypeBuiltinsScript.sml` near existing `well_typed_binop_*`. Assignment-subscript and operation leaf lemmas belong in `vyperTypeStatePreservationScript.sml` near existing `assign_subscripts_*` helpers. Do not move these into statement soundness.

### C3.1: Close binop no-TypeError lemmas
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: Case analysis over binop/type constructors is finite and already supported by success typing lemmas.
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C3.1

#### Progress note
Same theorem family as prior C3.1, now explicitly first in the update path.

#### Summary
Prove `well_typed_binop_no_type_error` and use it to prove `well_typed_update_binop_no_type_error` in `vyperTypeBuiltinsScript.sml`.

#### Statement
`Theorem well_typed_binop_no_type_error` and `Theorem well_typed_update_binop_no_type_error` in current source.

#### Approach
Split on the binop and the well-typed-binop relation. Use existing evaluator definitions, integer bound lemmas, decimal/wrapped operation no-error facts, and `well_typed_binop_success_type` where it supplies inversions. Keep arithmetic goals local with existing bound lemmas.

#### Not to try
Do not prove success typing and no-TypeError by separate exhaustive duplicated scripts if one helper can share case analysis. Do not leave update-binop as a wrapper over a cheated binop theorem.

### C3.2: Close assignment operation leaf no-TypeError for update/append/pop/plain assign
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Leaf operation soundness is a small case split on assignment operation, with C3.1 handling update-binop.
- Dependencies: C3.1
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C3.2

#### Progress note
First assignment-side consumer of the binop theorem.

#### Summary
Prove `assign_subscripts_update_leaf_no_type_error` and `assign_operation_runtime_typed_leaf_no_type_error` without cheats. These exclude TypeError at the leaf operation under `assign_operation_runtime_typed` and operation-shape hypotheses.

#### Statement
Current-source theorems named `assign_subscripts_update_leaf_no_type_error` and `assign_operation_runtime_typed_leaf_no_type_error` in `vyperTypeStatePreservationScript.sml`.

#### Approach
Case split on the assignment operation. Plain assignment is direct from value typing; update uses C3.1; append/pop use the strengthened dynamic-array requirement in `assign_operation_runtime_typed` to rule out wrong-shape TypeError. Keep success typing facts available for the preservation component.

#### Not to try
Do not hide append/pop shape requirements in simplification. If pop/append fail, inspect `assign_operation_runtime_typed` first rather than weakening the theorem.

### C3.3: Close recursive assignment-subscript no-TypeError and preservation
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: This is the structural recursive consumer of C3.2 and existing target-path typing lemmas.
- Dependencies: C3.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C3.2

#### Progress note
Completes the task-listed inherited update-binop path.

#### Summary
Prove `assign_subscripts_no_type_error_runtime_typed` and `assign_subscripts_preserves_type_runtime_typed` without inherited cheats. Use recursive subscript/path induction and the leaf operation theorem at the base.

#### Statement
Current-source theorems named `assign_subscripts_no_type_error_runtime_typed` and `assign_subscripts_preserves_type_runtime_typed` in `vyperTypeStatePreservationScript.sml`.

#### Approach
Use the induction principle for `assign_subscripts`/path recursion if available; otherwise induct on the subscript list in the direction matching the function. At each path step, use `target_path_step_type` to prove the traversal cannot raise TypeError and preserves the expected leaf type. At the base, invoke C3.2.

#### Not to try
Do not unfold all storage/top-level target cases here; this theorem is about recursive value subscript assignment, not top-level lookup.

### C4: Builtin, type-builtin, and builtin-typing soundness residuals
- Kind: `proof_group`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Current source isolates builtin residuals to a finite set of constructor branches and small arithmetic/ABI facts. The ABI encode bound has already been added to the typing predicate, removing the old spec gap.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4

#### Progress note
Keeps all task-listed builtin/binop/type-builtin cheats in one subsystem, with binop update path delegated to C3.

#### Summary
Remove reachable cheats in `vyperTypeBuiltinsScript.sml` and strict prerequisite fresh builtin-typing theories. This includes generic builtin no-TypeError/success typing residuals, type-builtin no-TypeError, ABI encode success branches, raw-call return type well-formedness, and Env/MsgGas-related issues if still reachable.

#### Approach
Close static typing prerequisites first if C0 shows them reachable, then generic builtin cases, then type-builtin no-TypeError/success branches. Use existing specialized lemmas such as bytes/crypto/ABI helpers instead of unfolding encoders deeply in every case.

#### Not to try
Do not re-open the old ABI encode unprovability gate unless current source lacks the `vyper_abi_size_bound` repair. Do not treat binop update-assignment cheats here; those are C3.

#### Argument
Builtin soundness is by constructor case analysis: the static typing predicate constrains argument lengths/types and result type; runtime argument typing plus specialized evaluator lemmas show no TypeError and success value typing. Type-builtins are similar but use `type_builtin_result_ok`; ABI encode branches now rely on its `vyper_abi_size_bound` condition to prove bytes length bounds. Raw-call return type well-formedness is arithmetic over `word_size`, `type_slot_size`, and the max-outsize bound.

#### Definition design
Use existing static predicates (`well_typed_builtin_app`, `well_typed_type_builtin_args`, `type_builtin_result_ok`) as the boundary. Do not add ad hoc side conditions in the final wrappers unless the source theorem is demonstrably underspecified; if underspecified, prove a small probe/counterexample before changing a theorem. Failure sign: ABI encode success typing cannot prove bytes length; this should be solved from `vyper_abi_size_bound`, not by weakening `value_has_type`.

#### Code structure
Builtin proofs stay in `semantics/prop/vyperTypeBuiltinsScript.sml`. If C0 shows reachable suspends in `vyperBuiltinTypingScript.sml`, close them there as static typing prerequisites only. Do not mix builtin proofs into statement or call soundness files.

### C4.1: Close reachable `vyperBuiltinTyping` suspended cases
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: These are static constructor cases over builtin typing and only required if C0 proves they are reachable.
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4.1

#### Progress note
Conditional leaf: execute only for C0-reported reachable suspends in `vyperBuiltinTypingScript.sml`.

#### Summary
If `vyperBuiltinTypingScript.sml` suspended builtin typing cases are reachable from `vyperSemanticsHolTheory`, prove exactly those cases. Cases include Len/Not/Neg/Abs/crypto/Env/Acc/etc. as reported by audit.

#### Statement
C0-reported reachable suspended cases in `semantics/prop/vyperBuiltinTypingScript.sml`, especially the large builtin typing case split around `suspend "Len"` etc.

#### Approach
For each constructor, unfold the static typing definition and prove the required result type/argument constraints. Prefer one constructor per edit/build cycle. If a case depends on a runtime semantic fact, that is a sign it belongs in `vyperTypeBuiltinsScript.sml`, not this static layer.

#### Not to try
Do not prove all grep-reported suspends if the theory is not reachable. Do not import runtime soundness theories into static builtin typing.

### C4.2: Close generic builtin no-TypeError and success typing residuals
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: The current proof skeleton already closes most constructors and has explicit fallback points for remaining branches.
- Dependencies: C4.1
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4.2

#### Progress note
Covers the cheat near the end of the generic builtin success/no-error proof skeleton, excluding type-builtins handled by C4.3-C4.4.

#### Summary
Remove the generic builtin proof cheat in `vyperTypeBuiltinsScript.sml` around the large builtin soundness case split. Close Env/Acc/crypto/bytes/arithmetic residuals with existing specialized lemmas.

#### Statement
Current-source generic builtin theorem(s) around line ~2380-2411 of `vyperTypeBuiltinsScript.sml`, including any C0-reported cheat in the proof of builtin success typing/no-TypeError before `Len_result_fits_uint256`.

#### Approach
Identify the exact constructor left by the final `cheat` by temporarily replacing it with `NO_TAC` if needed. Then add a branch-specific lemma or direct call to existing helpers (`Env_builtin_success_type`, `Acc_builtin_sound`, bytes/crypto length lemmas, bounded/wrapped op inversions). Keep arithmetic to small subgoals.

#### Not to try
Do not leave a catch-all `cheat` after many `TRY` tactics; each remaining constructor must be named and closed. Do not use broad `metis_tac` over all builtin lemmas if it obscures a missing side condition.

### C4.3: Prove type-builtin no-TypeError
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: No-TypeError follows by constructor case analysis using argument length/type constraints and context well-typedness.
- Dependencies: C4.1
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4.3

#### Progress note
Covers `well_typed_type_builtin_no_type_error` specifically.

#### Summary
Remove the cheat from `well_typed_type_builtin_no_type_error` in `vyperTypeBuiltinsScript.sml`. Use `well_typed_type_builtin_args_length` and the same constructor split as success typing.

#### Statement
`Theorem well_typed_type_builtin_no_type_error` in current source.

#### Approach
Split on `tb`, unfold `evaluate_type_builtin_def`, `type_builtin_result_ok_def`, and `well_typed_type_builtin_args_def` only for the active constructor. For conversions/extract/ABI cases, use existing no-error facts from conversion/ABI helper theories; if only success-typing helpers exist, prove a small no-TypeError analogue locally.

#### Not to try
Do not rely on success typing theorem alone to prove no-TypeError unless the evaluator equation is already known to be `INL`. Do not add assumptions beyond current theorem without a checked false-statement probe.

### C4.4: Prove ABI encode type-builtin success branches
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: The old ABI bound gap is repaired in `type_builtin_result_ok`, so the three suspended/cheated branches are now finite consumers of ABI bound lemmas.
- Dependencies: C4.3
- Checkpoint: yes
- Supersedes: old ABI encode result-bound gap
- Progress transition: `refinement`
- Carries progress/evidence from: TYPE_SYSTEM_REWRITE_PLAN ABI bound repair note

#### Progress note
Supersedes the stale unprovability concern by using the current source’s `vyper_abi_size_bound` side condition.

#### Summary
Finish `well_typed_type_builtin_success_type[abi_encode]`, `[encode_tuple]`, and `[encode_tuple_nowrap]`. Prove the result `BytesT`/ABI value typing from encoder success and the bound carried by `type_builtin_result_ok`.

#### Statement
`Resume well_typed_type_builtin_success_type[abi_encode]`, `[encode_tuple]`, and `[encode_tuple_nowrap]` in current `vyperTypeBuiltinsScript.sml`.

#### Approach
Unfold the active type-builtin case, extract `vyper_abi_size_bound` from `type_builtin_result_ok`, and use ABI encode length/success typing lemmas to prove the returned bytes/string value fits the result type. If a length lemma is missing, add it next to existing ABI helper lemmas as a strict prerequisite.

#### Not to try
Do not weaken the result type to dynamic bytes without checking the theorem statement. Do not ignore the bound side condition; it is the intended repair.

### C4.5: Close raw-call return type well-formedness and Env/MsgGas support
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: The remaining raw-call theorem is arithmetic over `word_size` and type slot size; Env/MsgGas issues are local builtin constructor facts.
- Dependencies: C4.2
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4.4

#### Progress note
Covers task-mentioned Env MsgGas issues and the visible `raw_call_return_type_well_formed` cheat.

#### Summary
Remove the cheat from `raw_call_return_type_well_formed` and close any remaining Env/MsgGas builtin support theorem reported by C0. These support special-call and builtin soundness wrappers.

#### Statement
`Theorem raw_call_return_type_well_formed` in `vyperTypeBuiltinsScript.sml`, plus any C0-reported reachable Env/MsgGas builtin helper cheat in the same file.

#### Approach
For raw-call, case split on flags and reduce to `word_size_le`, `type_slot_size_def`, and simple natural arithmetic under `flags.rcf_max_outsize < dimword(:256)`. For Env/MsgGas, unfold the relevant builtin evaluator/static typing branch and use context well-typedness fields that type gas/message values.

#### Not to try
Do not solve raw-call by assuming `word_size n < n`; the source already has the split and needs the equality case closed correctly. Do not add global context assumptions to special-call wrappers unless current Env builtin theorem is false and a probe confirms it.

### C5: Call wrapper soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: Call wrappers are downstream consumers of expression/statement/builtin soundness and function signature consistency; they do not require a new evaluator induction.
- Required for completion: yes
- Dependencies: C2, C4
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C5

#### Progress note
Keeps the task-listed call wrapper cheats explicit and downstream of statement/builtin soundness.

#### Summary
Prove `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, and `special_call_no_type_error` in `vyperTypeCallSoundnessScript.sml`. These are wrappers around existing argument/default/body/special-target soundness facts.

#### Approach
Prove external/special wrappers first because they avoid body recursion. Then internal no-TypeError and preservation using the same decomposition. Keep no-TypeError and preservation wrappers as projections from statement/expression joint results rather than duplicating call evaluator case analysis.

#### Not to try
Do not unfold the full statement evaluator inside call wrappers. Do not create an import cycle by making statement soundness depend on call soundness.

#### Argument
For internal calls, static expression typing gives a function signature and argument bounds; `fn_sigs_consistent` and `functions_well_typed_body` recover the callable body typing environment, defaults typing, parameter types, and return type. Argument and default evaluation soundness establish the call-entry state/env invariants; statement soundness for the body excludes TypeError and preserves state/return typing. External and special calls do not recurse into a Vyper body, so they reduce to argument/driver expression soundness and builtin/special-target no-TypeError facts.

#### Definition design
The call proof boundary is wrapper-level: `well_typed_expr ... Call ...` plus `env_consistent`, `state_well_typed`, `context_well_typed`, `accounts_well_typed`, and for internal calls `functions_well_typed`. Do not strengthen public call wrappers unless a checked false-statement probe shows a missing prerequisite. If internal preservation needs return-value typing not exported by statement soundness, add a statement corollary projection rather than re-inducting over statements here.

#### Code structure
All call wrapper edits belong in `semantics/prop/vyperTypeCallSoundnessScript.sml`. Helper lemmas about function signatures/defaults can live near existing `fn_sig_argument_bounds`, `defaults_env_erases_locals`, and `functions_well_typed_body`. Do not create imports from call soundness back into statement soundness.

### C5.1: External and special call no-TypeError wrappers
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: These wrappers avoid internal function body recursion and reduce to argument/driver and builtin/special-target facts.
- Dependencies: C4.5
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C5.1

#### Progress note
Same external/special wrapper obligation as pre-collapse plan.

#### Summary
Prove `external_call_no_type_error` and `special_call_no_type_error` in `vyperTypeCallSoundnessScript.sml`. Use expression argument soundness, optional driver soundness, and special-target builtin support.

#### Statement
`Theorem external_call_no_type_error` and `Theorem special_call_no_type_error` in current source.

#### Approach
Case split on the call target only as much as the theorem statement already distinguishes. Use `ext_call_args_typed` for external calls and current special-call/static builtin facts for the rest. Project `no_type_error_eval` from the expression/builtin soundness theorem used by the evaluator branch.

#### Not to try
Do not try to prove internal call facts in the special-call theorem; the hypotheses explicitly exclude `IntCall` and `ExtCall` for `special_call_no_type_error`.

### C5.2: Internal call no-TypeError wrapper
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: Existing helper lemmas recover function body typing and argument/default alignment; statement soundness supplies body no-TypeError.
- Dependencies: C2.3, C5.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C5.2

#### Progress note
Same theorem as source; proof is authorized after statement soundness is stable.

#### Summary
Prove `internal_call_no_type_error`. Decompose call evaluation into argument evaluation, defaults/parameter setup, body evaluation, and return handling; each phase consumes existing soundness/preservation projections.

#### Statement
`Theorem internal_call_no_type_error` in `vyperTypeCallSoundnessScript.sml`.

#### Approach
Use `fn_sig_argument_bounds`, `internal_call_signature_sound`, and `functions_well_typed_body` to obtain body typing and parameter/default facts. Evaluate arguments/defaults with expression/default soundness. Invoke the statement/body no-TypeError theorem for the function body and propagate through call-return wrapper code.

#### Not to try
Do not reconstruct `functions_well_typed` internals manually in the large proof if `functions_well_typed_body` applies. Do not weaken the theorem to omit `functions_well_typed cx`.

### C5.3: Internal call success preservation wrapper
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: It reuses the internal-call decomposition and projects the success state/value typing facts.
- Dependencies: C5.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C5.3

#### Progress note
Completes the task-listed internal call wrapper pair.

#### Summary
Prove `internal_call_type_preservation`. On successful internal call evaluation, show the final state remains well typed and the returned value is `expr_runtime_typed` for the call expression.

#### Statement
`Theorem internal_call_type_preservation` in `vyperTypeCallSoundnessScript.sml`.

#### Approach
Follow the same evaluator decomposition as C5.2, but retain the final success equation. Use statement body preservation/return typing to prove returned value type and state/accounts invariants. Then simplify `expr_runtime_typed` for the call expression using the signature return type equality from static typing.

#### Not to try
Do not prove this independently from C5.2 by a separate large case split; factor or reuse the same helper decomposition where possible.

### C6: Public fresh soundness wrapper surface
- Kind: `proof_group`
- Risk: 2
- Work priority: 60
- Work units: 0
- Rationale: The frozen public behaviors are projections of the subsystem joint invariants once assignment/statement/call/builtin layers are cheat-free.
- Required for completion: yes
- Dependencies: C1, C2, C3, C4, C5
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C6

#### Progress note
Preserves public theorem names/equivalent strength while allowing internal helper statements to have changed.

#### Summary
Ensure `vyperTypeSoundnessNewScript.sml` exposes wrappers equivalent in strength to the six frozen public obligations. Prove/repair only wrapper projections; missing facts should be exported from subsystem layers, not reproved here.

#### Approach
Prove each wrapper by applying the relevant subsystem theorem and simplifying the result projection. Keep theorem names and strength equivalent to the task list. After wrappers, build the aggregator to ensure all dependencies are reachable and clean.

#### Not to try
Do not copy old retired proof scripts wholesale. Do not change frozen public behavior to match an easier internal theorem.

#### Argument
The final fresh surface has no new semantic induction. Statement and expression no-TypeError wrappers project the `no_type_error_result` conjuncts. Success preservation wrappers project state/env/accounts/result typing from statement/expression joint soundness. Exception preservation projects the return-exception typing and state invariants. Callable-body no-TypeError composes call-entry/function-body soundness with statement soundness.

#### Definition design
The public interface should hide strengthened internal side conditions by deriving them from public well-typedness/context hypotheses. If a public wrapper cannot be proved, that indicates a missing subsystem corollary or an underspecified public hypothesis; because public behavior is frozen, add/export the missing internal corollary rather than weakening public behavior.

#### Code structure
Wrapper edits belong only in `semantics/prop/vyperTypeSoundnessNewScript.sml` and, if absolutely necessary, small projection corollaries in subsystem files. Do not import retired old soundness theories unless C0 proves they are still in the fresh dependency chain.

### C6.1: Prove/repair the six public wrapper theorems
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: Wrapper projection is standard after subsystem theorems are complete; any failure is evidence of a missing projection lemma, not new architecture.
- Dependencies: C5.3, C2.3, C1.6
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C6.1

#### Progress note
Same public wrapper obligation as pre-collapse plan.

#### Summary
Close wrappers equivalent to `typed_stmts_no_type_error`, `typed_stmts_success_preserves_state_env`, `typed_stmts_exception_preserves_state_and_return_type`, `typed_expr_no_type_error`, `typed_expr_success_preserves_type`, and `typed_callable_body_no_type_error`.

#### Statement
Current-source public wrapper theorems in `semantics/prop/vyperTypeSoundnessNewScript.sml`, equivalent in strength to the six names listed in the TASK file.

#### Approach
For each wrapper, instantiate the strongest available subsystem theorem and destruct only the final conjunction/case result needed. If the subsystem theorem statement changed, add a compatibility corollary with the public wrapper name/strength. Keep all public hypotheses derivable from the source typing/context assumptions.

#### Not to try
Do not weaken public theorem conclusions or add visible public preconditions without user approval; these behaviors are frozen by the TASK.

### C7: Final `vyperSemanticsHolTheory` zero-CHEAT validation
- Kind: `validation`
- Risk: 1
- Work priority: 70
- Work units: 2
- Rationale: Mechanical final build/audit; any remaining warning is concrete evidence for a small follow-up replan.
- Required for completion: yes
- Dependencies: C6.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C7

#### Progress note
Final validation component is carried forward unchanged in purpose.

#### Summary
Run `holbuild build vyperSemanticsHolTheory` and confirm success with zero CHEAT warnings reachable from the theory. If any warning remains, report the exact theorem/file and request a scoped replan rather than declaring completion.

#### Description
This is the task done-definition check. It must be performed after all proof components, because HOL can build through cheated theorems while still emitting warnings.

#### Statement
Command-level obligation: `holbuild build vyperSemanticsHolTheory` succeeds with zero reachable CHEAT warnings.

#### Approach
Use holbuild only. Capture the full warning summary and, if clean, close the task. If not clean, map each remaining warning to an existing component if possible; if it is uncovered, escalate PLAN_INCOMPLETE with the exact warning list.

#### Not to try
Do not ignore CHEAT warnings because the build exit code is zero. Do not clean unrelated warnings outside the dependency cone unless they are reachable from `vyperSemanticsHolTheory`.
