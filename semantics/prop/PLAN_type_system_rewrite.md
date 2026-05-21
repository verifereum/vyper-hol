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

### C2: Statement soundness stack
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Carry-forward ancestor wrapper only; this update does not change C2's scope or strategy. The new executable work below is decomposed into risk-2 helper/patch leaves.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2 plan context

#### Progress note
Included solely as an explicit parent for dotted replacement/merge validation; omitted siblings and prior C2 progress remain governed by the existing PLAN.

#### Summary
Carry-forward parent context for statement soundness work. This review changes only the For-cons ordinary-exception proof-shape leaf below. No sibling obligations are reclassified or invalidated.

### C2.0: Evaluator statement soundness mutual proof repairs
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Carry-forward ancestor wrapper only; the local For-cons repair does not alter the evaluator invariant or sibling case strategy.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.0 plan context

#### Progress note
Included only as an explicit dotted parent. Existing omitted descendants remain in the PLAN.

#### Summary
Carry-forward parent for evaluator statement soundness. The only changed descendant is the For-cons ordinary-exception endpoint repair.

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

### C2.0.2: For-loop statement cases
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Carry-forward ancestor wrapper only; E0571 concerns a local proof boundary in the For-cons case, not the overall for-loop semantics argument.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.0.2 plan context

#### Progress note
Included only as an explicit dotted parent. Existing omitted descendants remain in the PLAN.

#### Summary
Carry-forward parent for for-loop statement cases. The repair below preserves the current invariant and changes only how one ordinary-exception endpoint consumes the body IH.

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
- Rationale: The mathematical obligation is still just specialization of the existing body IH plus previously proved pop/return-exception helpers. E0552 showed a proof-interface/tactic brittleness, not a counterexample: the failed goal after body-IH specialization was exactly an implication from the specialized consequent to itself, and after stripping it exposed the four needed conjuncts as assumptions. The repaired subtree avoids whole-conjunction theorem acceptance and destructed existential reconstruction.
- Progress transition: `refinement`
- Carries progress/evidence from: C2.0.2.2.0, E0550
- Invalidates prior progress/evidence: C2.0.2.2.1@previous, E0552

#### Progress note
C2.0.2.2.0 cleanup remains useful and is carried forward. The previous C2.0.2.2.1 statement/approach is replaced because E0552 demonstrated the exact-endpoint interface was too brittle, but the mathematical content remains the same local For-cons exception suffix path.

#### Summary
This subtree repairs the For-cons exception suffix boundary without changing the core mutual statement theorem. The body IH already provides the full result for the concrete body evaluation; the proof must specialize that IH and build the requested conjunction with `rpt conj_tac`, not try to accept a whole conjunction theorem. The existential for the exception case must remain packaged as an assumption/conjunct; do not open it and reconstruct a witness. After the projection lemma builds, prove the suffix helper and only then patch the suspended For-cons tail in the core theorem.

#### Description
The prior plan correctly identified that the For-cons tail needs a boundary lemma before editing `eval_for_cons_type_sound_core`, but the proof interface encouraged exact theorem-object endpoint attempts. The new interface is intentionally mundane: clean up the failed theorem text, reprove the projection with subgoal-level conjunction construction, then use it in the suffix lemma. If the projection still reaches a goal where the four conjuncts are separate assumptions, the authorized closure is `rpt conj_tac >> first_assum ACCEPT_TAC`; whole-goal `ACCEPT_TAC`, explicit `ASSUME`/`LIST_CONJ`, and existential destruct/rebuild are forbidden.

#### Approach
Work in `semantics/prop/vyperTypeStmtSoundnessScript.sml` around the existing For-cons helper block. Keep `eval_for_cons_type_sound_core` unchanged until this subtree is complete. The proof shape is: specialize the body IH with `(stp, INR exn, st_body)`, discharge the four antecedent conjuncts from assumptions, strip the specialized consequent if necessary, then solve the final conjunction one conjunct at a time.

#### Not to try
Do not retry `first_assum ACCEPT_TAC` on the whole conjunction, explicit `ACCEPT_TAC (LIST_CONJ [ASSUME ...])`, `MATCH_MP` theorem-object construction, or opening the exception existential with `qexists_tac`. E0551/E0552 show those endpoints are brittle in this suspended/replayed proof context. Do not edit the core For-cons mutual proof before the projection and suffix helpers build.

#### Argument
For a pushed For-cons body state `stp`, the statement-soundness body IH has exactly the form needed for every body result: under env/state/account typing and the concrete `eval_stmts` equation, it returns state preservation, account preservation, no-TypeError, and a result-indexed postcondition. In the exceptional body case `res_body = INR exn`, the postcondition is definitionally the exception branch and therefore contains the packaged existence of an extended exception environment. The non-loop-exception suffix theorem then combines this body result with the facts supplied by the loop-wrapper decomposition: non-loop exceptions propagate as the outer result, while popped-state invariants are supplied by the pop/extension helper. Return exceptions additionally use the already proved weakening lemma that removes the local loop variable from `return_exception_typed`.

#### Definition design
No new definitions are required. The boundary interface is theorem-level: (1) the carried cleanup restores a parseable helper region; (2) a projection lemma exposes the body IH result for a concrete `INR exn`; (3) a suffix lemma consumes that projection and previously proved pop/return-exception helpers. Failure sign: if any proof requires choosing `env_exn` from the exception existential, the boundary is being used incorrectly; the suffix consumer should use the packaged exception branch or apply the existing return-exception weakening theorem only where it explicitly needs `return_exception_typed env ret_ty ...`.

#### Code structure
All work stays in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near lines 1475--1760 and the For-cons helper block near line 2758. Do not add a new theory or library file. Keep helper theorems local unless they are already non-local in source. The helper order should be: existing `for_cons_body_exception_typed_from_body_soundness` and return-exception helpers, repaired projection lemma, pop/env restoration helper, non-loop-exception suffix helper, then the later core patch component.

### C2.0.2.2.0: Clean up failed C2.0.2.2 helper edits
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This component was already completed in E0550 and is carried forward so C2.0.2.2.1 can continue to depend on a clean helper region. No new executor work is required here.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0550, C2.0.2.2.0@previous

#### Progress note
Completed cleanup remains valid after the local subtree replacement.

#### Summary
Carried-forward completed cleanup component. It exists to preserve the dependency edge for the repaired projection lemma. No action is required unless the executor finds the file still contains unparsable remnants from the failed proof attempts.

#### Approach
No work expected. If the source is not parseable at the helper block, overwrite the failed `for_cons_body_ih_exception_projection` proof as part of C2.0.2.2.1 rather than reopening this completed cleanup.

#### Not to try
Do not spend time on unrelated cleanup in this component.

### C2.0.2.2.1: Replace failed projection text with a conjunctive body-IH projection proof
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 2
- Rationale: The failed logs show the specialized body IH produces exactly the desired facts. The remaining issue is proof construction, so a subgoal-by-subgoal conjunction proof is standard and avoids the rejected whole-conjunction/ASSUME theorem endpoints.
- Dependencies: C2.0.2.2.0
- Checkpoint: yes
- Supersedes: C2.0.2.2.1@previous
- Progress transition: `replacement`
- Carries progress/evidence from: E0552
- Invalidates prior progress/evidence: C2.0.2.2.1@previous

#### Progress note
E0552 is carried as negative evidence: it rules out the old exact-endpoint approach and justifies this replacement. No completed proof progress from the old C2.0.2.2.1 is reused.

#### Summary
Overwrite the current partial `for_cons_body_ih_exception_projection` proof. Keep the same mathematical statement unless current source has already changed it to the full specialized body-IH consequent; either statement is acceptable only if the conclusion is solved by specializing the body IH and constructing conjuncts one by one. After the body IH is specialized and its antecedent discharged, use `strip_tac` followed by `rpt conj_tac >> first_assum ACCEPT_TAC` or equivalent per-conjunct assumption closure. The proof must not destruct the exception existential.

#### Description
The statement should match the theorem shown in the task/current source: from well-typed initial pushed body state, concrete `eval_stmts cx body stp = (INR exn, st_body)`, and the body IH, conclude `state_well_typed st_body /\ accounts_well_typed st_body.accounts /\ no_type_error_result (INR exn) /\ case (INR exn : unit + exception) of ...`. If the source currently has the full-specialized projection variant from E0552, it may be kept only if downstream C2.0.2.2.2 consumes it directly; otherwise restore the task statement. The crucial proof invariant is that the exception branch remains one assumption/conjunct containing `?env_exn...`. Do not simplify that branch in a way that introduces a free witness.

#### Statement
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
    state_well_typed st_body /\
    accounts_well_typed st_body.accounts /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + exception) of
     | INL u => env_consistent env_after cx st_body
     | INR exn0 =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn0)

#### Approach
Use a named specialization rather than `first_x_assum`: `qpat_x_assum` on the quantified body IH, `qspecl_then [stp, INR exn, st_body] mp_tac`, discharge its antecedent with the four assumptions, then strip the consequent. Close with per-conjunct tactics, e.g. `rpt conj_tac >> first_assum ACCEPT_TAC`; if the pretty-printed case annotation prevents exact matching, first use only `simp[sum_case_def]` on the goal/assumption without opening the existential witness. Verify with `holbuild build vyperTypeStmtSoundnessTheory`.

#### Not to try
Do not use `first_assum ACCEPT_TAC` on the entire conjunction: there is no whole-conjunction assumption after `strip_tac`. Do not build an explicit theorem with `ASSUME``...``/LIST_CONJ`; E0552 showed this fails validation in the replay context. Do not `gvs[sum_case_def]` so aggressively that it chooses an `env_exn` witness and leaves it free in hypotheses.

### C2.0.2.2.2: Prove full non-loop-exception suffix helper using the repaired projection
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Once C2.0.2.2.1 provides the body result for `INR exn`, this theorem is standard assembly from already available pushed-state/pop/env and return-exception helpers. No new semantic case analysis is needed.
- Dependencies: C2.0.2.2.1
- Checkpoint: yes
- Supersedes: C2.0.2.2.2@previous
- Progress transition: `refinement`
- Carries progress/evidence from: C2.0.2.2.2@previous

#### Progress note
The obligation remains the previous suffix-helper obligation, but its dependency is now the repaired conjunctive projection lemma rather than the brittle exact-endpoint projection interface.

#### Summary
Prove the For-cons non-loop-exception suffix lemma after the projection builds. Use decomposition facts to show the outer result is the same non-loop exception and use existing assumptions/helpers for popped state/account/env consistency. For `ReturnException`, use the existing return-exception weakening helper from the body’s extended environment to the original environment. This component should not re-run body evaluator induction or duplicate statement cases.

#### Description
The suffix lemma should be the consumer needed by the later `ReturnException_tail`/non-loop exceptional branch in the For-cons case. It should take the concrete pushed body evaluation, body IH, and any already-established popped-state/env assumptions, then conclude the outer statement postcondition after `pop_scope`. The exact theorem name may follow the source (`for_cons_non_loop_exception_suffix` or the currently planned helper), but it must expose the result expected by the core patch component rather than requiring the core proof to destruct the body IH itself.

#### Statement
Use the current source/planned statement for the For-cons non-loop-exception suffix helper. It must cover the case where the body returns `INR exn` with `exn <> ContinueException` and `exn <> BreakException`, and conclude the required outer postcondition after popping the For-cons local scope: preserved state/accounts, no TypeError for the outer `INR exn`, env consistency for the popped state where required, and `return_exception_typed env ret_ty exn` for propagated return exceptions.

#### Approach
First invoke `for_cons_body_ih_exception_projection` to obtain the packaged body facts. Use existing `for_body_env_extends_consistent_after_pop` or the local pop/env helper for `env_consistent env cx (st_body with scopes := TL st_body.scopes)`. For the return-typing part, split only on the exception constructor if needed: `ContinueException` and `BreakException` are excluded by hypotheses; `ReturnException v` is handled by `for_cons_body_ih_return_exception_typed` or `for_cons_return_exception_typed_from_body_ex` as appropriate; other exceptions should match the required non-return exception typing condition in the current statement.

#### Not to try
Do not inline `eval_stmts`/`finally`/`handle_loop_exception` again in this component; decomposition lemmas already isolated that. Do not specialize the body IH independently in the core proof after this helper exists. Do not open the projection’s existential except at a point where an existing theorem immediately consumes the packaged exception typing evidence.

### C2.0.2.3: For-cons case
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Carry-forward ancestor wrapper only; the For-cons decomposition remains valid and the new work is localized to the non-loop exception endpoint.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.0.2.3 plan context, E0570, E0571

#### Progress note
Included only as an explicit dotted parent. The current update replaces the failed endpoint proof shape under C2.0.2.3.2.1.

#### Summary
Carry-forward parent for the For-cons proof. The semantic decomposition of pushed scope, body evaluation, loop result, and popped scope remains unchanged.

### C2.0.2.3.1: Prove/fix the projected non-loop exception suffix helper
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: The statement is a direct conjunction assembly from its premises plus one already-used return-exception weakening lemma. E0558’s helper failure was caused by proof-script ordering after simplifying the `case INR exn`, not by missing semantics.
- Dependencies: C2.0.2.2.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0558

#### Progress note
This refines the failed projected-helper attempt from E0558. The statement may keep the current name `for_cons_non_loop_exception_suffix_projected`, but its proof must avoid the incorrect fixed sequence of `conj_tac` assumptions after `simp[sum_case_def]`.

#### Summary
Repair the local helper `for_cons_non_loop_exception_suffix_projected` or replace it with an equivalently caller-shaped theorem. It should take popped-state facts, `no_type_error_result (INR exn)`, and the actual existential exceptional case fact from the body IH. It should conclude the non-loop suffix facts under the original `env`. This helper must build before touching the core theorem again.

#### Statement
Preferred shape, matching the current source if possible:
```sml
Theorem for_cons_non_loop_exception_suffix_projected:
  !env cx id ty ret_ty st_body exn.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + exception) of
     | INL u => T
     | INR exn0 =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn0) ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
```
If simplifying the premise statement to an explicit `?env_exn...` makes the proof cleaner, also provide a compatibility theorem under the current name for the core call site.

#### Approach
Start with `rpt strip_tac` and simplify the `case INR exn` premise/conclusion using `sum_case_def`; avoid assuming the conjunction order after simplification. Split the final conjunction only after simplification reveals the exact goals, solve the first four conjuncts from assumptions, then destruct the existential and apply `return_exception_typed_extend_local_env_extends` with witnesses `F`, `env_exn`, `id`, and `ty`. If HOL’s `conj_tac` validation is brittle, prove an explicit existential-form helper first and make this theorem a one-line corollary by `fs[sum_case_def]`.

#### Not to try
Do not use a hard-coded sequence of four `conj_tac >- first_assum ACCEPT_TAC` immediately after `simp[sum_case_def]`; E0558 showed the goal order was not what that script assumed. Do not mention or require the universal body IH in this helper.

### C2.0.2.3.2: For-cons non-loop exception branch
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Carry-forward parent plus local strategy context. E0571 shows the non-loop exception branch needs a stronger proof boundary, but not a different semantic invariant.
- Progress transition: `refinement`
- Carries progress/evidence from: E0570, E0571
- Invalidates prior progress/evidence: local endpoint tactics that consume CHOOSE-origin existential/case premises inside eval_for_cons_type_sound_core

#### Progress note
The prior projected-helper progress is retained as diagnostic evidence. The revised child component moves existential/case consumption into a standalone helper.

#### Summary
Refines the For-cons non-loop exception proof strategy. Keep the existing decomposition and popped-scope facts, but do not consume the body-IH existential case inside `eval_for_cons_type_sound_core`. The child helper supplies a non-existential return-typing conclusion for the endpoint.

#### Description
This ancestor records the strategic rebase from local existential consumption to helper-based return typing. It preserves all state/account/env popped-scope reasoning already present in the core proof.

#### Approach
Use the new helper to isolate return exception typing. The endpoint should split easy final conjuncts using already visible facts and call the helper only for the `return_exception_typed env ret_ty y` conjunct.

#### Not to try
Do not retry direct acceptance, `simp`, `metis`, or `MATCH_MP` over the concrete `case (INR y)` existential in the endpoint. E0571 already shows these are validation-sensitive in this context.

#### Argument
In the ordinary non-loop exception branch, the loop body has evaluated as `eval_stmts cx body stp = (INR y, st_body)` and the loop result is propagated as `INR y`. The body IH already implies, for this concrete evaluation, an extended exception environment carrying `return_exception_typed env_exn ret_ty y`. The only mathematically necessary step is to transport this return typing back through the loop-local `extend_local env id ty F`. E0571 shows this is not safe to do by local CHOOSE-witness destruction in the suspended endpoint, so the branch must use a boundary lemma whose conclusion has no existential witness.

#### Definition design
No definition changes in this subtree. The proof interface should expose a helper from the universal body IH plus concrete evaluation/pushed-state premises directly to `return_exception_typed env ret_ty y`. Any remaining endpoint goal mentioning `?env_exn`, `case (INR y)`, or a local witness `env_exn` means the abstraction boundary is still too weak.

#### Code structure
Work only in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Put the helper in the existing For-cons helper section before `eval_for_cons_type_sound_core`; patch only the final ordinary-exception endpoint of that theorem. Do not edit assignment, builtin, call, or public wrapper theories for this local repair.

### C2.0.2.3.2.1: Rebase the For-cons ordinary-exception endpoint onto a body-IH boundary helper
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The evidence shows a local proof-shape/validation problem, not a false invariant. A standalone helper can specialize the body IH and consume the existential/case branch outside the problematic endpoint; the endpoint then passes the original universal IH and concrete evaluation facts without destructing any existential locally.
- Supersedes: C2.0.2.3.2.1@E0570-projected-endpoint, C2.0.2.3.2.1@E0571-stuck-endpoint
- Progress transition: `replacement`
- Carries progress/evidence from: E0571, TO_type_system_rewrite-20260521T121230Z_m35217_t002, TO_type_system_rewrite-20260521T121230Z_m35230_t001, TO_type_system_rewrite-20260521T121230Z_m35255_t001, TO_type_system_rewrite-20260521T121230Z_m35270_t001
- Invalidates prior progress/evidence: projected-helper endpoint tactic variants that destruct/accept the concrete case premise inside eval_for_cons_type_sound_core

#### Progress note
Prior progress is kept only as negative evidence: it proved that the universal-IH transport and projected concrete-case endpoint are validation-sensitive in this context. The current component replaces the tactic shape rather than continuing the same local acceptance attempts.

#### Summary
- Replace the stuck projected-helper endpoint with a small boundary helper proved before `eval_for_cons_type_sound_core`.
- The helper specializes the body statement IH at `(stp, INR y, st_body)` and derives `return_exception_typed env ret_ty y` outside the problematic endpoint.
- The endpoint must not destruct the existential/case premise locally; it should pass the universal IH and concrete pushed/eval facts to the helper.
- Completion for this leaf means `holbuild build vyperTypeStmtSoundnessTheory` advances past `eval_for_cons_type_sound_core`; a later failure in the `Resume For_cons` body is downstream evidence, not a failure of this leaf.

#### Description
This component replaces the previous endpoint tactic plan. The old plan successfully identified the right semantic fact but left the proof with a local existential/case premise whose witness could not be used in the instrumented/suspended context. The replacement pushes that existential reasoning into a standalone theorem, so the core proof no longer relies on accepting alpha-equivalent case premises or CHOOSE-derived assumptions.

#### Approach
First add the standalone boundary helper and prove it by specializing the body IH at `stp`, `INR y`, and `st_body`; use `for_cons_ordinary_exception_return_typed_from_case_premise` to convert the resulting case premise into `return_exception_typed env ret_ty y`. Then, in the final ordinary-exception branch of `eval_for_cons_type_sound_core`, after reducing the result equality to the return-typed obligation, invoke this helper with the visible universal body IH, `env_consistent (extend_local env id ty F) cx stp`, `state_well_typed stp`, `accounts_well_typed stp.accounts`, and `eval_stmts cx body stp = (INR y, st_body)`.

#### Not to try
Do not retry `strip_assume_tac`/`qexists env_exn`/`ACCEPT_TAC` on the concrete existential or its conjuncts inside `eval_for_cons_type_sound_core`; E0571 shows even the final `return_exception_typed env_exn ret_ty y` assumption fails CHOOSE validation. Do not return to the universal body-IH transport lemmas that leave an alpha-equivalent implication/case premise to prove in the endpoint. Do not use broad `gvs[sum_case_def]` over the large endpoint context.

#### Argument
The ordinary non-loop exception branch of `eval_for` has already decomposed the loop body to `eval_stmts cx body stp = (INR y, st_body)` and has the body induction hypothesis in the standard joint form. Semantically, the needed return typing is immediate: specialize the body IH at the pushed state `stp`; its `INR` branch provides an extended environment `env_exn` consistent with `st_body` and `return_exception_typed env_exn ret_ty y`; then transport return typing back through the loop-local `extend_local env id ty F` using the already-proved `return_exception_typed_extend_local_env_extends`/`for_cons_ordinary_exception_return_typed_from_case_premise` boundary. The failed attempts show that doing this existential/case consumption inside the endpoint causes CHOOSE validation failures, so the existential must be consumed inside a standalone helper theorem whose conclusion is the non-existential fact `return_exception_typed env ret_ty y`. The endpoint then only instantiates this helper with visible facts and no longer creates goals containing the CHOOSE witness.

#### Definition design
No definition changes are authorized in this subtree. The proof interface to add is a boundary lemma, not a new invariant: it should take the body IH in exactly the same joint form used by `eval_for_cons_type_sound_core`, plus pushed-state consistency/typing and the concrete body evaluation equation, and return only `return_exception_typed env ret_ty y`. Failure signs: if the endpoint still has a goal that is a `case (INR y)` premise, an existential over `env_exn`, or a goal mentioning the witness `env_exn`, the helper boundary is too weak or has been applied too late.

#### Code structure
Work only in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Place the new helper near the existing For-cons helper block, before `eval_for_cons_type_sound_core`, alongside `for_cons_ordinary_exception_return_typed_from_case_premise` and `for_cons_non_loop_exception_suffix_projected`. Then edit only the ordinary non-loop exception endpoint of `eval_for_cons_type_sound_core` to use this helper. Do not modify assignment, builtin, call, or public wrapper theories for this local repair.

### C2.0.2.3.2.1.1: Add the non-existential body-IH return-typing helper for For-cons ordinary exceptions
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: The helper proof is a standard specialization of the existing body IH followed by an already-proved environment-extension return-typing transport. It is low risk because the failed evidence was endpoint validation, not the underlying fact; the same existential-to-return transport already exists as standalone lemmas.
- Checkpoint: yes
- Carries progress/evidence from: E0571

#### Progress note
This helper is the new boundary introduced in response to the E0571 risk mismatch. E0571 supports its necessity by showing that the existential/case premise must not be consumed in the endpoint.

#### Summary
- Add a theorem before `eval_for_cons_type_sound_core` that specializes the body IH for the concrete `INR y` body result.
- The theorem conclusion should be exactly `return_exception_typed env ret_ty y`, with no existential witness in the conclusion.
- Prove it outside the endpoint using existing For-cons return-typing transport lemmas.
- This is a checkpoint because failure would mean the proposed boundary is still not strong enough or not syntactically aligned with the body IH.

#### Statement
Suggested theorem shape:
```sml
Theorem for_cons_ordinary_exception_return_typed_from_body_ih:
  !env env_after cx id ty ret_ty body stp st_body y.
    env_consistent (extend_local env id ty F) cx stp /\
    state_well_typed stp /\
    accounts_well_typed stp.accounts /\
    eval_stmts cx body stp = (INR y, st_body) /\
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
    return_exception_typed env ret_ty y
```
If the exact variable names in the surrounding file differ, keep the body-IH premise syntactically aligned with `eval_for_cons_type_sound_core` rather than preserving these names.

#### Approach
Specialize the universal body IH with `stp`, `INR y`, and `st_body`; discharge its antecedent from the first four premises. From the specialized conclusion, extract the `case (INR y)` branch in this standalone theorem and apply `for_cons_ordinary_exception_return_typed_from_case_premise` (or directly `return_exception_typed_extend_local_env_extends`) to eliminate the extension witness. Keep simplification local to `sum_case_def`; avoid proving any popped-state suffix here.

#### Not to try
Do not make the helper conclude the whole final suffix unless needed; the endpoint already has popped state/account/env facts and no-type-error. Do not include a free `env_exn` parameter or any existential in the conclusion. Do not phrase the premise as a separate alpha-renamed implication that will require transport at the endpoint; copy the body-IH shape from `eval_for_cons_type_sound_core`.

### C2.0.2.3.2.1.2: Patch `eval_for_cons_type_sound_core` to call the body-IH helper at the ordinary-exception endpoint
- Kind: `proof_patch`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: After the helper exists, the core endpoint should only instantiate a theorem with visible concrete facts. This avoids all previously failing CHOOSE-origin existential/case assumption acceptance.
- Dependencies: C2.0.2.3.2.1.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0570, E0571
- Invalidates prior progress/evidence: the local `for_cons_non_loop_exception_suffix_projected` endpoint proof attempts that still leave the concrete case premise

#### Progress note
This keeps the semantic endpoint from the prior component but changes the proof boundary. The prior projected-helper work remains useful only for locating the exact ordinary-exception endpoint and ruling out local case-premise consumption.

#### Summary
- Edit the final non-Continue/non-Break `INR y` branch of `eval_for_cons_type_sound_core`.
- Remove local destruction or acceptance of the body-IH `case (INR y)` existential premise.
- After establishing `res = INR y` and `st' = st_body with scopes := TL st_body.scopes`, use the new helper to prove the remaining return-typed fact.
- Verify with `holbuild build vyperTypeStmtSoundnessTheory`; success for this leaf is advancing past `eval_for_cons_type_sound_core`, even if a later `Resume For_cons` failure appears.

#### Statement
Patch target: the ordinary non-loop exception endpoint in
```sml
Theorem eval_for_cons_type_sound_core: ...
```
The theorem statement itself should not change.

#### Approach
At the endpoint, keep the already-proved facts: pushed `env_consistent`, pushed `state_well_typed`, pushed `accounts_well_typed`, concrete `eval_stmts cx body stp = (INR y, st_body)`, and the universal body IH. When the goal has reduced to `return_exception_typed env ret_ty y` (or the final suffix whose only nontrivial conjunct is that fact), `irule`/`match_mp_tac` the new helper and discharge premises by explicit `qexists_tac` plus `first_assum ACCEPT_TAC`/small `simp[]` only on non-existential facts. If the full suffix is still present, split the easy state/account/env/no-type-error conjuncts first, then call the helper for the return-typed conjunct.

#### Not to try
Do not call `for_cons_non_loop_exception_suffix_projected` here if it leaves the concrete case premise as a subgoal. Do not select, simplify, destruct, or accept a local assumption of shape `case (INR y) of ... ?env_exn ...`. Do not introduce a local witness `env_exn` in this theorem. If the new helper application still leaves a premise with a `case` or `?env_exn`, stop and escalate because the helper was not strong enough.

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
