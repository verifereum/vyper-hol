# PLAN

## Structured Components

### C0: Carry forward baseline build/CHEAT audit
- Kind: `source_audit`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already completed mechanical audit evidence remains valid and is not part of the remaining proof frontier.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0, E0530

#### Progress note
C0 is preserved as completed baseline evidence. It does not authorize stale scheduling; the remaining frontier is rebased below.

#### Summary
- Completed current-source baseline build/CHEAT audit is carried forward.
- No executor proof work remains in this component.
- Use it only as source-status context; final validation is C7.

#### Description
This component records the already-closed initial status check. The task completion criterion is still C7, not C0.

#### Statement
Build/audit baseline for the fresh stack reachable from `vyperSemanticsHolTheory`.

#### Approach
No work remains. Do not rerun unless later source changes make final validation fail and a new audit is needed.

#### Not to try
Do not treat old retired-theory cheats found during broad greps as task obligations unless C7 shows they are reachable from `vyperSemanticsHolTheory`.

### C1: Carry forward completed assignment-target state preservation and joint soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: Completed assignment-target branches and compatibility wrappers are preserved from accepted build-through evidence; no remaining C1 leaf is executable.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `carry_forward`
- Carries progress/evidence from: C1, C1.1, C1.2, C1.3, C1.4, C1.5, C1.6, E0531, E0532, E0533, E0534, E0535, E0536

#### Progress note
The assignment-target work that the TASK identified as handover-sensitive is preserved as done. The inherited update-binop CHEAT path is not part of this carry-forward; it is now owned by C3.

#### Summary
- Assignment-target state preservation and joint soundness branches are carried forward as complete.
- This includes the TopLevelVar HashMapRef/ArrayRef, ImmutableVar, TupleTargetV, assign_targets_cons, and compatibility wrapper work.
- Remaining assignment-related CHEAT warnings in the update-binop/subscript helper chain are scheduled separately under C3.
- Downstream statement proofs may use the strengthened assignment interfaces; they must not weaken them.

#### Description
No executor work remains here. If a downstream proof exposes that a completed assignment theorem still depends on a CHEAT in the update-binop path, route that work to C3 rather than reopening C1.

#### Statement
Current source-authoritative assignment-target mutual theorem and wrappers, including `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error`, remain available without weakening their strengthened assumptions.

#### Approach
Carry forward the existing proofs. Downstream components should use `drule`/`irule` against the strengthened wrappers, supplying shape and assignability side conditions from statement typing or target-runtime facts.

#### Not to try
Do not weaken `assign_target_sound_mutual` or drop `assign_target_assignable_context`. Do not inline top-level storage/hashmap/array assignment semantics in C2 statement cases.

#### Argument
The completed assignment-target theorem follows the assignment evaluator recursion and proves a joint all-result invariant: no TypeError, preservation of runtime consistency/state/accounts as appropriate, and target/value typing preservation. The strengthened side conditions `assign_operation_matches_target_shape` and `assign_target_assignable_context` remain part of the interface. Top-level storage/hashmap/array cases are discharged by branch helpers matching the semantic storage branches, while target-list cases follow the recursive `assign_targets` structure.

#### Definition design
The proof interface exported to downstream statement soundness is the strengthened assignment boundary: target runtime typing, operation runtime typing, shape matching, and assignable-context assumptions imply no TypeError and preservation. Failure signs for later consumers are attempts to unfold `assign_target_def` in statement/call proofs or to remove the strengthened side conditions. The inherited update-binop lemmas are not covered by this component and must be closed by C3 before final zero-CHEAT validation.

#### Code structure
Keep assignment target semantic proofs in `semantics/prop/vyperTypeStatePreservationScript.sml` and compatibility wrappers in `semantics/prop/vyperTypeAssignSoundnessScript.sml`. Statement proofs in `vyperTypeStmtSoundnessScript.sml` should consume these theorems, not duplicate assignment evaluator case analysis.

### C2: Verified theorem falsehood
- Kind: `unprovability_gate`
- Risk: 5
- Work priority: 0
- Work units: 0
- Rationale: Suspected theorem falsehood: complete probe components under C2 (including C2.4.1.b) before any other proof work. If probes confirm a counterexample, stop/report unprovable; do not silently repair the theorem.
- Required for completion: yes
- Checkpoint: yes

### C2.0: Carry forward completed statement-assignment and structural expression work
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Accepted evidence already proves the prior statement-assignment repairs and structural expression cases; retaining them as a single carry-forward leaf avoids stale over-decomposition.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.0, C2.1, C2.1.0, C2.1.1, C2.1.1.*, E0616, E0665, E0666, E0670, E0671, E0672, E0678, E0680, E0685, E0708

#### Progress note
Fine-grained completed C2.1 descendants are intentionally collapsed here. Their proof progress still counts; no executor work remains.

#### Summary
- Carries forward completed AnnAssign/Assign/AugAssign side-condition work and structural expression cases.
- Includes prior Subscript, IfExp, StructLit, FlagMember, TopLevelName/BareGlobalName, iterator, and related proof-order repairs.
- No work remains in this component.
- Later C2 leaves may depend on it as the mutual-proof prefix context.

#### Statement
Already-proved source regions of `eval_all_type_sound_mutual` before the remaining builtin/type-builtin/call resumes.

#### Approach
No proof action. If a build regression appears in these regions, escalate with exact failing theorem rather than reopening this collapsed component.

#### Not to try
Do not reintroduce the old fine-grained components or rely on their stale scheduling metadata.

### C2.2: Carry forward completed Expr_Attribute soundness
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: Expr_Attribute helper and integration evidence is complete and remains valid under the rebase.
- Dependencies: C2.0
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.2, C2.2.1, C2.2.2, C2.2.3, E0709, E0710, E0711

#### Progress note
The completed attribute boundary lemmas and resume integration are preserved without re-execution.

#### Summary
- Carries forward completed `Expr_Attribute` proof.
- The attribute evaluation boundary remains available as pattern evidence.
- No executor work remains.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Attribute]` is already proved in current source.

#### Approach
No action required. Later expression branches should imitate the boundary-helper pattern rather than inline semantic case splits.

#### Not to try
Do not unfold attribute evaluation again unless current source has regressed.

### C2.3: Carry forward completed Expr_Pop repair and soundness proof
- Kind: `carried_evidence`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The dynamic-array/assignability Pop typing repair and proof integration are completed and must be preserved as stable progress. It may still transitively depend on C3 cheats for final warning elimination, but the Pop source proof itself is done.
- Dependencies: C2.0, C1
- Supersedes: old Pop unprovability gate
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.3, C2.3.1, C2.3.2, C2.3.3, C2.3.4, C2.3.5, C2.3.6, E0719, E0720, E0721, E0722, E0727, E0729

#### Progress note
Completed Pop work is preserved. The old fixed-array Pop counterexample is superseded by the current source-authoritative dynamic-array and assignability typing repair.

#### Summary
- Carries forward the repaired `Expr_Pop` typing rule and proof.
- The source now requires dynamic-array Pop and assignment assignability, resolving the earlier false fixed-array path.
- No executor proof work remains in Pop.
- Any remaining CHEAT warning in assignment/update helpers belongs to C3, not this component.

#### Description
This component preserves the handover-sensitive Pop repair while acknowledging that final zero-CHEAT validation still requires closing the inherited update-binop path under C3.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Pop]` and its helper lemmas are already proved in current source.

#### Approach
No work remains. Downstream proofs may use the strong Pop extraction and assignment success typing lemmas introduced by this repair.

#### Not to try
Do not weaken Pop back to allowing fixed arrays. Do not reopen the earlier counterexample unless source reverts the dynamic-array/assignability preconditions.

### C2.4: Close `Expr_Builtin` statement-soundness case after local prefix cleanup
- Kind: `proof_group`
- Risk: 5
- Work priority: 40
- Work units: 0
- Rationale: Risk is inherited from the new C2.4.1 unprovability gate. The existing source cleanup C2.4.0 remains done; the Len proof component must be redesigned before the main resume can close.
- Progress transition: `refinement`
- Carries progress/evidence from: C2.4, E0791

#### Progress note
Parent context refined to replace the failed C2.4.1 proof with a gate while preserving C2.4.0 and any omitted descendants.

#### Summary
`Expr_Builtin` is blocked specifically in the Len subcase. The success path has evidence that `Len_builtin_sound` can type the returned integer. The unresolved path is whether `toplevel_array_length` can raise a TypeError for a well-typed Len argument, especially materialized fixed arrays. Resolve that with probes before continuing the non-Len branch.

#### Description
This group contains the local cleanup and the `Expr_Builtin` proof/gate. Only C2.4.1 is being replaced; C2.4.0 remains a completed prerequisite.

#### Argument
The `Expr_Builtin` proof should split first on `bt = Len`. For Len, `well_typed_builtin_app_def` gives one argument and result type `BaseT (UintT 256)`. The generated expression IH supplies no-TypeError/preservation/typing for the argument. The successful `toplevel_array_length` path is discharged by `Len_builtin_sound`; the exception path requires a boundary proving it is not a TypeError under the actual runtime-shape assumptions. The non-Len branch should later use normal `eval_exprs` and `evaluate_builtin` boundaries, but it must not distract from the possible Len counterexample.

#### Definition design
The Len boundary cannot be 'all typed sized values are accepted': fixed `SArrayV` values are typed and sized but rejected by `toplevel_array_length_def`. A correct boundary must mention the actual expression-evaluation invariant, an explicit runtime-shape predicate, or a repaired length semantics. The diagnostic probes below are mandatory before designing the final boundary.

#### Code structure
Place C2.4.1 probes locally in `vyperTypeStmtSoundnessScript.sml` near the blocked resume. Keep `FAIL_TAC` only as a temporary marker during the gate; final proof work must remove it. Do not edit unrelated builtin/call obligations while this gate is open.

### C2.4.0: Finish local prefix type-namespace/source annotations in `vyperTypeStmtSoundnessScript.sml`
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: The remaining failure is a mechanical HOL type-resolution issue, not a theorem-design or proof-strategy issue: `eval_stmts cx` requires a `stmt list`, while the free name `body` has been inferred/resolved as an unrelated word64 function type. The prior evidence already shows the explicit `+ exception` ambiguity is gone and the build advanced to this next local annotation problem.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C2.4.0, E0790, TO_type_system_rewrite-20260522T073012Z_m42546_t001, TO_type_system_rewrite-20260522T073012Z_m42548_t001, TO_type_system_rewrite-20260522T073012Z_m42549_t001, TO_type_system_rewrite-20260522T073012Z_m42549_t003

#### Progress note
E0790 is accepted as partial progress: grep found no remaining textual `+ exception` in the file, and holbuild passed the original `vfmExecution$exception`/`vyperState$exception` unification blocker. The component is refined, not closed, because the same prefix still fails to type-check at a local ambiguous `body` variable before downstream components can run.

#### Summary
- Keep the completed `exception` qualification edits from E0790.
- Repair the newly exposed local HOL source type ambiguity around `for_cons_body_exception_typed_from_body_soundness`.
- Make every theorem/proof occurrence that uses `eval_stmts cx body` force `body : stmt list`, preferably by annotating the theorem statement binder/use site rather than by large proof rewrites.
- Re-run `holbuild build vyperTypeStmtSoundnessTheory` and stop this component only when the build advances past these prefix/source type errors to the next real proof obligation or completes.

#### Description
This component remains a local source-cleanup gate for the statement soundness prefix. The explicit exception namespace cleanup is complete, but the theory still does not type-check because HOL resolves the free identifier `body` in a helper theorem as an unrelated word64-valued function instead of a statement list. Fix only the local annotation/name-resolution issue needed to let the source prefix elaborate. If similar adjacent helper theorems in the same for-cons block use `eval_stmts cx body`, annotate them consistently when holbuild exposes the same issue.

#### Statement
Target build check for this cleanup gate:

```sh
holbuild build vyperTypeStmtSoundnessTheory
```

must advance past the local prefix type-analysis failures caused by unqualified exception sums and ambiguous `body` variables in the for-cons helper block of `semantics/prop/vyperTypeStmtSoundnessScript.sml`.

#### Approach
At the failing helper theorem(s), force the intended type of the free variable by annotating the statement occurrence, e.g. use `(body : stmt list)` in `eval_stmts cx (body : stmt list) stp = ...`, or rename the variable to a fresh name such as `body_stmts` with a type annotation if that is cleaner. Apply the same small annotation to proof patterns (`qpat_x_assum`/quoted terms) only if they stop matching after the statement edit. Then rebuild the theory to confirm the source elaborator reaches the next obligation.

#### Not to try
Do not revisit or undo the completed `vyperState$exception` qualifications; the build evidence shows that blocker is past. Do not attempt semantic strengthening, evaluator induction changes, or statement-soundness proof repair under this component. Do not use broad rewrites or imports to influence name resolution; this should be fixed by local theorem statement/binder annotation or renaming.

### C2.4.1: Repair fixed-array `Len` runtime semantics and finish `Expr_Builtin` Len soundness
- Kind: `repair_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: All remaining obligations are now localized and low-risk: C2.4.1.1 has already repaired the definition; the newly exposed builtin proof failure is discharged by the existing `sparse_has_type_length` theorem plus elementary arithmetic; stale probe cleanup and Len boundary use those repaired facts.
- Progress transition: `refinement`
- Carries progress/evidence from: C2.4.1, E0797, E0798
- Invalidates prior progress/evidence: old C2.4.1.2 scheduling

#### Progress note
E0798 is accepted as a plan-incomplete/stuck episode for the old cleanup leaf. It does not invalidate the repaired definition from E0797; it reorders the subtree so the newly exposed builtin theorem is repaired before cleanup or statement-level Len boundary work.

#### Summary
- Complete the Len fixed-array repair path after adding `SArrayV` support to `toplevel_array_length`.
- First repair the builtin theorem `Len_result_fits_uint256`, whose old proof assumed materialized static arrays could not return a length.
- Then remove or rewrite stale counterexample probes that asserted the former TypeError behavior.
- Finally prove the Len typed no-TypeError boundary and use it to close the `Expr_Builtin` Len branch.

#### Argument
The semantic repair makes `toplevel_array_length cx (Value (ArrayV (SArrayV sparse)))` succeed with `LENGTH sparse`. Therefore every typed Len proof must account for materialized static arrays, not contradict them. For fixed arrays, typing provides `SORTED $< (MAP FST sparse)` and `sparse_has_type tv len sparse`; the existing `sparse_has_type_length` theorem gives `LENGTH sparse <= len`. Well-formed fixed array typing provides the storage bound `len * type_slot_size tv < 2**256` and the slot-size positivity already materialized in the failing goal. Hence `LENGTH sparse < 2**256` follows by `LENGTH sparse <= len <= len * slot < bound`. This restores `Len_result_fits_uint256`, which feeds `Len_builtin_sound`, which in turn supports the statement-level Len success/no-TypeError boundary.

#### Definition design
The public definition interface after C2.4.1.1 is: `toplevel_array_length` returns the runtime length for every runtime array-like value, including `Value (ArrayV (SArrayV sparse))`, and only raises TypeError for non-array-like values. Consumers must not rely on static arrays raising TypeError. Boundary facts in this subtree should hide `toplevel_array_length_def` from statement soundness: builtin soundness proves the uint256 bound and success typing; statement soundness consumes a typed Len no-TypeError lemma. Failure signs: any theorem/probe claiming a well-typed fixed `SArrayV` Len can return `TypeError "toplevel_array_length"` is stale and must be deleted or rewritten as a regression success check.

#### Code structure
Make the builtin proof repair in `semantics/prop/vyperTypeBuiltinsScript.sml` near `Len_result_fits_uint256`; do not move this arithmetic into statement soundness. Use the exported typing lemma `sparse_has_type_length` from `vyperTypingScript.sml` if visible; if not visible, add the minimal import/open dependency rather than reproving a local copy. Keep stale-probe cleanup in `semantics/prop/vyperTypeStmtSoundnessScript.sml` after the builtin theory builds, because `vyperTypeStmtSoundnessTheory` depends on `vyperTypeBuiltinsTheory`. The final `Expr_Builtin` resume should use repaired boundary lemmas rather than unfolding `toplevel_array_length_def` repeatedly.

### C2.4.1.1: Add `toplevel_array_length` support for materialized static arrays
- Kind: `definition_repair`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already proved in E0797. The definition now returns `LENGTH sparse` for `Value (ArrayV (SArrayV sparse))`, matching intended array-like Len behavior.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0797, C2.4.1.1

#### Progress note
Carry forward the closed proof episode that edited `semantics/vyperStateScript.sml` and verified the definition repair far enough to expose the downstream builtin proof failure.

#### Summary
- Keep the completed `toplevel_array_length` definition repair.
- This is the prerequisite for all subsequent Len fixed-array soundness work.
- No further executor work is requested for this leaf unless later builds show the committed edit was lost.

### C2.4.1.2: Repair `Len_result_fits_uint256` for materialized static arrays
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 2
- Rationale: The failing goal has exactly the assumptions needed for the existing theorem `sparse_has_type_length`: `sparse_has_type tv len sparse` and `SORTED $< (MAP FST sparse)`. The remaining proof is elementary natural-number transitivity using the existing fixed-array bound and slot positivity.
- Dependencies: C2.4.1.1
- Checkpoint: yes
- Supersedes: old C2.4.1.2
- Progress transition: `replacement`
- Carries progress/evidence from: E0798
- Invalidates prior progress/evidence: old C2.4.1.2 cleanup leaf

#### Progress note
E0798 closes the old cleanup leaf as plan-incomplete and motivates replacing this ID with the newly exposed builtin repair. The old cleanup obligation is reclassified under C2.4.1.3.

#### Summary
- Patch `semantics/prop/vyperTypeBuiltinsScript.sml` theorem `Len_result_fits_uint256`.
- In the fixed-array `SArrayV sparse` branch, use `sparse_has_type_length` to derive `LENGTH sparse <= len`.
- Combine this with `0 < slot` and `len * slot < bound` to prove `LENGTH sparse < dimword(:256)`.
- Verify with `holbuild build vyperTypeBuiltinsTheory` and preferably `holbuild build vyperTypeStmtSoundnessTheory` up to the next planned failure.

#### Description
The old proof branch split on `0 < len` and tried to prove the zero-length case by arithmetic alone. After `toplevel_array_length` succeeds on materialized static arrays, the returned value is `LENGTH sparse`, so the proof must use the sparse typing invariant to show the sparse representation cannot contain entries beyond the declared fixed length. The theorem `sparse_has_type_length` is already present in `vyperTypingScript.sml` and is visible in generated `vyperTypingTheory`; use it rather than creating an ad hoc local induction.

#### Statement
Repair existing theorem without changing its statement:
```sml
Theorem Len_result_fits_uint256:
  well_typed_builtin_app ty Len [arg_ty] ∧
  evaluate_type tenv arg_ty = SOME arg_runtime_tv ∧
  well_formed_type_value arg_runtime_tv ∧
  toplevel_value_typed arg_tv arg_runtime_tv ∧
  toplevel_array_length cx arg_tv st = (INL n, st') ==>
  n < dimword(:256)
```
Optional local helper shape if direct use is awkward:
```sml
Theorem sparse_fixed_array_length_lt_bound[local]:
  SORTED $< (MAP FST sparse) ∧ sparse_has_type tv len sparse ∧
  0 < slot ∧ len * slot < bound ==>
  LENGTH sparse < bound
```

#### Approach
In the failing fixed-array branch, after abbreviating `len`, `slot`, and `bound`, derive `LENGTH sparse <= len` by `drule_all sparse_has_type_length` (or `irule`/`metis_tac` with the two assumptions). Derive `len <= len * slot` from `0 < slot` using arithmetic, then chain `LENGTH sparse <= len`, `len <= len * slot`, and `len * slot < bound` with `LESS_EQ_TRANS`/`LESS_EQ_LESS_TRANS`. Avoid special-casing `len = 0` unless arithmetic automation needs it; the length bound handles zero cleanly.

#### Not to try
Do not restore the old contradiction/probe behavior where materialized `SArrayV` Len raises TypeError; C2.4.1.1 intentionally changed that semantics. Do not unfold `sparse_has_type` manually in `Len_result_fits_uint256`; the exported `sparse_has_type_length` theorem is the intended proof interface. Do not push this arithmetic into `vyperTypeStmtSoundnessScript.sml`; statement soundness should consume builtin boundary facts.

### C2.4.1.3: Replace old counterexample probes with post-repair regression/audit
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 20
- Work units: 1
- Rationale: Once `Len_result_fits_uint256` builds, stale local probes in `vyperTypeStmtSoundnessScript.sml` that asserted TypeError for fixed `SArrayV` Len are mechanically obsolete. Cleanup is deletion or conversion to success-regression facts using the repaired definition.
- Dependencies: C2.4.1.2
- Progress transition: `reclassified`
- Carries progress/evidence from: old C2.4.1.2, E0798

#### Progress note
This is the old C2.4.1.2 cleanup obligation moved after the builtin theorem repair that E0798 showed is a strict prerequisite for verifying `vyperTypeStmtSoundnessTheory`.

#### Summary
- Remove or rewrite stale local counterexample probes around lines 7674-7757 of `vyperTypeStmtSoundnessScript.sml`.
- The facts `len_fixed_array_value_typed_but_toplevel_array_length_type_error` and `len_fixed_array_well_typed_expr_type_error_probe` are no longer true after C2.4.1.1.
- If keeping regression coverage, replace them with success/no-TypeError checks for `SArrayV` Len.
- Verify that no local theorem still claims `TypeError "toplevel_array_length"` for a well-typed fixed array value.

#### Description
The current source context shows stale local probes immediately before `Resume eval_all_type_sound_mutual[Expr_Builtin]`. After the definition repair, `toplevel_array_length cx (Value (ArrayV (SArrayV sparse))) st` computes `(INL (&LENGTH sparse), st)`, so any theorem stating it returns `INR (Error (TypeError "toplevel_array_length"))` must be removed or changed. This cleanup should be small and should not attempt to solve the entire builtin branch.

#### Statement
No frozen theorem statement. Source cleanup target:
```sml
Theorem len_fixed_array_value_typed_but_toplevel_array_length_type_error[local]: ...
Theorem well_typed_fixed_array_expr_can_eval_to_sarray_probe[local]: ...
Theorem len_fixed_array_well_typed_expr_type_error_probe[local]: ...
```
Delete false probes or replace with local regression facts asserting successful length evaluation for materialized fixed arrays.

#### Approach
After C2.4.1.2, build will reach `vyperTypeStmtSoundnessScript.sml` again. Delete the false TypeError probes; keep `well_typed_fixed_array_expr_can_eval_to_sarray_probe` only if useful and true, otherwise remove it with its consumers. If replacing with a regression, state the direct computation of `toplevel_array_length` on `SArrayV []` and prove by `simp[toplevel_array_length_def, return_def]`.

#### Not to try
Do not leave false local theorems with `cheat` or weakened assumptions. Do not spend effort proving large env-consistency witnesses for a regression probe unless a downstream proof consumes it; direct computation regressions are sufficient.

### C2.4.1.4: Prove Len typed-runtime no-TypeError boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: After the definition and builtin length-bound repairs, the prior fixed-array counterexample is gone. The boundary follows by case analysis on the typed Len argument/result shape and should isolate `toplevel_array_length_def` from statement consumers.
- Dependencies: C2.4.1.2, C2.4.1.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C2.4.1.3

#### Progress note
Same downstream boundary obligation as before, now explicitly dependent on the builtin repair and stale-probe cleanup.

#### Summary
- Establish the typed Len no-TypeError boundary needed by `Expr_Builtin`.
- It should say that under well-typed Len application, evaluated typed argument value, and consistent runtime typing, `toplevel_array_length` cannot produce `Error (TypeError ...)`.
- Use `Len_result_fits_uint256`/`Len_builtin_sound` for success typing and direct `toplevel_array_length` case analysis only inside this lemma.
- This lemma is a checkpoint because it is the consumer-facing interface for statement soundness.

#### Statement
Use the current source’s intended boundary statement if already present. If absent, introduce a local theorem in `vyperTypeStmtSoundnessScript.sml` or exported theorem in `vyperTypeBuiltinsScript.sml` with this shape:
```sml
well_typed_builtin_app ty Len [arg_ty] ∧
evaluate_type tenv arg_ty = SOME arg_runtime_tv ∧
toplevel_value_typed arg_tv arg_runtime_tv ∧
well_formed_type_value arg_runtime_tv ==>
∀cx st err st'.
  toplevel_array_length cx arg_tv st = (INR (Error (TypeError err)), st') ==> F
```
Adjust quantifiers/names to match the `Expr_Builtin` use site.

#### Approach
Prove by cases on `arg_ty`, evaluated runtime type, and `arg_tv`, reusing the repaired `toplevel_array_length_def` cases. Keep all unfolding in this boundary lemma. For success branches, `Len_result_fits_uint256` and `Len_builtin_sound` should remain available to prove the uint256 result typing separately.

#### Not to try
Do not duplicate this case split directly in `eval_all_type_sound_mutual[Expr_Builtin]`. Do not use the deleted fixed-array TypeError probe as a contradiction; the semantics now succeeds on `SArrayV`.

### C2.4.1.5: Finish `eval_all_type_sound_mutual[Expr_Builtin]` Len branch
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 3
- Rationale: With the typed Len no-TypeError boundary in place, the remaining statement proof branch is proof integration rather than semantic design. The success branch can rely on `Len_builtin_sound`, and the TypeError branch is contradicted by C2.4.1.4.
- Dependencies: C2.4.1.4
- Progress transition: `refinement`
- Carries progress/evidence from: C2.4.1.4

#### Progress note
This is the old C2.4.1.4 integration obligation shifted after the newly inserted builtin repair and cleanup.

#### Summary
- Complete the `Resume eval_all_type_sound_mutual[Expr_Builtin]` Len case in `vyperTypeStmtSoundnessScript.sml`.
- Use the boundary lemma from C2.4.1.4 rather than unfolding `toplevel_array_length_def` in the mutual proof.
- Use `Len_builtin_sound` for the successful value typing obligation.
- Verify with `holbuild build vyperTypeStmtSoundnessTheory` before proceeding to broader statement soundness work.

#### Statement
Close the existing suspended/resumed proof branch:
```sml
Resume eval_all_type_sound_mutual[Expr_Builtin]:
  ...
QED
```
Do not change public theorem statements unless a later checked failure proves the current statement is false.

#### Approach
At the Len subcase, split on the result of `toplevel_array_length`. If it is a TypeError, invoke the C2.4.1.4 no-TypeError boundary with the typed argument facts already in the mutual proof context. If it succeeds, invoke `Len_builtin_sound` to obtain `value_has_type` for the returned uint256 length, then discharge the mutual invariant conjuncts by the existing expression proof framework.

#### Not to try
Do not start a second induction over expression evaluation. Do not inline all builtin typing cases in the statement proof; only the Len-specific boundary should be used here.

### C2.5: Close `Expr_TypeBuiltin` statement-soundness case using completed type-builtin boundaries
- Kind: `proof`
- Risk: 2
- Work priority: 60
- Work units: 5
- Rationale: After C4.3/C4.4/C4.5 close, the type-builtin expression branch is the same consumer pattern as ordinary builtins.
- Dependencies: C2.4, C4.3, C4.4, C4.5
- Supersedes: C2.5
- Progress transition: `replacement`
- Invalidates prior progress/evidence: old C2.5 authorization before C4.3/C4.4/C4.5

#### Progress note
This component is rebased after the whole-plan review. Its previous local replacement attempt was correctly rejected because it could not reorder cross-top-level C4 dependencies.

#### Summary
- Replace `Resume eval_all_type_sound_mutual[Expr_TypeBuiltin]: cheat QED`.
- Consume C4.3 no-TypeError and C4.4 success typing.
- Use C4.5 for raw-call/ABI/Env side facts if the type-builtin branch needs them.
- Keep ABI encode/decode reasoning out of C2.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_TypeBuiltin]:
  ...
QED
```

#### Approach
Unfold the type-builtin expression typing and evaluator one step to expose argument evaluation and `evaluate_type_builtin`. Use the `eval_exprs` IH to obtain no-TypeError/preservation for arguments and runtime typed argument values; then invoke `well_typed_type_builtin_no_type_error` for TypeError exclusion and `well_typed_type_builtin_success_type` for successful result typing.

#### Not to try
Do not locally prove ABI encode bounds, raw-call return-size facts, or MsgGas arithmetic in `vyperTypeStmtSoundnessScript.sml`; those are C4-owned facts. Do not start before C4.3/C4.4/C4.5 are cheat-free.

### C2.6: Close external and special call-target expression resumes
- Kind: `proof`
- Risk: 2
- Work priority: 70
- Work units: 8
- Rationale: These call targets do not evaluate a Vyper function body. After arguments/drivers are handled by IHs, target-specific no-TypeError and typing facts come from C4 boundaries.
- Dependencies: C2.5, C4.5
- Progress transition: `refinement`
- Carries progress/evidence from: old C2.6
- Invalidates prior progress/evidence: old C2.6 scheduling before C4.5

#### Progress note
Rescheduled after C4.5 so raw/special-call facts are available before C2 consumers run.

#### Summary
- Replace cheats for `Expr_Call_ExtCall`, `Expr_Call_Send`, `Expr_Call_RawCallTarget`, `Expr_Call_RawLog`, `Expr_Call_RawRevert`, `Expr_Call_SelfDestructTarget`, and `Expr_Call_CreateTarget` as present in current source.
- Use argument/driver IHs and C4 raw/special-call no-TypeError facts.
- Prove only the mutual statement-theory obligations; public call wrappers remain C5.
- Avoid importing or depending on `vyperTypeCallSoundness`.

#### Statement
Resume blocks in `semantics/prop/vyperTypeStmtSoundnessScript.sml` for external and special call expression cases, including:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_Send]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_RawLog]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_RawRevert]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_SelfDestructTarget]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_CreateTarget]: ... QED
```

#### Approach
For each call target, unfold `well_typed_expr_def` and `evaluate_def` only to the point where subexpressions/argument lists are evaluated. Apply IHs to subexpressions and `eval_exprs`; on successful arguments, use C4.5 raw/special-call facts to rule out TypeError and establish result typing. Group similar raw-call/log/revert cases only if the proof script remains readable; otherwise prove small branch helpers in the same file.

#### Not to try
Do not call the wrapper theorems in `vyperTypeCallSoundnessScript.sml`; that would create a cycle or duplicate the architecture. Do not unfold raw-call encoding/ABI internals in C2.

### C2.7: Prove non-circular internal-call support and close `Expr_Call_IntCall`
- Kind: `proof_group`
- Risk: 2
- Work priority: 80
- Work units: 0
- Rationale: Internal calls are the only remaining C2 case with recursive statement-body evaluation. Splitting callee typing, call-frame consistency, and resume integration gives low-risk leaves matching evaluator order.
- Dependencies: C2.6
- Progress transition: `refinement`
- Carries progress/evidence from: old C2.7

#### Progress note
Internal-call work remains downstream of builtin/type-builtin/special-call consumers so the mutual proof can be finalized cleanly.

#### Summary
- Add non-circular helpers for function body typing and call-frame environment consistency.
- Close `Expr_Call_IntCall` using argument/default IHs and the statement-body IH.
- Keep call wrapper public theorems in C5.
- Avoid importing `vyperTypeCallSoundness` into statement soundness.

#### Statement
Close:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_IntCall]:
  ...
QED
```

#### Approach
First prove the two helpers C2.7.1 and C2.7.2. Then in the resume follow evaluator order: argument IH, default IH, function lookup/body typing helper, frame consistency helper, body statement IH, scope/pop restoration, and result typing/no-TypeError projection.

#### Not to try
Do not use `internal_call_no_type_error` or `internal_call_type_preservation` wrappers in the mutual proof. Do not duplicate `functions_well_typed_def` map projections in the final resume.

#### Argument
Internal call evaluation first evaluates explicit arguments and defaults, then constructs a callee frame, evaluates the callee body, and restores/pops scope. Static `functions_well_typed` and function signature consistency recover the body typing environment and return type. Runtime argument/default typedness plus env-extension/scope-push lemmas establish `env_consistent` for the callee frame. The mutual IH on the body gives no-TypeError and preservation; scope-pop restoration lemmas transfer preservation back to the caller frame.

#### Definition design
Helpers should expose exactly what the resume needs: callee body typing facts from `functions_well_typed`, and a frame-consistency lemma that consumes evaluated argument/default values plus `LIST_REL value_has_type`. Failure signs are manual reconstruction of large finite maps in the resume or theorem plumbing with quoted full assumptions. If needed, make the helper conclusion include the exact `env_consistent env_body cx st_call` and parameter assignability facts.

#### Code structure
Place helper lemmas before `Finalise eval_all_type_sound_mutual` in `vyperTypeStmtSoundnessScript.sml` unless doing so creates clutter; a separate prerequisite theory is acceptable only if it does not import `vyperTypeCallSoundness`. Public wrappers remain in `vyperTypeCallSoundnessScript.sml` under C5.

### C2.7.1: Expose callee body typing facts in a non-circular helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: A similar helper exists in the call wrapper layer, but C2 needs a non-circular version before statement soundness finalizes. The proof is map/projection work from `functions_well_typed_def`.
- Progress transition: `refinement`
- Carries progress/evidence from: old C2.7.1

#### Progress note
Retained but scheduled after C2.6 through parent dependency.

#### Summary
- Prove a helper recovering callee body environment, return type evaluation, defaults typing, parameter types, and body `type_stmts` from function lookup and `functions_well_typed`.
- Avoid depending on `vyperTypeCallSoundness`.
- Match the `Expr_Call_IntCall` resume use site.

#### Statement
A non-circular analogue of `functions_well_typed_body` suitable for use before `vyperTypeCallSoundness`, with current source variables for `env`, `cx`, `src`, `fn`, signature maps, defaults, parameters, return type, and body.

#### Approach
Unfold `functions_well_typed_def` and function signature consistency only as needed, then project the existing body typing record. Include in the conclusion the exact environment fields and parameter assignability facts needed by the internal-call resume.

#### Not to try
Do not import or use the theorem from `vyperTypeCallSoundnessScript.sml` if that theory depends on statement soundness.

### C2.7.2: Prove call-frame environment consistency from evaluated arguments/defaults
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: This is frame/env consistency bookkeeping using existing env extension, scope push/pop, and expression-list runtime typing facts. The helper prevents brittle map reconstruction in the final resume.
- Dependencies: C2.7.1
- Progress transition: `refinement`
- Carries progress/evidence from: old C2.7.2

#### Progress note
Retained with explicit dependency on the callee typing helper.

#### Summary
- Prove that evaluated typed arguments/defaults initialize a callee frame consistent with the callee body environment.
- Consume `exprs_runtime_typed`/`LIST_REL value_has_type` and parameter typing facts.
- Export a conclusion matching the internal-call resume.
- Keep scope restoration facts separate unless they are already part of an existing helper.

#### Statement
Helper theorem shape:
```sml
... /\nexprs_runtime_typed env args arg_tvs /
LIST_REL value_has_type param_tvs arg_values /
callee_body_typing_facts ... ==>
env_consistent env_body cx st_call /\ state_well_typed st_call /\ accounts_well_typed st_call.accounts
```
Use current source names and exact call-frame construction terms.

#### Approach
Use existing env-extension and scope-push lemmas rather than unfolding all finite maps. If the resume needs both explicit and default arguments, prove the helper over the combined parameter/value list so the conclusion directly feeds the body IH.

#### Not to try
Do not manually instantiate many `FLOOKUP` goals in the final resume. If the helper needs a stronger conclusion for `drule`, strengthen it here.

### C2.7.3: Close the `Expr_Call_IntCall` mutual-proof resume
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: With callee body typing and call-frame consistency helpers, the resume follows evaluator order and uses the mutual IH for argument/default expressions and callee body statements.
- Dependencies: C2.7.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C2.7.3

#### Progress note
Checkpoint because this should allow finalizing `eval_all_type_sound_mutual` once C2.4-C2.6 are done.

#### Summary
- Replace `Resume eval_all_type_sound_mutual[Expr_Call_IntCall]: cheat QED`.
- Use C2.7.1/C2.7.2 helpers, argument/default IHs, and body statement IH.
- Prove no-TypeError and result/state preservation for internal calls.
- Do not call downstream C5 wrapper theorems.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_IntCall]:
  ...
QED
```

#### Approach
Unfold the evaluator to expose function lookup, argument/default evaluation, frame setup, body evaluation, and restoration. Apply IHs in the semantic order; after successful setup, invoke the call-frame helper and then the statement-list/body IH. Finish by applying scope-pop/restoration preservation lemmas and projecting expression result typing for the call return value.

#### Not to try
Do not unfold all function/body maps inline. Do not use wrappers from `vyperTypeCallSoundnessScript.sml`.

### C2.8: Audit `vyperTypeStmtSoundnessTheory` for build success and zero local cheats
- Kind: `build_audit`
- Risk: 1
- Work priority: 90
- Work units: 2
- Rationale: After all remaining resumes are proved, local validation is mechanical and catches forgotten `cheat`/`suspend` scaffolding before downstream wrapper work.
- Dependencies: C2.7.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C2.8

#### Progress note
Still required, but now scheduled after all rebased C2 leaves.

#### Summary
- Build `vyperTypeStmtSoundnessTheory`.
- Grep `vyperTypeStmtSoundnessScript.sml` for remaining `cheat`/unexpected suspended resumes.
- Report any reachable residual as a new focused dependency.
- This is the checkpoint before C5 call wrappers and C6 public wrappers.

#### Statement
`holbuild build vyperTypeStmtSoundnessTheory` succeeds with no local CHEAT warnings from `vyperTypeStmtSoundnessScript.sml`.

#### Approach
Run the build and a scoped grep. If a remaining cheat is in an in-scope resume, escalate for a new component; if it is unreachable/retired, record evidence and do not expand scope.

#### Not to try
Do not broaden to repository-wide cleanup during this audit.

### C3: Update-binop and assignment-subscript runtime-typed path
- Kind: `proof_group`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The inherited cheats form a localized dependency chain from binop no-TypeError through assignment operation leaf and recursive subscript no-TypeError/preservation. They must be closed before any consumers can count as CHEAT-free, and C4 builtin facts may depend on the binop boundary.
- Required for completion: yes
- Dependencies: C1
- Progress transition: `refinement`
- Carries progress/evidence from: old C3

#### Progress note
C3 is moved before C4/C2 remaining consumers. It owns the inherited update-binop path listed in the TASK and prevents hidden CHEAT dependencies from leaking into statement/builtin proofs.

#### Summary
- Prove the inherited update-binop path without cheats.
- Start with generic binop no-TypeError, then operation leaf soundness, then recursive subscript no-TypeError/preservation.
- C4 builtin boundaries depend on the binop part when they reason about binary operations.
- C2 assignment/Pop consumers may rely on these theorems only after C3 closes.

#### Description
This component is scheduled before C4.2 and before remaining C2 consumers because otherwise theorem proofs could build while still depending on CHEATed update/binop facts.

#### Statement
Close the current source-authoritative inherited path:
```sml
well_typed_binop_no_type_error
well_typed_update_binop_no_type_error
assign_subscripts_update_leaf_no_type_error
assign_operation_runtime_typed_leaf_no_type_error
assign_subscripts_no_type_error_runtime_typed
assign_subscripts_preserves_type_runtime_typed
```

#### Approach
Prove in dependency order: binop no-TypeError first, update-binop as a corollary, operation leaf no-TypeError, then recursive subscript no-TypeError and preservation by the existing recursion induction. Derive compatibility theorem names after any stronger joint lemma so downstream source need not change broadly.

#### Not to try
Do not let C2/C4 prove around these cheats. Do not split no-TypeError and preservation into independent recursive inductions if the current helper already carries both runtime typing and preservation information.

#### Argument
The chain is structural. A well-typed binary operation on typed operands never reaches the `TypeError` fallback branch of `evaluate_binop`; arithmetic failures are runtime errors or successful bounded values. Assignment operation leaf soundness then splits on `AssignOp`, `UpdateOp`, `AppendOp`, and `PopOp`: update uses the binop theorem, append/pop use array dynamic/fixed shape and existing value typing, and plain assignment uses the provided assigned value typing. Recursive `assign_subscripts` soundness follows the subscript list/path recursion, with the leaf theorem applied after the target path has reduced to the final leaf type.

#### Definition design
The boundary theorems should match existing current-source names in `vyperTypeStatePreservationScript.sml`: `well_typed_binop_no_type_error`, `well_typed_update_binop_no_type_error`, `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`. If existing statements are underspecified but not frozen, strengthen a joint helper and derive compatibility corollaries with these names. Failure signs are large consumers unfolding `evaluate_binop_def` or `assign_subscripts_def` outside this layer.

#### Code structure
Keep binop-specific facts in `vyperTypeBuiltinsScript.sml` if the theorem currently lives there, and assignment-subscript recursion facts in `vyperTypeStatePreservationScript.sml`. Do not move statement-level assignment cases into this component; C2 only consumes the resulting boundary lemmas.

### C3.1: Close binop no-TypeError boundary lemmas
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: Finite case analysis over binop/type/value constructors is already supported by many local per-operator no-TypeError helpers in `vyperTypeBuiltinsScript.sml`. The main work is completing the generic theorem without cheat.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C3.1

#### Progress note
Moved earlier so C4 builtin boundaries do not depend on cheated binop facts.

#### Summary
- Replace the cheat for `well_typed_binop_no_type_error` and any direct binop no-TypeError scaffold it depends on.
- Use existing per-operator helper lemmas for concrete well-typed values.
- Export a theorem matching update-binop and builtin consumers.
- Checkpoint because many downstream leaves depend on this boundary.

#### Statement
Current source theorem, expected name:
```sml
Theorem well_typed_binop_no_type_error:
  ...
Proof
  ...
QED
```
and any immediate `well_typed_update_binop_no_type_error` corollary if it is in the same source region.

#### Approach
Unfold the well-typed binop predicate enough to identify the operator/type class and operand value constructors, then apply the local `binop_no_type_error_*` helpers rather than simplifying all of `evaluate_binop_def`. For success-typing side facts use existing binop success typing lemmas if present; otherwise keep the goal to no-TypeError only and split constructors locally.

#### Not to try
Do not use a single enormous `gvs[evaluate_binop_def, AllCaseEqs()]` over all operators if it causes case explosion. Do not prove arithmetic bounds in consumers; keep them here or in existing value/builtin helper layers.

### C3.2: Close assignment operation leaf no-TypeError
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: After C3.1, assignment operation leaves reduce by finite operation cases: update uses binop no-TypeError, append/pop use array operation facts, and plain assignment uses value typing.
- Dependencies: C3.1
- Progress transition: `refinement`
- Carries progress/evidence from: old C3.2

#### Progress note
C3.2 remains the strict prerequisite for recursive subscript closure.

#### Summary
- Prove `assign_subscripts_update_leaf_no_type_error` and `assign_operation_runtime_typed_leaf_no_type_error` without cheats.
- Consume C3.1 for update operations.
- Keep operation-shape assumptions explicit.
- Do not reason about recursive subscript traversal here.

#### Statement
Current source theorem names:
```sml
assign_subscripts_update_leaf_no_type_error
assign_operation_runtime_typed_leaf_no_type_error
```

#### Approach
Case split on the assignment operation and, for update, apply `well_typed_update_binop_no_type_error`. For append/pop, use the strengthened operation runtime typing (`PopOp` requires dynamic array) and existing array operation definitions to rule out `TypeError`; runtime errors are allowed.

#### Not to try
Do not fold recursive subscript preservation into this leaf. Do not drop the strengthened `assign_operation_runtime_typed` dynamic-array precondition for `PopOp`.

### C3.3: Close recursive assignment-subscript no-TypeError and preservation
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: The recursive helper follows the `assign_subscripts` recursion over the target path/subscripts and consumes the leaf operation theorem from C3.2.
- Dependencies: C3.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C3.3

#### Progress note
Checkpoint because C1/C2 final CHEAT-freedom depends on these recursive helpers no longer carrying cheats.

#### Summary
- Prove `assign_subscripts_no_type_error_runtime_typed` and `assign_subscripts_preserves_type_runtime_typed` without cheats.
- Use recursion-matching induction over `assign_subscripts`.
- Leaf case consumes C3.2; recursive cases use target-path typing/leaf-type bridge lemmas.
- Preserve compatibility theorem names for existing callers.

#### Statement
Current source theorem names:
```sml
assign_subscripts_no_type_error_runtime_typed
assign_subscripts_preserves_type_runtime_typed
```

#### Approach
Use the function induction principle for `assign_subscripts` or structural induction on the subscript/path list, whichever matches the current definition. In each recursive branch, invert the relevant `target_path_type`/`place_leaf_typed` premise to obtain the sub-leaf type and apply the IH; in the base branch use C3.2.

#### Not to try
Do not reprove top-level storage/hashmap assignment branch facts here. Do not unfold callers like `assign_target`; this component is only about subscript recursion.

### C4: ABI/builtin prerequisite soundness stack (structural ancestor)
- Kind: `structural_context`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Carry-forward ancestor included only to satisfy dotted-component validation; this update changes no C4 siblings and the max risk of the edited C4.4.5 subtree is 2.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4, E0781

#### Progress note
No strategic change is made at C4 scope. The only substantive update is within descendant C4.4.5.

#### Summary
- Structural ancestor for ABI/builtin prerequisite obligations.
- Included only so the C4.4.5 dotted subtree validates.
- No C4 siblings are added, removed, reordered, or redesigned by this update.

#### Approach
Proceed only into the C4.4.5 subtree for executable work.

#### Not to try
Do not treat this structural parent as authorization to replan C4 siblings.

#### Argument
This ancestor carries the existing ABI/builtin prerequisite context. The current update does not change the C4-level argument; it only refines the local ABI encoding length-bound proof in C4.4.5.

#### Definition design
No C4-level definition design changes are made. New definitions introduced by this update are local to `vyperTypeABIScript.sml` under C4.4.5.

#### Code structure
No C4-level file organization changes are made. All executable edits from this update belong to `semantics/prop/vyperTypeABIScript.sml` in the C4.4.5 region.

### C4.1: Carry forward closed reachable static builtin-typing suspended cases
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0735 accepted this leaf as proved, and no current C4.4/C4.5 repair changes its statements or definitions.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.1, E0735

#### Progress note
Preserved as completed evidence under the C4 scheduling rebase.

#### Summary
- Static builtin-typing suspended cases are already closed or audited as unreachable.
- No executor work remains here.
- Later C4 leaves may rely on the generic static builtin interface being stable.

#### Statement
Already-proved reachable suspended cases in `vyperBuiltinTypingScript.sml` / builtin static typing support required by the fresh stack.

#### Approach
No action. If a future build reports a regression in this area, escalate with the exact theorem and dependency path.

#### Not to try
Do not reopen the large suspended static-builtin case split as part of ABI or raw-call work.

### C4.2: Carry forward generic builtin no-TypeError and success typing boundary
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: E0740 accepted the generic builtin boundary. Remaining C4 work is in type-builtins and raw-call support, not this generic builtin proof.
- Dependencies: C4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.2, E0740

#### Progress note
Preserved as completed evidence under the C4 scheduling rebase.

#### Summary
- Generic builtin no-TypeError/success typing boundary is complete.
- No executor work remains.
- This leaf stays before type-builtin work because later facts may use the same builtin typing context.

#### Statement
Already-proved generic builtin no-TypeError and success typing theorems in the reachable fresh stack.

#### Approach
No action. Treat this as stable boundary evidence for downstream evaluator/call proofs.

#### Not to try
Do not duplicate generic builtin constructor analysis inside C4.4 or C4.5.

### C4.3: Carry forward repaired type-builtin no-TypeError boundary
- Kind: `proof_group`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: C4.3.1-C4.3.3 are accepted as proved through E0745 and directly precede the remaining type-builtin success theorem.
- Dependencies: C4.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.3, C4.3.1, C4.3.2, C4.3.3, E0743, E0744, E0745

#### Progress note
The Extract32 repair and no-TypeError theorem remain valid and are the static interface consumed by C4.4.

#### Summary
- Carries forward the repaired `Extract32` static predicate.
- Carries forward the supported-target Extract32 no-TypeError helper.
- Carries forward the closed `well_typed_type_builtin_no_type_error` theorem.
- No executor work remains in this group.

#### Statement
Already-proved repaired `well_typed_type_builtin_no_type_error` and helper facts.

#### Approach
No action. C4.4 should use these definitions directly and should not reopen the C4.3 proof.

#### Not to try
Do not weaken the repaired `Extract32` restriction or reintroduce Bool/unsupported targets.

#### Argument
The no-TypeError theorem for type-builtins is already repaired by strengthening static admissibility for `Extract32`. This ensures the evaluator cannot choose an unsupported target type in that branch. The success-typing theorem in C4.4 should consume the same repaired static interface but need not redo its no-TypeError reasoning.

#### Definition design
The key definition interface is now `well_typed_type_builtin_args_def` plus `type_builtin_result_ok_def`. For `Extract32`, supported target bases are part of static admissibility. For ABI encode, size bounds are part of `type_builtin_result_ok_def`, not an external postulate.

#### Code structure
No edits in this carried group. New type-builtin success work should remain below the existing `Resume well_typed_type_builtin_success_type[...]` clauses in `vyperTypeBuiltinsScript.sml`.

### C4.3.1: Carry forward Extract32 static predicate repair and Bool rejection regression
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0743 proved this definition repair/regression and it remains the source-authoritative static interface.
- Dependencies: C4.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.3.1, E0743

#### Progress note
Carried forward under C4.3; listed explicitly so prior evidence remains visible after subtree replacement.

#### Summary
- `Extract32` static target restriction repair is complete.
- Bool/unsupported-target regression is proved.
- No remaining work.

#### Statement
Current source definitions/probes around `well_typed_type_builtin_args_def` and `extract32_result_base_ok_def` are already repaired.

#### Approach
No action.

#### Not to try
Do not alter this definition while proving ABI encode branches.

### C4.3.2: Carry forward supported Extract32 no-TypeError helper
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: E0744 proved the helper using the repaired static premise.
- Dependencies: C4.3.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.3.2, E0744

#### Progress note
Carried forward under C4.3; no proof work remains.

#### Summary
- Supported-target Extract32 no-TypeError helper is complete.
- It is available to the finalized type-builtin no-TypeError theorem.
- No remaining work.

#### Statement
Already-proved local Extract32 no-TypeError helper in `vyperTypeBuiltinsScript.sml`.

#### Approach
No action.

#### Not to try
Do not destruct Extract32 values again in unrelated ABI branches.

### C4.3.3: Carry forward repaired `well_typed_type_builtin_no_type_error`
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: E0745 proved and built `vyperTypeBuiltinsTheory` through this theorem.
- Dependencies: C4.3.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.3.3, E0745

#### Progress note
This is the prerequisite boundary for the remaining C4.4 success typing proof.

#### Summary
- Repaired type-builtin no-TypeError theorem is complete.
- `vyperTypeBuiltinsTheory` built after this checkpoint.
- No remaining work.

#### Statement
`Theorem well_typed_type_builtin_no_type_error: ...` is already proved in current source.

#### Approach
No action. C4.4 starts after this carried theorem.

#### Not to try
Do not reopen the no-TypeError theorem while proving success typing.

### C4.4: ABI encode bound obligations (structural ancestor)
- Kind: `structural_context`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Carry-forward ancestor included only to satisfy dotted-component validation; the updated descendant C4.4.5 remains risk 2 after decomposition.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.4, E0781

#### Progress note
No C4.4 sibling is replanned. This update only decomposes active child C4.4.5.

#### Summary
- Structural ancestor for ABI encode bound obligations.
- Included only so the C4.4.5 dotted subtree validates.
- No C4.4 siblings are substantively modified by this update.

#### Approach
Proceed into C4.4.5. Do not start work on C4.4 siblings from this update.

#### Not to try
Do not use this ancestor as a license to address unrelated ABI cheats or builtin cases.

#### Argument
The ABI encode bound layer proves static encoded-size estimates needed by ABI encode builtin soundness. The current update leaves the surrounding C4.4 strategy intact and repairs only the direct Vyper-to-ABI length-bound theorem by local helper decomposition.

#### Definition design
No C4.4-level definition design changes are made beyond the C4.4.5 local helper definitions.

#### Code structure
No C4.4-level file organization changes are made. All executable work remains in `semantics/prop/vyperTypeABIScript.sml`.

### C4.4.1: Carry forward already-proved typed ABI encoder wrappers
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0756 closed this component, and E0758 does not invalidate typed ABI encoder wrappers; it only shows they cannot be generalized to malformed values without extra premises.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.4.1, E0756

#### Progress note
No new executor work. These wrappers remain available as auxiliary facts for genuinely ABI-typed values, but not as the core default/converted Vyper interface.

#### Summary
Already closed. Keep the typed `has_type` encoder length wrappers. They are auxiliary and must not be used to assert ABI typing of unaligned Vyper integers or defaults.

### C4.4.2: Remove the false default ABI typing attempt
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: E0757 closed this cleanup. The false `default_to_abi_has_type*` block has been removed; E0758's temporary counterexample belongs to C4.4.3 cleanup, not this component.
- Dependencies: C4.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.4.2, E0757

#### Progress note
No new executor work for the old false default ABI typing cleanup.

#### Summary
Already closed. The unconditional default ABI `has_type` theorem is false and should stay deleted. Do not reintroduce byte-alignment preconditions into builtin-facing Vyper length theorems.

### C4.4.3: Add hybrid no-ABI-typing encoder length algebra
- Kind: `infrastructure_subtree`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The generic encoder algebra is now split into raw actual-length facts and static-premise corollaries. Each leaf is a standard induction over `ts`/`vs` or a wrapper around `enc_def`; no false fully no-type static-length claim remains.
- Dependencies: C4.4.2
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0758
- Invalidates prior progress/evidence: old C4.4.3 fully no-type tuple head-sum lemma, enc_tuple_head_sum_length_bound_no_type_counterexample as durable source

#### Progress note
E0758 closes the old statement as wrong and motivates this replacement. Prior failed proof work does not count toward the new lemmas except as diagnostic evidence.

#### Summary
Replace the false no-type static head-sum lemma. First remove the diagnostic counterexample theorem from source after recording it in the episode. Prove a raw tuple accumulator bound that uses actual `LENGTH (enc t v)` for static elements. Prove a monotone/static-premise corollary that may use `static_length t` only under `~is_dynamic t ==> LENGTH (enc t v) <= static_length t`. Build dynamic/fixed array wrappers with the same static premise and fixed-array length side condition.

#### Argument
The recursion of `enc_tuple` adds one head per matched `(t,v)` pair and, for dynamic elements, one tail equal to `enc t v`. Thus the unconditional invariant is exact up to list reversal/flattening and uses actual element encoding lengths. To recover ABI layout bounds, fold in a separate per-static-element side condition; this is the minimal replacement for the lost `has_type` hypothesis. Array wrappers instantiate tuple lemmas with `REPLICATE (LENGTH vs) t`; `SUM_MAP2_REPLICATE` then turns per-element bounds into `LENGTH vs * embedded`, with a final monotonic multiplication step for fixed arrays when `LENGTH vs <= n`.

#### Definition design
C4.4.3 exports local proof interfaces only; they are not public ABI typing claims. The raw lemma should be usable without any type premise and should not mention `static_length`. The static-premise corollary is the only lemma in this group whose conclusion contains `static_length` for static elements. Array wrappers must expose assumptions in the shape downstream Vyper proofs can supply: `!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound`, `~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t`, embedded-size inequality, and for fixed arrays `LENGTH vs <= n`.

#### Code structure
Place these lemmas in `vyperTypeABIScript.sml` where the old C4.4.3 lemmas were, before Vyper dynamic/static bridge lemmas. Use `contractABITheory.enc_def`, `LENGTH_FLAT`, `REV_REVERSE_LEM`, `MAP_REVERSE`, `SUM_REVERSE`, `SUM_APPEND`, and `LENGTH_enc_number`; do not unfold `contractABITheory.has_type_def` in this component.

### C4.4.3.0: Remove the diagnostic false no-type counterexample theorem
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: The EVAL counterexample is valid evidence but should not remain in the final proof script as a durable local theorem once the PLAN is repaired.
- Carries progress/evidence from: E0758

#### Progress note
The counterexample remains documented in E0758 and this PLAN. Source should instead contain the repaired lemmas.

#### Summary
Delete `enc_tuple_head_sum_length_bound_no_type_counterexample` from `semantics/prop/vyperTypeABIScript.sml`. Verify that the build still reaches the known `vyper_to_abi_enc_length_bound` probe or the next new C4.4.3 lemma. Do not delete any proved dynamic/static/embedded bridge lemmas.

#### Approach
This is a mechanical edit. Remove only the local counterexample theorem block added for E0758. The expected build state after deletion is unchanged except that this theorem name no longer exists.

#### Not to try
Do not keep the counterexample as a permanent regression theorem in the source; the final task is a clean soundness stack, not a catalog of abandoned lemma shapes.

### C4.4.3.1: Prove raw tuple accumulator bound with actual element encoding lengths
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: This follows directly by induction on `ts` with a case split on `vs`, mirroring the existing typed `enc_tuple_acc_length_bound` but replacing the static branch contribution by `LENGTH (enc t v)`.
- Dependencies: C4.4.3.0

#### Summary
Prove the unconditional tuple-accumulator length lemma. It must not assume `has_types` or any ABI validity. Static and dynamic elements are both bounded by their actual encoded lengths; dynamic elements additionally contribute the 32-byte offset head.

#### Statement
Theorem enc_tuple_acc_length_bound_actual[local]:
  !ts vs hl tl hds tls.
    LENGTH (enc_tuple hl tl ts vs hds tls) <=
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else LENGTH (enc t v)) ts vs)

#### Approach
Induct on `ts` and case split on `vs`. The mismatched-list base cases use the final `enc_tuple` catch-all and `FLAT/REV` length rewrites. In the matched cons case unfold one step of `enc_tuple`; for dynamic elements use `LENGTH_enc_number = 32` for the offset head and put `enc t v` into tails, while for static elements put `enc t v` into heads and no tail.

#### Not to try
Do not try to prove a no-premise bound with `static_length t` in the static branch; E0758 shows it is false for `Tuple []` paired with `NumV 0`. Do not import `has_type` here; this lemma is intentionally raw encoder algebra.

### C4.4.3.2: Prove static-premise tuple head-sum corollary
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: A simple list induction over `ts`/`vs` or a MAP2/SUM monotonic helper converts the raw actual-length sum into the old static-head shape under an explicit static-element length premise.
- Dependencies: C4.4.3.1

#### Summary
Recover the old useful tuple bound, but only with the missing static-element premise. This is the boundary lemma downstream Vyper conversions should use when they can prove each static converted/default element encodes within its static ABI size.

#### Statement
Theorem enc_tuple_acc_length_bound_static_premise[local]:
  !ts vs hl tl hds tls.
    (!t v. MEM (t,v) (ZIP (ts,vs)) /\ ~is_dynamic t ==>
           LENGTH (enc t v) <= static_length t) ==>
    LENGTH (enc_tuple hl tl ts vs hds tls) <=
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)

Theorem enc_tuple_length_bound_static_premise[local]:
  !ts vs.
    (!t v. MEM (t,v) (ZIP (ts,vs)) /\ ~is_dynamic t ==>
           LENGTH (enc t v) <= static_length t) ==>
    LENGTH (enc (Tuple ts) (ListV vs)) <=
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)

#### Approach
First prove a small SUM/MAP2 monotonic fact by induction on `ts` and case split on `vs`, or prove the corollary directly with the raw accumulator lemma plus that induction. For the tuple wrapper, unfold `enc_def` once and instantiate the accumulator with `head_lengths ts 0`, `0`, `[]`, `[]`. Keep the premise over `ZIP (ts,vs)` so cons-step membership facts simplify naturally.

#### Not to try
Do not encode the premise as an ABI `has_types ts vs` assumption; that reintroduces the unaligned-integer problem. Avoid manual large theorem instantiations in consumers; this lemma's conclusion should match the tuple wrapper use site directly.

### C4.4.3.3: Prove replicated MAP2 embedded-size bound under static premise
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 30
- Work units: 2
- Rationale: This is a small variant of the existing `SUM_MAP2_REPLICATE_enc_bound`, with an extra static-element premise used only when `is_dynamic t` is false.
- Dependencies: C4.4.3.2

#### Summary
Adapt the replicated element-sum bound so it can consume the static-premise tuple corollary. Dynamic elements use the per-element `elem_bound`; static elements use the explicit `LENGTH (enc t v) <= static_length t` premise and the embedded-size inequality.

#### Statement
Theorem SUM_MAP2_REPLICATE_enc_bound_static_premise[local]:
  !t vs elem_bound embedded.
    ((!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
              (REPLICATE (LENGTH vs) t) vs) <= LENGTH vs * embedded

#### Approach
Induct on `vs`. In the step case, specialize the IH to the tail and use the MEM premise for `h`. Split on `is_dynamic t`; dynamic uses `elem_bound`, static uses the static premise and the embedded inequality.

#### Not to try
Do not try to reuse the old no-premise replicated bound if it assumes static elements already have `static_length`; the premise is the whole repair.

### C4.4.3.4: Prove dynamic and fixed array no-ABI-typing wrappers with static premises
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 40
- Work units: 3
- Rationale: These wrappers are straightforward instantiations of the static-premise tuple lemma on `REPLICATE (LENGTH vs) t`, plus the replicated SUM bound. Fixed arrays need an explicit `LENGTH vs <= n` side condition because the encoder uses the actual value-list length.
- Dependencies: C4.4.3.3
- Checkpoint: yes
- Invalidates prior progress/evidence: old enc_dyn_array_same_length_bound/enc_fixed_array_same_length_bound as core no-type wrappers if they require ABI has_type

#### Summary
Provide the array interfaces needed by Vyper same/sparse conversions. Dynamic arrays add a 32-byte length prefix and then tuple-encode actual elements. Fixed arrays tuple-encode actual elements and are bounded by `n * embedded` when `LENGTH vs <= n`. No ABI `has_type` premise is used.

#### Statement
Theorem enc_dyn_array_same_length_bound_static_premise[local]:
  !t vs elem_bound embedded.
    ((!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    LENGTH (enc (Array NONE t) (ListV vs)) <= 32 + LENGTH vs * embedded

Theorem enc_fixed_array_same_length_bound_static_premise[local]:
  !n t vs elem_bound embedded.
    (LENGTH vs <= n /\
     (!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    LENGTH (enc (Array (SOME n) t) (ListV vs)) <= n * embedded

#### Approach
Unfold `enc_def` once for each array. Instantiate `enc_tuple_acc_length_bound_static_premise` or the tuple wrapper on `REPLICATE (LENGTH vs) t` and `vs`; the ZIP/MEM static premise reduces to the supplied `MEM v vs` premise. Apply the replicated SUM bound, then arithmetic; for fixed arrays use multiplication monotonicity from `LENGTH vs <= n`.

#### Not to try
Do not depend on `contractABI.has_type_def` to get fixed-array length equality. In this repaired interface the converter/sparse proof supplies `LENGTH vs <= n` (usually equality) explicitly.

### C4.4.4: Default ABI encode-length bridge (structural ancestor)
- Kind: `structural_context`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Carry-forward parent for the edited C4.4.4.3 subtree; the replacement relies on already-proved C4.4.4.2 tuple helpers.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.4.4, C4.4.4.2.1, C4.4.4.2.2, C4.4.4.2.3, C4.4.4.2.4

#### Progress note
Structural parent only. C4.4.4.2 tuple boundary progress carries forward and is consumed by the new C4.4.4.3 leaves.

#### Summary
Structural parent for default ABI bridge work. C4.4.4.2 tuple LIST_REL/SUM/static helpers are assumed closed and carried forward. This update replaces only the brittle C4.4.4.3 proof plan.

#### Argument
Default ABI length bounds are assembled in layers: element bounds, tuple LIST_REL boundaries, evaluator recursion over type/type-list evaluation, then packaging corollaries. This scoped update affects the evaluator-recursion layer only and intentionally consumes, rather than reopens, the tuple boundary layer.

#### Definition design
Use `default_to_abi_elem_bound_rel` as the interface between element evaluation and tuple consumers. The failure sign is any downstream proof needing to unfold `enc_tuple` where a LIST_REL boundary lemma should apply.

#### Code structure
Keep all helper lemmas local in `semantics/prop/vyperTypeABIScript.sml`. Insert new C4.4.4.3 helper immediately after `default_to_abi_tuple_bound_from_LIST_REL`; leave later downstream theorem blocks untouched.

### C4.4.4.1: Audit and preserve existing Vyper dynamic/static and array-default length bridges
- Kind: `source_audit`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: This is a mechanical source audit: the relevant helper lemmas are already present in the current file, and the executor only needs to ensure they remain available before replacing the failed theorem body.
- Progress transition: `refinement`
- Carries progress/evidence from: source lines around vyperTypeABIScript.sml:430-545, E0770 source audit

#### Progress note
E0770 read evidence confirms the fixed-array default helper is present and the stale monolithic theorem starts immediately after it.

#### Summary
Confirm that the existing local helpers for Vyper ABI dynamic/static length and fixed-array defaults are present and usable. Do not edit their statements unless build errors force trivial name/import fixes. This leaf prepares the file for the C4.4.4.2-.4 replacement.

#### Approach
Check `vyper_to_abi_type_dynamic`, `vyper_to_abi_static_length_bound`, `vyper_to_abi_embedded_head_bound`, `enc_fixed_array_replicate_tuple_bound_static_premise`, and `default_fixed_array_replicate_tuple_bound_from_elem`. If all are present, record progress and proceed; no holbuild is required unless the file has been changed.

#### Not to try
Do not try to resume or repair the old `default_to_abi_enc_length_bound_eval` here. This component is only an audit/carry-forward boundary.

### C4.4.4.2: Prove tuple default-encoding bounds from per-element default bounds
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The planned proof remains a standard LIST_REL/list-sum bound after naming the element predicate; the current issue is that its children were queued but not made to block downstream leaves.
- Dependencies: C4.4.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001

#### Progress note
Carries forward the decomposition guidance; only dependency metadata is repaired.

#### Summary
Prove the exact local theorem `default_to_abi_tuple_bound_from_LIST_REL` after C4.4.4.1. Execute children C4.4.4.2.1-.4 in dependency order. This subtree must close before C4.4.4.3, C4.4.4.4, and C4.4.5 are attempted.

#### Description
Replace the current partial/brittle proof block with the local helper family already described: element predicate, head embedded-size bound, static ZIP premise helper, SUM_MAP2 bound helper, and final tuple bound. Run `holbuild build vyperTypeABITheory` after C4.4.4.2.4 closes.

#### Statement
Culminates in the existing local theorem `default_to_abi_tuple_bound_from_LIST_REL` in `semantics/prop/vyperTypeABIScript.sml`; keep its statement unchanged.

#### Approach
Follow the child components in order. Do not start downstream ABI leaves while this source block is partial or while `vyperTypeABITheory` fails here.

#### Not to try
Do not bypass this failed source state by beginning C4.4.5; C4.4.5 assumes the default bridge checkpoint is available.

#### Argument
The LIST_REL premise supplies per-element default encoding and static-length facts. C4.4.4.2.1 turns those into a pointwise embedded-size head bound; C4.4.4.2.2 supplies the static premise for tuple layout; C4.4.4.2.3 bounds the MAP2/SUM by list induction; C4.4.4.2.4 composes those two bounds.

#### Definition design
The local element relation is only a proof-interface device to stabilize LIST_REL consumers. Downstream children should use the relation/head-bound lemma rather than manually manipulating the anonymous lambda.

#### Code structure
Place the helper definition and local theorems immediately before the existing `default_to_abi_tuple_*` block in `semantics/prop/vyperTypeABIScript.sml`.

### C4.4.4.2.1: Name the per-element default ABI bound relation and prove the head embedded-size bound
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Direct use of the existing `vyper_to_abi_embedded_head_bound`; low risk once scheduled before its consumers.
- Dependencies: C4.4.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001

#### Progress note
Same leaf obligation as the decomposition; now explicitly first after the C4.4.4.1 audit.

#### Summary
Add the local element relation and prove the one-element embedded-size head bound. This is the first executable repair leaf for the currently failing tuple-bound block.

#### Statement
Use the previously specified `default_to_abi_elem_bound_rel_def[local]` and `default_to_abi_elem_embedded_size_bound[local]` interfaces.

#### Approach
Unfold the relation, apply `vyper_to_abi_embedded_head_bound`, split on `is_dynamic (vyper_to_abi_type tenv typ)`, and finish arithmetically.

#### Not to try
Do not prove downstream ZIP or SUM facts before this lemma exists; they should consume this pointwise interface.

### C4.4.4.2.2: Prove the static ZIP premise helper from LIST_REL
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 10
- Work units: 2
- Rationale: Routine list induction/MEM_ZIP proof once C4.4.4.2.1 is present.
- Dependencies: C4.4.4.2.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001, E0772

#### Progress note
Same helper; dependency on the named element relation is made explicit.

#### Summary
Re-establish `default_to_abi_tuple_static_premise_from_LIST_REL`. It supplies the static premise for `enc_tuple_length_bound_static_premise` and must precede the final tuple-bound theorem.

#### Statement
Keep the existing local theorem statement `default_to_abi_tuple_static_premise_from_LIST_REL[local]` unchanged.

#### Approach
Induct on `ts` with `tvs` generalized, case split `tvs`, simplify `vyper_to_abi_type_def` and `MEM_ZIP`, use `vyper_to_abi_type_dynamic` in the head static case, and apply the IH in the tail case.

#### Not to try
Do not combine this with the SUM_MAP2 proof or unfold tuple encoding.

### C4.4.4.2.3: Prove the tuple SUM_MAP2 bound from LIST_REL
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Standard head-plus-tail list induction after the pointwise lemma; no unprovability evidence.
- Dependencies: C4.4.4.2.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001

#### Progress note
Same helper; dependency on the pointwise embedded-size lemma is made explicit.

#### Summary
Prove the exact `SUM (MAP2 ...) <= vyper_abi_size_bound_list` helper. This is independent of the static ZIP helper but depends on the pointwise embedded-size bound.

#### Statement
Keep the existing local theorem statement `default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL[local]` unchanged.

#### Approach
Induct on `ts` with `tvs` generalized. In the cons case, split the LIST_REL premise into head and tail facts, use `default_to_abi_elem_embedded_size_bound` on the head, the IH on the tail, and finish with `vyper_abi_size_bound_def` and arithmetic.

#### Not to try
Do not manually fight anonymous-lambda IH matching; rewrite/use the named element relation from C4.4.4.2.1.

### C4.4.4.2.4: Prove the final tuple default-encoding length bound from LIST_REL
- Kind: `target_theorem`
- Risk: 1
- Work priority: 30
- Work units: 2
- Rationale: Direct transitivity once the static ZIP and SUM_MAP2 helpers are proved.
- Dependencies: C4.4.4.2.2, C4.4.4.2.3
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001

#### Progress note
Same final leaf, now explicitly waits for both boundary helpers. Checkpoint is retained because successful build through this block unblocks downstream default ABI work.

#### Summary
Prove `default_to_abi_tuple_bound_from_LIST_REL`. After closing this leaf, run `holbuild build vyperTypeABITheory` to verify the partial source block is repaired before proceeding.

#### Statement
Keep the existing local theorem statement `default_to_abi_tuple_bound_from_LIST_REL[local]` unchanged.

#### Approach
Use `enc_tuple_length_bound_static_premise` plus C4.4.4.2.2 to bound tuple encoding by the MAP2/SUM expression, then C4.4.4.2.3 to bound the SUM by `vyper_abi_size_bound_list`; finish by transitivity/arithmetic.

#### Not to try
Do not unfold `enc` or tuple layout; the proof should be a boundary-lemma composition.

### C4.4.4.3: Default ABI bounds via evaluator LIST_REL invariant
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The unproven arithmetic/tuple accumulator branch is eliminated. Remaining work is a standard recursion-matching induction plus a packaging corollary using already-proved local tuple boundary lemmas.
- Dependencies: C4.4.4.2
- Progress transition: `refinement`
- Carries progress/evidence from: C4.4.4.3, E0777, C4.4.4.2.1, C4.4.4.2.2, C4.4.4.2.3, C4.4.4.2.4
- Invalidates prior progress/evidence: C4.4.4.3 monolithic accumulator proof attempt in E0777

#### Progress note
Prior progress established that the theorem statement needed a SUM_MAP2 conjunct and that tuple LIST_REL helpers are closed. The failed accumulator proof does not carry forward tactically; the strengthened helper shape below replaces it while preserving the same task obligation.

#### Summary
Replace the brittle direct proof of `default_to_abi_enc_length_bound_eval` with a stronger local helper that follows `evaluate_type_ind`. The helper returns `default_to_abi_elem_bound_rel` for a single evaluated type and a `LIST_REL default_to_abi_elem_bound_rel` for the fresh suffix produced by `evaluate_types`. The exact theorem then follows by applying `default_to_abi_tuple_bound_from_LIST_REL`, `default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL`, and `default_to_abi_tuple_static_premise_from_LIST_REL`. Do not reason about `enc_tuple` accumulators in the `evaluate_types` cons case.

#### Description
This component owns only the local mutual default-ABI bound theorem around lines 651-759 of `semantics/prop/vyperTypeABIScript.sml`. The previous direct proof exposed goals about `enc_tuple (head_lengths (head::tail) 0) ...` with accumulated head/tail byte lists; that is the wrong interface for evaluator recursion. The recursion naturally constructs the semantic type-value list suffix, not an ABI tuple encoding accumulator. Prove that suffix as a `LIST_REL` of element bounds, then consume the tuple boundary lemmas already proved in C4.4.4.2.

#### Approach
First prove the stronger helper by `ho_match_mp_tac evaluate_type_ind`. The only list-accumulator work should be choosing `dtvs = []` in the nil case and `dtvs = tv::tail_dtvs` in the cons case; all ABI tuple encoding bounds belong in the single-type tuple constructor case or the final packaging theorem. Reuse the existing successful per-type case proof fragments for base, bytes, arrays, and fixed arrays, but route tuple cases through the LIST_REL tuple helper rather than through `enc_tuple_acc_length_bound_static_premise`.

#### Not to try
Do not keep patching the old monolithic `TRY` chain by adding more `qmatch_goalsub_abbrev_tac` or `FIRST_ASSUM` steps around `head_lengths`; E0777 showed this is a proof-interface problem, not a missing arithmetic rewrite. Do not unfold tuple encoding in the `evaluate_types` cons branch. Do not edit `vyper_to_abi_enc_length_bound` or downstream builtin/call files while this local theorem is unresolved.

#### Argument
For `evaluate_types tenv ts acc = SOME tvs`, the evaluator uses `acc` only as a reverse prefix of already-evaluated type values. The semantic invariant is therefore: there exists a fresh suffix `dtvs` such that `tvs = REVERSE acc ++ dtvs` and each source type in `ts` is related to its corresponding fresh type value by `default_to_abi_elem_bound_rel`. In the cons case, the recursive call on the tail with accumulator `tv::acc` yields `tvs = REVERSE (tv::acc) ++ tail_dtvs`; choose the caller's suffix as `tv::tail_dtvs`, and the equality reduces to `REVERSE acc ++ [tv] ++ tail_dtvs = REVERSE acc ++ (tv::tail_dtvs)`. For a tuple type in the single-type conjunct, the list IH gives exactly this `LIST_REL` for the elements, and `default_to_abi_tuple_bound_from_LIST_REL` supplies the tuple encoding bound. Once this stronger relation is proved, the public exact theorem is a corollary: unwrap the relation for the first conjunct, and for the list conjunct apply the tuple length, SUM_MAP2, and static ZIP boundary lemmas to the fresh suffix.

#### Definition design
Do not add a new datatype or executable definition. Reuse the existing local relation `default_to_abi_elem_bound_rel_def` as the proof interface: it packages `(evaluate_type tenv typ = SOME tv)`, the default ABI encoded-length bound, and the static bound needed by tuple encoders. Add one local theorem, before `default_to_abi_enc_length_bound_eval`, with a mutual statement over `evaluate_type`/`evaluate_types` that returns this relation and a `LIST_REL` of this relation. The failure sign for this design is any remaining need in the `evaluate_types` cons branch to unfold `contractABITheory.enc_def` or to instantiate `enc_tuple_acc_length_bound_static_premise`; if that happens, the proof has drifted back to the old bad interface.

#### Code structure
All edits are local to `semantics/prop/vyperTypeABIScript.sml` near the existing default ABI helper block. Insert the new local theorem immediately after `default_to_abi_tuple_bound_from_LIST_REL` and before `default_to_abi_enc_length_bound_eval`. Then replace the body of `default_to_abi_enc_length_bound_eval` with a short corollary proof from the new helper and the three C4.4.4.2 tuple boundary lemmas. Leave `vyper_to_abi_enc_length_bound` and builtin consumers untouched in this component.

### C4.4.4.3.1: Prove LIST_REL helper for evaluated default ABI elements
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: This is the natural induction invariant for `evaluate_type_ind`; the hard accumulator tuple goal disappears, and the remaining type cases can reuse existing local bound helpers.
- Dependencies: C4.4.4.2
- Checkpoint: yes
- Carries progress/evidence from: E0777, C4.4.4.2.1, C4.4.4.2.2, C4.4.4.2.3, C4.4.4.2.4

#### Progress note
E0777 contributes the diagnosis and confirms the strengthened list theorem needs a SUM bound later; C4.4.4.2 contributes the tuple boundary lemmas used in tuple type cases.

#### Summary
Add and prove a local mutual helper, tentatively named `default_to_abi_elem_bound_rel_eval`. The first conjunct proves `default_to_abi_elem_bound_rel tenv typ tv` from `evaluate_type tenv typ = SOME tv`. The second conjunct proves that `evaluate_types` returns `REVERSE acc` plus a fresh suffix related to the source types by `LIST_REL default_to_abi_elem_bound_rel`. This helper is the durable replacement for the brittle accumulator-level proof branch.

#### Statement
Theorem default_to_abi_elem_bound_rel_eval[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv ==>
     default_to_abi_elem_bound_rel tenv typ tv) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     ?dtvs.
       tvs = REVERSE acc ++ dtvs /\
       LIST_REL (default_to_abi_elem_bound_rel tenv) ts dtvs)

#### Approach
Use `ho_match_mp_tac evaluate_type_ind`, then simplify with `evaluate_type_def`, `default_to_abi_elem_bound_rel_def`, `default_to_abi_def`, `default_to_abi_list_MAP`, `default_to_abi_fields_MAP`, `vyper_to_abi_type_def`, `vyper_abi_size_bound_def`, `AllCaseEqs()`, `LET_THM`, and the byte length facts already used by the old proof. In the tuple type case, destruct the list IH for `evaluate_types ... []`, rewrite the suffix equality to obtain the actual element list, and apply `default_to_abi_tuple_bound_from_LIST_REL`; for the static conjunct use the proved length bound plus `vyper_to_abi_static_length_bound` after `vyper_to_abi_type_dynamic` relates source and ABI dynamicness. In the `evaluate_types` cons case, use the head type IH for `default_to_abi_elem_bound_rel tenv typ tv`, use the tail list IH, choose `tv::dtvs`, and solve with `LIST_REL` simplification and `REVERSE_DEF`/append simplification; there should be no ABI encoding subgoal in this branch.

#### Not to try
Do not include the exact theorem's tuple `LENGTH`, `SUM MAP2`, or static ZIP conclusions in this helper's `evaluate_types` conjunct. Those are consumer facts derivable from `LIST_REL`; putting them in the recursive invariant recreates the head-plus-tail accumulator problem. Do not instantiate `enc_tuple_acc_length_bound_static_premise` in this helper's list cons branch.

### C4.4.4.3.2: Derive exact default_to_abi_enc_length_bound_eval from LIST_REL helper
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 10
- Work units: 3
- Rationale: Once the LIST_REL helper is proved, the exact theorem is only projection and application of already-closed tuple boundary lemmas.
- Dependencies: C4.4.4.3.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C4.4.4.3, E0777
- Invalidates prior progress/evidence: old direct proof body of default_to_abi_enc_length_bound_eval

#### Progress note
This leaf completes the original theorem obligation using the repaired interface; previous direct proof progress is intentionally replaced by a short corollary proof.

#### Summary
Replace the body of `default_to_abi_enc_length_bound_eval` with a short proof from `default_to_abi_elem_bound_rel_eval`. The single-type conjunct unfolds the relation and projects the encoded-length bound. The list conjunct obtains `dtvs` and `LIST_REL`, then calls the tuple length, SUM_MAP2, and static ZIP boundary lemmas. This is the theorem named in the task and is a checkpoint because it unblocks the downstream default ABI packaging corollaries.

#### Statement
Theorem default_to_abi_enc_length_bound_eval[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv ==>
     LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
     vyper_abi_size_bound tenv typ) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     ?dtvs.
       tvs = REVERSE acc ++ dtvs /\
       LENGTH (enc (Tuple (vyper_to_abi_types tenv ts))
                   (ListV (MAP default_to_abi dtvs))) <=
       vyper_abi_size_bound_list tenv ts /\
       SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                            else static_length t)
                 (vyper_to_abi_types tenv ts) (MAP default_to_abi dtvs)) <=
       vyper_abi_size_bound_list tenv ts /\
       (!t v. MEM (t,v) (ZIP (vyper_to_abi_types tenv ts,
                               MAP default_to_abi dtvs)) /\
              ~is_dynamic t ==>
              LENGTH (enc t v) <= static_length t))

#### Approach
For conjunct 1, `drule (cj 1 default_to_abi_elem_bound_rel_eval)` and simplify with `default_to_abi_elem_bound_rel_def`. For conjunct 2, `drule (cj 2 default_to_abi_elem_bound_rel_eval)`, choose the returned `dtvs`, and keep the `LIST_REL` fact. Each of the three remaining conjuncts should be solved by applying respectively `default_to_abi_tuple_bound_from_LIST_REL`, `default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL`, and `default_to_abi_tuple_static_premise_from_LIST_REL`, with `default_to_abi_elem_bound_rel_def` unfolded only enough to match their expected lambda relation.

#### Not to try
Do not copy the old proof's large `TRY` blocks into this theorem. Do not prove tuple length or SUM facts by unfolding `contractABITheory.enc_def`; the whole point of C4.4.4.2 was to provide these boundary lemmas. If matching a tuple helper requires manual theorem plumbing, add a tiny local assertion converting `LIST_REL (default_to_abi_elem_bound_rel tenv) ts dtvs` to the helper's lambda relation by `fs[default_to_abi_elem_bound_rel_def]`, rather than instantiating every argument manually.

### C4.4.4.4: Derive compatibility default ABI length theorem and static corollary
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 40
- Work units: 2
- Rationale: Wrapper/corollary work is mechanical once both default ABI bridge inputs are available.
- Dependencies: C4.4.4.2.4, C4.4.4.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: prior C4.4.4.4 plan

#### Progress note
Adds explicit dependencies on the tuple-bound theorem and mutual invariant before the compatibility checkpoint.

#### Summary
Package the compatibility default ABI length theorem and static corollary only after C4.4.4.2.4 and C4.4.4.3. Closing this checkpoint authorizes direct ABI theorem work in C4.4.5.

#### Approach
Derive by projections/composition from the mutual invariant and tuple-bound bridge; build `vyperTypeABITheory` at the end.

#### Not to try
Do not start C4.4.5 before this checkpoint closes.

### C4.4.5: Prove direct mutual Vyper-to-ABI encoded-length theorem via local ABI-bound relations
- Kind: `boundary_lemma_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The remaining proof is standard once conversion success is factored into element/list/same/sparse ABI-value bound relations. Existing tuple/array static-premise lemmas and default_to_abi bounds cover the hard size arithmetic; the main new design point is the sparse IH predicate independent of the array length.
- Progress transition: `refinement`
- Carries progress/evidence from: E0781, C4.4.5

#### Progress note
E0781 validated that the old direct induction reaches only local ABI length-bound obligations and identified the brittle monolithic proof suffix. Prior progress on existing helpers in `vyperTypeABIScript.sml` is carried forward, but the proof strategy for the main theorem is refined into explicit local relation/boundary components.

#### Summary
- Replace the broad `TRY`/case-analysis suffix in `vyper_to_abi_enc_length_bound` with local relation infrastructure.
- Package encoded ABI values by their static Vyper type and runtime type, independent of their source Vyper value where possible.
- Prove tuple/dynamic-array/fixed-array consumers from these relations using existing `enc_*_static_premise` lemmas.
- Strengthen the mutual conversion theorem so list/same/sparse branches return reusable bound relations, then derive the exported theorem as a corollary.
- For sparse arrays, use a value-typed predicate independent of the current recursion length; do not require `sparse_has_type tv n sparse` in the recursive IH.

#### Description
This component owns only `semantics/prop/vyperTypeABIScript.sml` local helpers immediately preceding `vyper_to_abi_enc_length_bound` and the proof of that theorem. The theorem statement should remain the current source statement. Internal helper statements may be added locally. The final public theorem should expose exactly the four-conjunct length-bound theorem currently named `vyper_to_abi_enc_length_bound`, because downstream ABI encode builtin cases wait on it.

#### Approach
Proceed by adding the relation definitions, proving consumer boundary lemmas, proving the strengthened mutual theorem, then deriving the existing theorem. The induction variable for the strengthened theorem is exactly `vyper_to_abi_ind`; the strengthened sparse conjunct is what makes the induction align with the recursive call on `n`.

#### Not to try
Do not continue extending the current broad `TRY (Cases_on v >> gvs[...] >> ...)` suffix; E0781 shows it leaves heterogeneous goals and obscures the needed invariants. Do not formulate the sparse strengthened IH with `sparse_has_type tv n sparse`: in the `SUC n` case, the sparse map may contain key `n`, so `sparse_has_type tv (SUC n) sparse` does not imply `sparse_has_type tv n sparse`. Do not duplicate tuple/array encoding arithmetic in the main mutual proof; use the existing `enc_tuple_length_bound_static_premise`, `enc_dyn_array_same_length_bound_static_premise`, and `enc_fixed_array_same_length_bound_static_premise` through boundary lemmas.

#### Argument
The conversion functions recursively produce ABI values whose encoded length is bounded by the static ABI size computed from the Vyper type. Instead of re-proving tuple/array arithmetic in every evaluator branch, define an element relation `abi_av_bound_rel tenv typ tv av` that records `evaluate_type tenv typ = SOME tv` and the direct encoded length bound for the converted ABI value `av`. Define a heterogeneous list relation `abi_av_list_bound_rel tenv ts avs tvs` as the pointwise version of this element relation.

From the heterogeneous relation, tuple encoding is bounded by `vyper_abi_size_bound_list`: first derive the static-element premise required by `enc_tuple_length_bound_static_premise` using `vyper_to_abi_type_dynamic` and `vyper_to_abi_static_length_bound`, then prove the `SUM MAP2` bound by induction over the relation, mirroring the existing `default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL`. From an `EVERY (abi_av_bound_rel tenv typ tv) avs`, dynamic and fixed same-type arrays are bounded by the existing `enc_dyn_array_same_length_bound_static_premise` and `enc_fixed_array_same_length_bound_static_premise` plus `vyper_to_abi_embedded_head_bound`.

The strengthened mutual theorem follows `vyper_to_abi_ind`. Its first conjunct proves `abi_av_bound_rel` for each successful `vyper_to_abi`; its second proves `abi_av_list_bound_rel` for `vyper_to_abi_list`; its third proves `EVERY abi_av_bound_rel` and length preservation for `vyper_to_abi_same`; its fourth proves `EVERY abi_av_bound_rel` and `LENGTH avs = n` for `vyper_to_abi_sparse`. The sparse conjunct must assume only that every value occurring in `sparse` has type `tv`, not `sparse_has_type tv n sparse`, because the recursive call decrements `n` while the sparse map may still contain key `n`. The exported theorem is then a direct corollary: apply the relevant strengthened conjunct and the tuple/array boundary lemmas; convert `sparse_has_type` to the length-independent sparse value predicate for the public sparse conjunct.

#### Definition design
Add only local definitions in `vyperTypeABIScript.sml`:

1. `abi_av_bound_rel tenv typ tv av` packages `evaluate_type tenv typ = SOME tv` and `LENGTH (enc (vyper_to_abi_type tenv typ) av) <= vyper_abi_size_bound tenv typ`. Do not include source value/conversion success in this relation; the relation should also cover default ABI values used by sparse arrays.
2. `abi_av_list_bound_rel tenv ts avs tvs` is a recursive four-list relation matching `ts`, converted ABI values `avs`, and runtime type values `tvs` pointwise with `abi_av_bound_rel`.
3. `sparse_values_have_type tv sparse` is the length-independent predicate `!k v. MEM (k,v) sparse ==> value_has_type tv v`.

Boundary behavior expected from these definitions:
- `abi_av_bound_rel` plus non-dynamic ABI type should imply the static-length premise by `vyper_to_abi_type_dynamic` and `vyper_to_abi_static_length_bound`.
- `abi_av_list_bound_rel` should imply the tuple `SUM MAP2` bound, the static-element premise, and finally the tuple `enc` length bound.
- `EVERY (abi_av_bound_rel tenv typ tv) avs` should feed the existing same-type array static-premise lemmas.
- `sparse_values_have_type` should be stable across recursive calls of `vyper_to_abi_sparse`; this is the empirical failure sign to avoid if a proof tries to use `sparse_has_type tv n sparse` as the sparse IH premise.

#### Code structure
All edits for this subtree belong in `semantics/prop/vyperTypeABIScript.sml`, after the existing default ABI bound helpers (`default_to_abi_enc_length_bound`, `default_to_abi_static_enc_length_bound`) and before `vyper_to_abi_enc_length_bound`. Keep new definitions and helper theorems `[local]` unless a downstream file later explicitly needs them; the only exported output from this component should remain `vyper_to_abi_enc_length_bound`. Replace the current proof body of `vyper_to_abi_enc_length_bound` with a short compatibility proof from the strengthened local theorem. Do not move ABI arithmetic helpers to another theory or introduce dependencies outside the fresh stack.

### C4.4.5.1: Add local ABI-value bound and sparse-value predicates
- Kind: `definition_infrastructure`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: These are simple local recursive/predicate definitions with no hard proof content. They only package facts already present in existing goals and avoid source-value dependence for default sparse elements.

#### Progress note
New local infrastructure introduced to decompose the E0781 failing theorem.

#### Summary
- Define `abi_av_bound_rel` for a single ABI value produced for a Vyper type.
- Define `abi_av_list_bound_rel` for heterogeneous tuples/lists of ABI values.
- Define `sparse_values_have_type` as a length-independent sparse value typing predicate.
- Place definitions locally before `vyper_to_abi_enc_length_bound`.

#### Statement
```sml
Definition abi_av_bound_rel_def[local]:
  abi_av_bound_rel tenv typ tv av <=>
    evaluate_type tenv typ = SOME tv /\
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
      vyper_abi_size_bound tenv typ
End

Definition abi_av_list_bound_rel_def[local]:
  abi_av_list_bound_rel tenv [] [] [] = T /\
  abi_av_list_bound_rel tenv (typ::ts) (av::avs) (tv::tvs) =
    (abi_av_bound_rel tenv typ tv av /\
     abi_av_list_bound_rel tenv ts avs tvs) /\
  abi_av_list_bound_rel tenv _ _ _ = F
End

Definition sparse_values_have_type_def[local]:
  sparse_values_have_type tv sparse <=>
    !k v. MEM (k,v) sparse ==> value_has_type tv v
End
```

#### Approach
Add these definitions as local infrastructure. Keep `abi_av_bound_rel` deliberately minimal: static-length consequences should be derived by boundary lemmas, not stored in the definition. The list relation should recurse on all three lists so that `simp[abi_av_list_bound_rel_def]` gives length alignment by cases.

#### Not to try
Do not include `vyper_to_abi ... = SOME av` or `value_has_type tv v` in `abi_av_bound_rel`; sparse default entries have no source conversion premise but still need the same encoded-bound interface. Do not define sparse typing in terms of `n`, because the sparse conversion recursion decreases `n` while reusing the same sparse map.

### C4.4.5.2: Prove ABI-bound relation consumer lemmas for tuples and same-type arrays
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The proofs are standard inductions/reuses of existing static-premise encoding lemmas. The helper conclusions match the use sites in the strengthened mutual theorem and final compatibility corollary.
- Dependencies: C4.4.5.1

#### Progress note
New helper layer replacing monolithic arithmetic in the failed proof.

#### Summary
- Derive static-element premises from `abi_av_bound_rel` using dynamic/static type facts.
- Derive a `SUM MAP2` tuple bound from `abi_av_list_bound_rel`.
- Derive tuple `enc` length bound from the relation.
- Derive dynamic and fixed same-type array bounds from `EVERY abi_av_bound_rel`.

#### Statement
```sml
Theorem abi_av_bound_rel_static_premise[local]:
  !tenv typ tv av.
    abi_av_bound_rel tenv typ tv av /\
    ~is_dynamic (vyper_to_abi_type tenv typ) ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
    static_length (vyper_to_abi_type tenv typ)

Theorem abi_av_list_static_premise[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    !t av.
      MEM (t,av) (ZIP (vyper_to_abi_types tenv ts, avs)) /\ ~is_dynamic t ==>
      LENGTH (enc t av) <= static_length t

Theorem abi_av_list_SUM_MAP2_bound[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    SUM (MAP2 (\t av. if is_dynamic t then 32 + LENGTH (enc t av)
                          else static_length t)
              (vyper_to_abi_types tenv ts) avs) <=
    vyper_abi_size_bound_list tenv ts

Theorem abi_av_list_tuple_bound[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    LENGTH (enc (Tuple (vyper_to_abi_types tenv ts)) (ListV avs)) <=
    vyper_abi_size_bound_list tenv ts

Theorem abi_avs_dyn_array_bound[local]:
  !tenv typ tv avs.
    evaluate_type tenv typ = SOME tv /\
    EVERY (abi_av_bound_rel tenv typ tv) avs ==>
    LENGTH (enc (Array NONE (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    32 + LENGTH avs * vyper_abi_embedded_size tenv typ

Theorem abi_avs_fixed_array_bound[local]:
  !tenv typ tv n avs.
    evaluate_type tenv typ = SOME tv /\
    EVERY (abi_av_bound_rel tenv typ tv) avs /\
    LENGTH avs <= n ==>
    LENGTH (enc (Array (SOME n) (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    n * vyper_abi_embedded_size tenv typ
```

#### Approach
For `abi_av_bound_rel_static_premise`, unfold the relation, use `vyper_to_abi_type_dynamic` to convert the `is_dynamic` assumption to `~vyper_is_dynamic`, then use `vyper_to_abi_static_length_bound`. Prove the list static and SUM lemmas by induction on `ts` with cases on `avs` and `tvs`, simplifying `abi_av_list_bound_rel_def`, `vyper_to_abi_type_def`, and `vyper_abi_size_bound_def`. The tuple and array bounds should be short wrappers around existing `enc_*_static_premise` lemmas plus `vyper_to_abi_embedded_head_bound`.

#### Not to try
Do not manually expand `contractABITheory.enc_def` in these consumers except where an existing encoding lemma requires it; the existing `enc_*_static_premise` lemmas are the proof interface. Do not prove tuple length directly in the mutual theorem. Do not require `values_have_types` or source Vyper values in these lemmas; they are relation consumers only.

### C4.4.5.3: Prove sparse value-typing projection lemmas
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 20
- Work units: 2
- Rationale: These are small structural facts from `sparse_has_type_def`, `sparse_values_have_type_def`, and standard `ALOOKUP`/`MEM` behavior. They are needed only to align the sparse conversion induction.
- Dependencies: C4.4.5.1

#### Progress note
New sparse-specific helper replacing the unworkable length-indexed sparse IH.

#### Summary
- Convert public `sparse_has_type tv n sparse` into length-independent `sparse_values_have_type tv sparse`.
- Extract `value_has_type tv v` from `ALOOKUP sparse k = SOME v` under `sparse_values_have_type`.
- These lemmas allow the `vyper_to_abi_sparse` `SUC` case to use the recursive IH on the same sparse map.

#### Statement
```sml
Theorem sparse_has_type_values_have_type[local]:
  !tv n sparse.
    sparse_has_type tv n sparse ==> sparse_values_have_type tv sparse

Theorem sparse_values_have_type_ALOOKUP[local]:
  !tv sparse k v.
    sparse_values_have_type tv sparse /\ ALOOKUP sparse k = SOME v ==>
    value_has_type tv v
```

#### Approach
Prove `sparse_has_type_values_have_type` by induction on `sparse`, unfolding `value_has_type_def` only as needed for the recursive sparse predicate equations. For `ALOOKUP`, either use an existing `ALOOKUP_MEM` theorem if available or prove by induction on `sparse`; then apply `sparse_values_have_type_def`. Keep both lemmas local.

#### Not to try
Do not attempt to prove `sparse_has_type tv (SUC n) sparse ==> sparse_has_type tv n sparse`; it is false when the sparse map contains key `n`. Do not use sortedness or key bounds for this component; only value typing is needed.

### C4.4.5.4: Prove strengthened mutual Vyper-to-ABI conversion bound theorem
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 30
- Work units: 8
- Rationale: The proof follows the conversion recursion exactly and each branch now has a matching relation conclusion. Sparse recursion is de-risked by the length-independent sparse value predicate and default ABI bound helpers.
- Dependencies: C4.4.5.2, C4.4.5.3
- Checkpoint: yes

#### Progress note
This is the lynchpin replacement for the failed monolithic suffix in E0781.

#### Summary
- Use `ho_match_mp_tac vyper_to_abi_ind` with strengthened relation conclusions.
- First conjunct proves `abi_av_bound_rel` for successful single-value conversion.
- List conjunct proves `abi_av_list_bound_rel` for heterogeneous tuple/list conversion.
- Same and sparse conjuncts prove `EVERY abi_av_bound_rel` plus output length facts.
- Sparse branch uses `sparse_values_have_type`, `sparse_values_have_type_ALOOKUP`, and default ABI bounds for missing entries.

#### Statement
```sml
Theorem vyper_to_abi_bound_rel_strong[local]:
  (!tenv typ v av tv.
     vyper_to_abi tenv typ v = SOME av /\
     evaluate_type tenv typ = SOME tv /\
     value_has_type tv v ==>
     abi_av_bound_rel tenv typ tv av) /\
  (!tenv ts vs avs tvs.
     vyper_to_abi_list tenv ts vs = SOME avs /\
     LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ts tvs /\
     values_have_types tvs vs ==>
     abi_av_list_bound_rel tenv ts avs tvs) /\
  (!tenv typ vs avs tv.
     vyper_to_abi_same tenv typ vs = SOME avs /\
     evaluate_type tenv typ = SOME tv /\
     all_have_type tv vs ==>
     EVERY (abi_av_bound_rel tenv typ tv) avs /\ LENGTH avs = LENGTH vs) /\
  (!tenv typ tv n sparse avs.
     vyper_to_abi_sparse tenv typ tv n sparse = SOME avs /\
     evaluate_type tenv typ = SOME tv /\
     sparse_values_have_type tv sparse ==>
     EVERY (abi_av_bound_rel tenv typ tv) avs /\ LENGTH avs = n)
```

#### Approach
Start with `ho_match_mp_tac vyper_to_abi_ind`, then simplify `vyper_to_abi_def`, `value_has_type_def`, `abi_av_bound_rel_def`, `abi_av_list_bound_rel_def`, `sparse_values_have_type_def`, `AllCaseEqs()`, and `PULL_EXISTS`. In the base-type branch, use existing `vyper_to_abi_base_enc_length_bound`. In tuple/list/struct branches, use the list relation IH plus `abi_av_list_tuple_bound` to establish the first-conjunct length bound; in dynamic/fixed array branches use same/sparse IHs plus `abi_avs_dyn_array_bound`/`abi_avs_fixed_array_bound` and the relevant `vyper_abi_size_bound_def` arithmetic.

For `vyper_to_abi_list`, combine the head single-value IH and tail list IH directly into `abi_av_list_bound_rel_def`. For `vyper_to_abi_same`, combine the head single-value IH and tail same IH into `EVERY` and length. For `vyper_to_abi_sparse (SUC n)`, use the recursive sparse IH first; if `ALOOKUP sparse n = SOME v`, get `value_has_type tv v` from `sparse_values_have_type_ALOOKUP` and apply the single-value IH to the explicit conversion; if no value exists, add the default ABI element using `default_to_abi_enc_length_bound` to prove `abi_av_bound_rel_def`.

#### Not to try
Do not make this theorem conclude the final exported four length bounds directly for every conjunct; that recreates the 13-goal monolith. Do not unfold tuple/array `enc` arithmetic inside the induction except through C4.4.5.2 boundary lemmas. Do not use the public sparse premise `sparse_has_type tv n sparse` in this strengthened theorem; use `sparse_values_have_type tv sparse`.

### C4.4.5.5: Derive exported `vyper_to_abi_enc_length_bound` from the strengthened theorem
- Kind: `compatibility_corollary`
- Risk: 1
- Work priority: 40
- Work units: 2
- Rationale: Once the strengthened theorem is proved, the current public four-conjunct theorem is a short wrapper selecting the right relation consumer for each conjunct.
- Dependencies: C4.4.5.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0781

#### Progress note
This closes the originally active C4.4.5 obligation without changing its external statement.

#### Summary
- Keep the current source statement of `vyper_to_abi_enc_length_bound` unchanged.
- Replace the failed proof body with a compatibility proof from `vyper_to_abi_bound_rel_strong`.
- Use `abi_av_bound_rel_def` for the single-value conjunct.
- Use tuple/same-array/fixed-array boundary lemmas for list, same, and sparse conjuncts.
- Convert public sparse typing to `sparse_values_have_type` via C4.4.5.3.

#### Statement
```sml
Theorem vyper_to_abi_enc_length_bound:
  (!tenv typ v av tv.
    vyper_to_abi tenv typ v = SOME av /\
    evaluate_type tenv typ = SOME tv /\
    value_has_type tv v ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
    vyper_abi_size_bound tenv typ) /\
  (!tenv ts vs avs tvs.
    vyper_to_abi_list tenv ts vs = SOME avs /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ts tvs /\
    values_have_types tvs vs ==>
    LENGTH (enc (Tuple (vyper_to_abi_types tenv ts)) (ListV avs)) <=
    vyper_abi_size_bound_list tenv ts) /\
  (!tenv typ vs avs tv.
    vyper_to_abi_same tenv typ vs = SOME avs /\
    evaluate_type tenv typ = SOME tv /\
    all_have_type tv vs ==>
    LENGTH (enc (Array NONE (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    32 + LENGTH vs * vyper_abi_embedded_size tenv typ) /\
  (!tenv typ tv n sparse avs.
    vyper_to_abi_sparse tenv typ tv n sparse = SOME avs /\
    evaluate_type tenv typ = SOME tv /\
    sparse_has_type tv n sparse ==>
    LENGTH (enc (Array (SOME n) (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    n * vyper_abi_embedded_size tenv typ)
```

#### Approach
Prove the conjunctions independently. For the first, apply conjunct 1 of `vyper_to_abi_bound_rel_strong` and unfold `abi_av_bound_rel_def`. For the second, apply conjunct 2 then `abi_av_list_tuple_bound`. For the third, apply conjunct 3 then `abi_avs_dyn_array_bound`, rewriting `LENGTH avs = LENGTH vs`. For the fourth, derive `sparse_values_have_type` from `sparse_has_type`, apply conjunct 4, then use `abi_avs_fixed_array_bound` with `LENGTH avs = n`.

#### Not to try
Do not re-run `ho_match_mp_tac vyper_to_abi_ind` in this theorem; all induction belongs in C4.4.5.4. Do not leave the old `FAIL_TAC "probe_c44_vyper_to_abi_enc_length_bound"` or broad `TRY` suffix in place. Do not alter the theorem statement unless HOL reports a genuine falsehood after the strengthened local theorem is proved.

### C4.4.6: Discharge ABI encode resumes in `well_typed_type_builtin_success_type`
- Kind: `proof`
- Risk: 2
- Work priority: 60
- Work units: 5
- Rationale: Builtin cases are low-risk only once the direct encoded-length theorem is available.
- Dependencies: C4.4.5
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: prior C4.4.6 plan

#### Progress note
Adds explicit dependency on C4.4.5 so builtin discharge waits for the direct encoded-length theorem.

#### Summary
Discharge builtin ABI encode proof resumes after C4.4.5. This should be the last ABI/builtin step in this local chain.

#### Approach
Use the direct encoded-length theorem exported by C4.4.5 in the finite builtin cases.

#### Not to try
Do not reopen ABI tuple/default algebra in builtin proof branches.

### C4.5: Close raw-call return well-formedness and Env/MsgGas support
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: After C4.4, the remaining builtin-file support is localized. `raw_call_return_type_well_formed` is arithmetic over `word_size`, `type_slot_size`, and the cases of `raw_call_return_type_def`; Env/MsgGas support is constructor-specific and should not require evaluator induction.
- Dependencies: C4.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C4.5

#### Progress note
This leaf is no longer beginable before C4.4. Its dependency is intentional source-order scheduling: close the type-builtin success theorem first, then edit the later raw-call/Env support region.

#### Summary
- Remove the cheat in `raw_call_return_type_well_formed`.
- Audit/close the localized Env/MsgGas builtin support obligations reachable from `vyperSemanticsHolTheory`.
- Keep proofs in the builtin layer; do not duplicate evaluator/call case analysis.
- Use `word_size_le` and simple DIV/arithmetic facts for raw-call bounds.
- Checkpoint after `holbuild build vyperTypeBuiltinsTheory` succeeds and no C4.5 cheats remain.

#### Description
The raw-call theorem currently has a single cheated arithmetic subgoal after unfolding `raw_call_return_type_def`, `well_formed_type_def`, `evaluate_type_def`, and `type_slot_size_def`. The proof should show the dynamic bytes return bound is well-formed under `flags.rcf_max_outsize < dimword(:256)`, using the already-proved `word_size_le` and the definition of `word_size`. Env/MsgGas issues mentioned in the task are part of the same builtin support layer; handle only those still reachable/cheated in current source.

#### Statement
Primary known source obligation:
```sml
Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)
```
Also close any same-layer reachable Env/MsgGas support theorem(s) in `vyperTypeBuiltinsScript.sml` that still contain `cheat`/suspended proof text and are prerequisites for call/expression consumers.

#### Approach
First replace the raw-call cheat by strengthening the local arithmetic enough to prove all branches after case-splitting `flags`; keep any new helper near `word_size_le`. Expected shape: derive `word_size n ≤ n`, split on the branch that compares `word_size n < n`, and use the max-outsize/dimword hypothesis to discharge `type_slot_size`/well-formed natural-number bounds. Then grep/audit only `vyperTypeBuiltinsScript.sml` for remaining reachable Env/MsgGas cheats; close them by constructor rewriting using `env_item_type_def`/current context hypotheses, preserving any existing premise excluding `MsgGas` unless a checked theorem requires otherwise.

#### Not to try
Do not remove the `item <> MsgGas` premise from generic Env helper theorems just to make rewriting easier; the task notes this as a known issue, not permission to broaden a false helper. Do not start call-wrapper proofs under C5 from this leaf. Do not unfold the statement evaluator or raw-call expression evaluator here; consumers should use this well-formedness/support boundary.

### C5: Call wrapper soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: Call wrappers are downstream consumers of completed expression/statement/builtin soundness and function signature consistency; no new evaluator induction is required.
- Required for completion: yes
- Dependencies: C2.8, C4.5
- Progress transition: `refinement`
- Carries progress/evidence from: old C5

#### Progress note
C5 remains downstream; it must not be used by C2 internal-call proof.

#### Summary
- Prove call wrapper theorems in `vyperTypeCallSoundnessScript.sml`.
- External/special wrappers consume C2/C4 expression soundness.
- Internal no-TypeError and preservation wrappers consume completed statement/body soundness.
- No new evaluator induction or semantic case duplication.

#### Statement
Current source theorem names:
```sml
internal_call_no_type_error
internal_call_type_preservation
external_call_no_type_error
special_call_no_type_error
```

#### Approach
Prove wrappers as projections/corollaries. Use `functions_well_typed_body` or its repaired non-circular analogue, expression soundness for call expressions, and statement body soundness; avoid redoing call evaluator case analysis except for the one-step wrapper shape if current theorem statement is exactly an `eval_expr` call.

#### Not to try
Do not feed these wrappers back into `vyperTypeStmtSoundnessScript.sml`. Do not duplicate C2.7 call-frame proof internals unless a small projection helper is missing.

#### Argument
The call wrappers are API-facing corollaries of the completed mutual expression/statement soundness and function consistency facts. External and special calls reduce to the expression soundness of the corresponding call expressions. Internal calls use function signature/body typing to instantiate statement-list soundness for the callee body, then project no-TypeError or success preservation from the joint invariant. The wrappers preserve the frozen public behavior but are not proof drivers for the mutual theorem.

#### Definition design
The wrapper interface should expose the existing names `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, and `special_call_no_type_error`. If a wrapper cannot be proved by projection, add a projection lemma from C2/C4 with the exact conclusion rather than unfolding evaluator internals here.

#### Code structure
Edit `semantics/prop/vyperTypeCallSoundnessScript.sml`. It may import completed `vyperTypeStmtSoundness` and `vyperTypeBuiltins`, but no earlier theory may import this file for C2 work.

### C5.1: External and special call no-TypeError wrappers
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: These wrappers avoid internal function body recursion and reduce to completed expression/call-target facts.
- Progress transition: `refinement`
- Carries progress/evidence from: old C5.1

#### Progress note
Scheduled after C2/C4 through parent dependencies.

#### Summary
- Prove `external_call_no_type_error` and `special_call_no_type_error`.
- Consume C2 expression soundness and C4 raw/special-call boundary facts.
- Keep proofs as wrapper projections.

#### Statement
```sml
Theorem external_call_no_type_error: ...
Theorem special_call_no_type_error: ...
```

#### Approach
Instantiate the expression soundness theorem on the relevant `Call` expression and project `no_type_error_eval`. Use the target discriminating assumptions to select the external/special call case; any target-specific fact should already be in C4/C2.

#### Not to try
Do not unfold raw-call or builtin definitions here.

### C5.2: Internal call no-TypeError wrapper
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Existing function body typing and completed statement soundness supply internal-call no-TypeError; proof should be a projection from joint invariants.
- Dependencies: C5.1
- Progress transition: `refinement`
- Carries progress/evidence from: old C5.2

#### Progress note
Downstream wrapper only; does not affect C2.

#### Summary
- Prove `internal_call_no_type_error`.
- Use completed expression/internal-call mutual soundness and function consistency.
- Preserve current theorem statement unless source repair is needed and non-frozen.

#### Statement
```sml
Theorem internal_call_no_type_error: ...
```

#### Approach
Instantiate `eval_all_type_sound_mutual`/expression no-TypeError wrapper for `Call ty (IntCall (src,fn)) args drv`, or use the completed internal-call expression resume via a smaller expression theorem. Use `fn_sig_argument_bounds`/`functions_well_typed_body` only if the current wrapper statement requires explicit body facts.

#### Not to try
Do not redo the body evaluation proof; C2.7 owns it.

### C5.3: Internal call success preservation wrapper
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: This is the preservation projection counterpart to C5.2 and should reuse the same decomposition.
- Dependencies: C5.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C5.3

#### Progress note
Checkpoint because public wrappers depend on call preservation.

#### Summary
- Prove `internal_call_type_preservation`.
- Project state and expression result typing from completed joint soundness.
- Avoid fresh evaluator induction.

#### Statement
```sml
Theorem internal_call_type_preservation: ...
```

#### Approach
Use the same instantiated expression/call soundness theorem as C5.2, then specialize to the `INL` success result and project `state_well_typed` plus `expr_runtime_typed`. Add a small projection lemma if the joint theorem conclusion is inconvenient.

#### Not to try
Do not weaken the preservation conclusion or ignore account/env invariants if the current source theorem needs them downstream.

### C6: Public fresh soundness wrapper surface
- Kind: `proof_group`
- Risk: 2
- Work priority: 60
- Work units: 0
- Rationale: The frozen public behaviors are projections of the subsystem joint invariants once assignment/statement/call/builtin layers are cheat-free.
- Required for completion: yes
- Dependencies: C5.3, C3.3, C4.5
- Progress transition: `refinement`
- Carries progress/evidence from: old C6

#### Progress note
C6 remains the public surface layer. It may adjust internal helper use but must keep wrappers equivalent in strength to the TASK list.

#### Summary
- Prove/repair public wrapper theorems in `vyperTypeSoundnessNewScript.sml`.
- Preserve frozen public behavior: no well-typed TypeError and preservation for success/exceptional results.
- Wrappers should be projections, not new evaluator inductions.
- Any missing projection indicates a C2/C5 helper gap to repair.

#### Statement
Public wrappers equivalent in strength to:
```sml
typed_stmts_no_type_error
typed_stmts_success_preserves_state_env
typed_stmts_exception_preserves_state_and_return_type
typed_expr_no_type_error
typed_expr_success_preserves_type
typed_callable_body_no_type_error
```

#### Approach
For each public wrapper, instantiate the strongest available joint theorem and simplify the result predicates. If a public theorem has a legacy statement shape, prove a stronger internal lemma and derive the legacy-compatible corollary.

#### Not to try
Do not weaken frozen public behavior. Do not start a parallel soundness induction in the public file.

#### Argument
Public soundness follows by instantiating the completed fresh-stack joint invariants for statements, expressions, callable bodies, assignment/call helpers, and projecting the user-facing conclusions. No public theorem should require new semantic case analysis: statement no-TypeError and preservation come from C2; expression no-TypeError/success typing from C2/C4; callable body no-TypeError from C5/C2 function body soundness; assignment/call wrappers from C1/C5.

#### Definition design
The public surface must expose wrappers equivalent in strength to `typed_stmts_no_type_error`, `typed_stmts_success_preserves_state_env`, `typed_stmts_exception_preserves_state_and_return_type`, `typed_expr_no_type_error`, `typed_expr_success_preserves_type`, and `typed_callable_body_no_type_error`. Internal theorem names/statements may be strengthened or renamed, but compatibility corollaries with these public names/strength must remain. Failure sign: a public wrapper proof unfolding evaluator definitions rather than projecting a completed joint theorem.

#### Code structure
Edit only the public fresh surface `semantics/prop/vyperTypeSoundnessNewScript.sml` and small projection lemmas in immediate prerequisite theories if necessary. Do not edit retired old theories unless C7 proves they are still imported.

### C6.1: Prove/repair the six public wrapper theorems
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: After subsystem theorems are complete, wrapper projection is standard; failures should expose only missing projection lemmas, not new architecture.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C6.1

#### Progress note
Scheduled after C5/C3/C4 through parent dependencies.

#### Summary
- Close all public wrapper cheats in `vyperTypeSoundnessNewScript.sml`.
- Preserve the six frozen public behaviors listed by the TASK.
- Use projection lemmas from C2/C5 rather than evaluator unfolding.
- Checkpoint before final full-stack validation.

#### Statement
Current source-authoritative public wrapper theorems corresponding to the six TASK names/behaviors.

#### Approach
Prove each wrapper by `drule`/`irule` against the relevant subsystem theorem and simplify definitions of public result predicates. If a theorem statement is awkward but non-frozen internally, add a stronger helper in the lower layer and keep the public wrapper equivalent in strength.

#### Not to try
Do not alter public theorem strength to avoid side conditions. Do not include old retired-stack theorems in the proof path.

### C7: Final `vyperSemanticsHolTheory` zero-CHEAT validation
- Kind: `validation`
- Risk: 1
- Work priority: 70
- Work units: 3
- Rationale: Mechanical final build/audit; any remaining warning gives concrete evidence for a small follow-up replan.
- Required for completion: yes
- Dependencies: C6.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C7

#### Progress note
Final completion criterion remains unchanged.

#### Summary
- Run `holbuild build vyperSemanticsHolTheory`.
- Confirm zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.
- If warnings remain, identify the exact reachable theory/theorem and escalate for a focused component.
- Do not clean unrelated repository files as part of this validation.

#### Statement
```sh
holbuild build vyperSemanticsHolTheory
```
succeeds with zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.

#### Approach
Run the build exactly as the TASK requires and inspect CHEAT warnings. Use a scoped dependency/reachability audit to distinguish in-scope fresh-stack warnings from old retired theories; only escalate in-scope reachable obligations.

#### Not to try
Do not use direct HOL. Do not stage or modify untracked scratch files during validation.
