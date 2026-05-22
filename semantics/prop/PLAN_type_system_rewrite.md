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

### C2: Statement and expression mutual soundness cases
- Kind: `proof_group`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Completed structural/assignment/attribute/Pop work is preserved; remaining expression resumes are small consumers after C3/C4 boundary lemmas are proved. The scheduling defect is repaired by explicit cross-top-level dependencies and later priorities.
- Required for completion: yes
- Dependencies: C1
- Progress transition: `refinement`
- Carries progress/evidence from: C2, C2.0, C2.1, C2.2, C2.3, E0616, E0708, E0711, E0729
- Invalidates prior progress/evidence: old C2.4/C2.5 scheduling before C4 boundary closure

#### Progress note
This rebase preserves completed C2 evidence but changes the remaining C2 frontier ordering. C2.4/C2.5/C2.6 are now consumers of C4 boundary facts, and C2.7 internal-call work remains after the non-circular helpers are available.

#### Summary
- Carries forward completed statement/expr mutual proof work through Expr_Attribute and Expr_Pop.
- Remaining C2 work is limited to `Expr_Builtin`, `Expr_TypeBuiltin`, external/special call expression resumes, internal-call support, and a local audit.
- C2 consumers are explicitly blocked on C4 builtin/type-builtin/raw-call boundary leaves.
- Statement soundness must consume subsystem boundaries, not reprove builtin/call/assignment semantics.
- After C2.8, `vyperTypeStmtSoundnessTheory` should build without local cheats.

#### Description
This parent owns only the current source-authoritative remaining statement/expression cheats. Completed old fine-grained C2 subtrees are collapsed below as carry-forward components so the frontier is no longer over-decomposed or stale.

#### Statement
Current source-authoritative `eval_all_type_sound_mutual` in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, with no cheated/suspended cases remaining after C2.8.

#### Approach
Work through remaining C2 leaves only after their C3/C4 dependencies close. In each resume, unfold `well_typed_expr_def` once for static facts, unfold `evaluate_def` once for the semantic shape, apply IHs to recursive evaluations, and finish with the boundary theorem named in the leaf.

#### Not to try
Do not use cheated C4 boundary theorems as completion evidence. Do not duplicate builtin/type-builtin/raw-call case analysis in `vyperTypeStmtSoundnessScript.sml`. Do not start a second induction over the evaluator; strengthen/extract boundary helpers instead.

#### Argument
The mutual theorem follows the evaluator recursion. For ordinary expression constructors, the proof sequence is: unfold the evaluator one step, apply the relevant IH to subexpressions/targets/statement lists, propagate error cases using the IH's `no_type_error_result`, and for successful subcomputations invoke a subsystem boundary theorem for the non-recursive operation. Builtin and type-builtin branches have no additional evaluator recursion after `eval_exprs`; therefore their soundness is exactly the C4 boundary theorem plus expression-list runtime typing. External/special call-target branches similarly evaluate arguments and drivers, then consume raw-call/special-target no-TypeError facts from C4. Internal calls are the only remaining branch that evaluates a Vyper body, so it needs call-frame extraction and environment consistency helpers before using the mutual statement IH on the callee body.

#### Definition design
The C2 proof interface must stay at subsystem boundaries: `exprs_runtime_typed` supplies evaluated argument type-values and `LIST_REL value_has_type`; C4 supplies builtin/type-builtin/raw-call no-TypeError and success typing; C1/C3 supplies assignment no-TypeError/preservation; call-frame helpers expose callee body typing and frame consistency. A failure sign is any need to unfold `evaluate_builtin_def`, `evaluate_type_builtin_def`, raw-call internals, or assignment evaluator definitions inside the statement mutual proof. If a C4 theorem statement does not match the consumer, replan the C4 boundary theorem rather than adding case analysis in C2.

#### Code structure
Edit remaining `Resume eval_all_type_sound_mutual[...]` blocks in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Put builtin/type-builtin/raw-call constructor proofs in `vyperTypeBuiltinsScript.sml` (C4), update-binop assignment helper proofs in `vyperTypeStatePreservationScript.sml`/`vyperTypeBuiltinsScript.sml` as already located (C3), and non-circular call-frame helper lemmas either before the mutual finalization in `vyperTypeStmtSoundnessScript.sml` or in a prerequisite fresh theory if import cycles require it. Do not import `vyperTypeCallSoundness` into statement soundness.

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

### C2.4: Close `Expr_Builtin` statement-soundness case using completed builtin boundaries
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: Once C4.2 is cheat-free, this resume is standard evaluator/IH sequencing and builtin boundary application.
- Dependencies: C2.3, C4.2, C3.3
- Supersedes: C2.4
- Progress transition: `replacement`
- Invalidates prior progress/evidence: stale C2.4 dossier entries for unrelated iterator/Append/assignment audits, old C2.4 scheduling before C4.2

#### Progress note
C2.4 keeps the current-source obligation at `Resume eval_all_type_sound_mutual[Expr_Builtin]` but is rescheduled after C4.2. Prior unrelated C2.4 evidence does not count for this proof.

#### Summary
- Replace `Resume eval_all_type_sound_mutual[Expr_Builtin]: cheat QED`.
- Start only after C4.2 and C3.3 are closed without cheats.
- Use `eval_exprs` IH for arguments and C4.2 for builtin execution.
- Do not unfold builtin constructors in statement soundness.

#### Description
This component repairs the earlier local rebase: the proof is a consumer, not the owner of builtin semantics. C3.3 is included as a dependency so the expression theorem does not close through assignment/update-path CHEAT warnings indirectly reachable in the same theory stack.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Builtin]:
  ...
QED
```

#### Approach
Unfold `well_typed_expr_def` once for the `Builtin` constructor and `evaluate_def` once to expose `eval_exprs` followed by `evaluate_builtin`. Apply the `eval_exprs` IH; in the successful argument case unpack `exprs_runtime_typed` into evaluated argument type-values and `LIST_REL value_has_type`, then use `well_typed_builtin_app_no_type_error` and `well_typed_builtin_app_success_type`. Builtins are pure, so state after the builtin call is the state returned by `eval_exprs`.

#### Not to try
Do not expand `evaluate_builtin_def` or split on builtin constructors here. Do not use C4.2 while it still contains CHEAT warnings.

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

### C4: Builtin, type-builtin, and raw/special-call boundary soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: Builtin residuals are finite constructor proofs once C3 binop facts and current ABI bound repairs are available. C4 must close before C2 builtin/type-builtin/call consumers start.
- Required for completion: yes
- Dependencies: C3.1
- Progress transition: `refinement`
- Carries progress/evidence from: old C4
- Invalidates prior progress/evidence: old scheduling that placed C2.4/C2.5 before C4

#### Progress note
C4 is promoted before remaining C2 consumer leaves. C4.2/C4.3/C4.4/C4.5 are strict prerequisites for C2.4/C2.5/C2.6.

#### Summary
- Owns all builtin/type-builtin/raw-call boundary facts that statement soundness consumes.
- Must prove generic builtin no-TypeError/success typing, type-builtin no-TypeError, ABI encode success typing, and raw-call/Env MsgGas support.
- C2 must not unfold builtin semantics while C4 remains incomplete.
- Constructor-specific arithmetic/ABI facts belong here or in existing lower helper theories.

#### Description
This component repairs the cross-top-level scheduling bug. The executor must complete C4 leaves before beginning C2.4/C2.5/C2.6.

#### Statement
Current source-authoritative C4 theorems and suspended branches, especially:
```sml
well_typed_builtin_app_no_type_error
well_typed_builtin_app_success_type
well_typed_type_builtin_no_type_error
well_typed_type_builtin_success_type
```
plus raw-call/Env MsgGas helpers needed by expression-call consumers.

#### Approach
Proceed by boundary theorem: static typing first if needed, then generic builtin, then type-builtin no-TypeError, then ABI success branches, then raw-call/Env support. Use C3.1 for binary-operation builtins rather than reopening binop definitions.

#### Not to try
Do not prove C2 `Expr_Builtin` or `Expr_TypeBuiltin` by expanding builtin semantics. Do not leave ABI encode branches cheated and then use the resulting theorem in C2.

#### Argument
Builtin evaluation is non-recursive after arguments have been evaluated. Therefore soundness is by finite case analysis on the builtin/type-builtin target plus static typing inversion. Well-typed argument lists provide length/type constraints and `LIST_REL value_has_type` for runtime values. For ABI encode/decode and raw-call sizing, current typing predicates include the required bounds, so success typing follows from ABI helper lemmas and word/slot arithmetic. Env/account builtins consume `context_well_typed` and `accounts_well_typed`; `MsgGas` must be handled in the builtin boundary, not excluded in statement soundness unless the static rule excludes it.

#### Definition design
Export boundary theorems that match C2 consumers: `well_typed_builtin_app_no_type_error`, `well_typed_builtin_app_success_type`, `well_typed_type_builtin_no_type_error`, and `well_typed_type_builtin_success_type`. If raw-call/special targets need helper facts, package them as no-TypeError/success-typing lemmas over the static well-typed call-target predicate and already-evaluated arguments. Failure signs are C2 needing `evaluate_builtin_def`, `evaluate_type_builtin_def`, ABI encoding internals, or Env/MsgGas case splits.

#### Code structure
Edit `semantics/prop/vyperTypeBuiltinsScript.sml` for builtin/type-builtin/binop/raw-call support. Static typing suspended cases, if any are still reachable and imported, belong in their existing builtin typing source before C4.2 consumes them. Do not put these proofs in `vyperTypeStmtSoundnessScript.sml`. Keep compatibility theorem names if callers already use them.

### C4.1: Close reachable static builtin-typing suspended cases
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Only needed if current build/audit shows these suspended static cases are reachable; otherwise the leaf should record a local audit that no reachable CHEAT remains there. The proof work is finite constructor typing.
- Progress transition: `refinement`
- Carries progress/evidence from: old C4.1

#### Progress note
Scheduled before C4.2 so builtin boundary proofs do not depend on static typing scaffolding.

#### Summary
- Audit and close reachable static builtin-typing suspended/cheated cases.
- If no reachable cheats exist, document the grep/build evidence and mark complete.
- Use constructor inversion over builtin typing definitions.
- Keep the scope limited to fresh-stack theories reachable from `vyperSemanticsHolTheory`.

#### Statement
Current reachable suspended/cheated static builtin-typing obligations, if any, in fresh-stack builtin typing sources.

#### Approach
Run the scoped grep/build audit first. For any reachable suspended case, unfold the static typing definition for that constructor and prove the finite side conditions; otherwise close the component with audit evidence only.

#### Not to try
Do not clean old retired theories unless they are imported transitively by `vyperSemanticsHolTheory`.

### C4.2: Close generic builtin no-TypeError and success typing boundary
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: The theorem skeleton exists and most constructors are already handled; after C3.1, remaining branches are finite builtin constructor cases with existing helper lemmas.
- Dependencies: C4.1, C3.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C4.2

#### Progress note
This checkpoint gates C2.4. C2.4 must not begin until this theorem is proved without CHEAT warnings.

#### Summary
- Prove `well_typed_builtin_app_no_type_error` and `well_typed_builtin_app_success_type` without cheats.
- Include Env/Acc and ordinary builtins whose expression branch uses `Builtin`.
- Consume C3.1 for binop-related cases.
- Export theorem statements that let C2.4 avoid builtin constructor analysis.

#### Statement
```sml
Theorem well_typed_builtin_app_no_type_error:
  ...
Theorem well_typed_builtin_app_success_type:
  ...
```

#### Approach
Invert `well_typed_builtin_app` to obtain argument length/type constraints and use `LIST_REL value_has_type` to recover concrete value constructors. Apply existing per-builtin helpers (`Env_builtin_*`, `Acc_builtin_sound`, bytes/crypto/default/conversion helpers) and C3.1 for binops. Keep separate no-TypeError and success-typing outputs if current source names require it, but prove them from shared local case-analysis facts where convenient.

#### Not to try
Do not prove the statement expression branch here. Do not hide residual ABI/type-builtin cases under this theorem if they are actually owned by C4.3/C4.4.

### C4.3: Prove type-builtin no-TypeError boundary
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: No-TypeError for type builtins is finite case analysis using static argument constraints, context well-typedness, and ABI helper no-TypeError facts.
- Dependencies: C4.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C4.3

#### Progress note
This checkpoint is a strict prerequisite for C2.5.

#### Summary
- Replace the cheat in `well_typed_type_builtin_no_type_error`.
- Handle extract32, ABI decode/encode, and other type-builtin constructors at the boundary layer.
- No success typing is required here except as needed to prove no-TypeError.
- C2.5 may consume this theorem only after it is cheat-free.

#### Statement
```sml
Theorem well_typed_type_builtin_no_type_error:
  ...
```

#### Approach
Invert the type-builtin well-typed predicate to get argument lengths and evaluated type facts. Split on the type-builtin constructor; show each evaluation either succeeds or raises only runtime/non-TypeError errors under the static constraints. Reuse ABI no-TypeError lemmas rather than unfolding encoders where available.

#### Not to try
Do not postpone ABI encode no-TypeError to C2.5. Do not use broad simplification that expands all ABI encode/decode internals unless a branch-specific helper is missing.

### C4.4: Prove type-builtin success typing, including ABI encode branches
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 8
- Rationale: The task notes the old ABI encode bound gap has been repaired by current typing predicates; remaining branches are finite consumers of ABI bound and value typing lemmas.
- Dependencies: C4.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C4.4

#### Progress note
This checkpoint is a strict prerequisite for C2.5 and public expression success typing.

#### Summary
- Replace cheated/suspended branches in `well_typed_type_builtin_success_type`, especially `abi_encode`, `encode_tuple`, and `encode_tuple_nowrap`.
- Use the repaired ABI bound side conditions in the current typing predicate.
- Preserve existing theorem name for C2 consumers.
- Keep ABI arithmetic localized to C4.

#### Statement
```sml
Theorem well_typed_type_builtin_success_type:
  ...
Resume well_typed_type_builtin_success_type[abi_encode]: ... QED
Resume well_typed_type_builtin_success_type[encode_tuple]: ... QED
Resume well_typed_type_builtin_success_type[encode_tuple_nowrap]: ... QED
```

#### Approach
For each suspended ABI success branch, invert the static type-builtin predicate to obtain evaluated result type and encoding-size/bound premises. Apply existing ABI typing lemmas to show the returned bytes/tuple value has the expected `type_value`; if a lower ABI lemma has the wrong conclusion, add a local boundary lemma in this file matching the branch use site.

#### Not to try
Do not manually prove byte-length arithmetic in `vyperTypeStmtSoundnessScript.sml`. Do not weaken the success theorem to omit ABI encode typing; public expression success preservation needs it.

### C4.5: Close raw-call return well-formedness and Env/MsgGas support
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 8
- Rationale: The remaining raw-call theorem is localized arithmetic over word/slot sizes, and Env/MsgGas issues are constructor-specific builtin facts. These are strict prerequisites for external/special call expression consumers.
- Dependencies: C4.2, C4.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C4.5

#### Progress note
This checkpoint gates C2.5/C2.6 where type-builtin/raw/special-call expression branches consume these facts.

#### Summary
- Prove remaining raw-call return type well-formedness/no-TypeError support.
- Resolve Env/MsgGas builtin support in the boundary layer.
- Package facts so external/special call expression resumes can be short consumers.
- Do not move raw-call arithmetic into statement soundness.

#### Statement
Current source theorem(s) around raw-call return type well-formedness and Env/MsgGas builtin no-TypeError/success typing, including any remaining cheat near the end of `vyperTypeBuiltinsScript.sml`.

#### Approach
Inspect the exact remaining cheat after C4.2-C4.4. For raw-call, use evaluated return type and word/slot-size lemmas to prove well-formedness/no-TypeError; for Env MsgGas, either extend the existing `Env_builtin_no_type_error`/success theorem to cover `MsgGas` under `context_well_typed` or prove a separate helper consumed by the generic builtin theorem.

#### Not to try
Do not exclude `MsgGas` in C2 unless the current static typing rule truly excludes it. Do not add ad-hoc assumptions to public wrappers; fix the boundary theorem or static rule if a source-authoritative probe shows a real spec gap.

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
