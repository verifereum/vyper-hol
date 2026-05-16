# STATE_type_system_rewrite
Updated: 2026-05-16

## Cursor
- component: C5.4.5
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: 1) Delete or replace assign_target_INL_imp_assignable_context_stmt_ind (line 420) + assign_target_INL_imp_assignable_context_stmt (line 447) - grep confirmed zero consumers per LEARNINGS. 2) Patch Assign resume line 1113 cheat: use assign_target_no_type_error from C4, deriving assign_operation_matches_target_shape via assign_operation_matches_target_shape_Replace_from_typed and assign_target_assignable_context via target_runtime_typed_imp_assignable_context. 3) Patch Assign resume line 1119 cheat: materialise TypeError sub-case. 4) Patch AugAssign resume line 1141 cheat: rewrite using base-target IH and new bridges. 5) Audit remaining cheats in other Resume blocks within C5 scope.
- expected_goal_shape: Assign INL-success branch after assign_target: need assign_target_no_type_error premises (assign_operation_matches_target_shape + assign_target_assignable_context) derivable from target_runtime_typed + env_consistent. AugAssign needs similar plus update-binop typing.
- verify_with: holbuild(targets=['vyperTypeStmtSoundnessTheory'])

## If This Fails
- If assignable_context bridge fails in Assign branch, check that env_consistent is preserved at the right state (st3 for assign_target call). If AugAssign proof structure is wrong, escalate to plan_oracle for C5.4.5 restructuring.

## Do Not Retry
- metis_tac[env_consistent_toplevel_storage_static, assignment_value_static_assignable_context_TopLevelVar, IS_SOME_EXISTS] for Type branch of target_runtime_typed_TopLevelVar_imp_static_context: 4 lemmas with existential quantifiers + compound FLOOKUP keys (string_to_num id) + variable name overlap (lemma ty vs goal t from Cases_on) creates search space too large for metis. Times out.
  - evidence: episode:E0129
- irule (iffLR (GEN_ALL assignment_value_static_assignable_context_TopLevelVar)) after drule + strip_tac + gvs: irule cannot instantiate the universally-quantified variables in GEN_ALL of the biconditional to match goal assumptions.
  - evidence: episode:E0128

## Reflection
### Tunnel Vision Check
- The cheat at line 442 (assign_target_INL_imp_assignable_context_stmt_ind TupleTargetV) has been known unused since E0122. Multiple sessions have skipped actually deleting it. Do it now - it's blocking zero-CHEAT.
- C5.4.5 scope is narrow: only side-condition call sites in Assign/AugAssign. Don't get drawn into broader builtin/call cheats.
- The Assign branch already has target_runtime_typed rebuilt at line 1065 and 1092. The missing link is assign_operation_matches_target_shape (from Replace_from_typed) and assign_target_assignable_context (from target_runtime_typed_imp_assignable_context). These should be mechanical to derive.

### What Went Wrong
- Previous sessions on C5.4.3 correctly identified the metis_tac timeout issue but took multiple attempts to find the right tactical (drule_all + rw + qexists). The drule_all approach should be the first choice for existentials + compound FLOOKUP keys from now on.
- The mutual theorem Goal 4 fix was simple (fs + simp + metis_tac) but required a FAIL_TAC probe to understand the goal shape after ho_match_mp_tac.

### Ignored Signals
- The holbuild output showed the standalone lemma proving but mutual theorem failing - should have immediately done a FAIL_TAC probe on Goal 4 instead of guessing.

### Strategy Adjustments
- Always use drule_all for projection lemmas with existential conclusions and compound keys; never start with metis_tac for these.
- After proving a standalone lemma and a mutual theorem, do a full build immediately to confirm both compile before moving on.
- C5.4.5 should prioritize deleting the unused cheat theorems first (quick win) before patching statement branches.

### Oracle Feedback
- C5.4.3 architecture (standalone TopLevelVar lemma then use in mutual) was validated as the correct approach.
- The oracle correctly predicted that drule_all would work but underestimated the metis_tac difficulty even for HashMapT branch (where rw already solved existentials).
- C5.4.4 composition of C5.4.3 + C5.2.3 was as straightforward as predicted - simple metis_tac sufficed.

## Evidence Pointers
- episode:E0130 - C5.4.3 proved with drule_all approach
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:420-456 - unused cheat theorems to delete
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:1113,1119,1141 - Assign/AugAssign cheats to patch
