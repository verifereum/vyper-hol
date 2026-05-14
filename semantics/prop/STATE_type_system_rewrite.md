# STATE_type_system_rewrite
Updated: 2026-05-14

## Cursor
- component: C3.1.7.3.1
- status: in_progress
- active_file: semantics/prop/vyperTypeStatePreservationScript.sml
- next_action: Complete assign_target_TopLevelVar_ArrayRef_ordinary_no_type_error proof: after Cases_on `final_tv` >> gvs[CaseEq type_value, bind_def, lift_sum_def, return_def, raise_def, AllCaseEqs(), no_type_error_result_def] produces 21 goals. Each needs: derive assign_subscripts = INL new_val from lift_sum assumption via Cases_on `assign_subscripts tv current_val remaining_subs op` >> gvs[return_def, raise_def], then chain through read_storage_slot_success_type, assign_subscripts_preserves_type_runtime_typed, assign_result_no_type_error_from_successful_assign/_split, write_storage_slot_no_type_error_from_value_has_type, assign_subscripts_no_type_error_runtime_typed, read_storage_slot_error. Alternatively define a small helper lemma to extract the INL fact.
- expected_goal_shape: 21 goals after gvs each with forall msg. res ~= INR (Error (TypeError msg)) conclusion and monadic chain assumptions including (case assign_subscripts ... of INL v => return v | INR e => raise (Error e)) s = ...
- verify_with: holbuild(targets=['vyperTypeStatePreservationTheory'])

## If This Fails
- If Cases_on approach on assign_subscripts creates too many subgoals, define a helper lemma: Theorem lift_sum_INL_imp[local]: (case f of INL v => return v | INR e => raise (Error e)) s = (INL w,s') ==> ?v. f = INL v /\ v = w /\ s' = s. If still stuck close episode stuck/missing_helper and escalate to plan_oracle.

## Do Not Retry
- gvs[AllCaseEqs()] with weak exclusion hypotheses (op=PopOp => final_tv<>ArrayTV Dynamic) on ordinary ArrayRef boundary lemma: AllCaseEqs must split on both op and final_tv to apply exclusion, creating 35+ branches and timing out
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m6760_t001
- Cases_on op + Cases_on final_tv after simp[Once assign_target_def] + strip_tac on ordinary lemma: Even targeted Cases_on creates 7*7 combinatorial explosion timing out
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m6762_t001
- gvs[AllCaseEqs()] without Cases_on final_tv first: gvs cannot split case final_tv of ... when final_tv is free; produces unsplit goals
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m6790_t001
- rpt (FIRST [...]) with metis_tac to uniformly close 21 goals: No FIRST clause matches goal shapes since assign_subscripts result is wrapped in lift_sum; metis cannot chain through it
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m6824_t001

## Reflection
### Tunnel Vision Check
- The 21-goal explicit >- approach with sum_case_eq was wrong - sum_case_eq does not exist as HOL4 identifier. Should have used Cases_on assign_subscripts or defined a helper lemma.
- Spent too many iterations on gvs[AllCaseEqs()] without Cases_on final_tv first. AllCaseEqs cannot split case final_tv of ... when final_tv is free - must destruct first.
- Should have checked HashMapRef proof structure applicability after adding Cases_on final_tv, rather than trying many gvs variant combinations.

### What Went Wrong
- Weak exclusion hypotheses (op=PopOp => final_tv<>ArrayTV Dynamic) caused combinatorial explosion with gvs[AllCaseEqs()] because AllCaseEqs must split on both op AND final_tv creating 35+ branches
- gvs[AllCaseEqs()] alone cannot reduce case final_tv of BaseTV=>...|TupleTV=>...|ArrayTV=>... when final_tv is free - need Cases_on first then gvs[CaseEq type_value]
- After Cases_on final_tv >> gvs[CaseEq type_value,...,AllCaseEqs(),no_type_error_result_def], the 21 goals each have (case assign_subscripts ... of INL v => return v | INR e => raise (Error e)) assumption needing further resolution

### Ignored Signals
- PLAN says Do NOT use single gvs[AllCaseEqs()] blast across all cases for ArrayRef - should have led immediately to Cases_on final_tv approach
- HashMapRef proof works on free final_tv without destructing because HashMapRef has NO inner (op,final_tv) case. ArrayRef IS structurally different and requires destructing final_tv
- Previous STATE explicitly recommended splitting into separate boundary sub-lemmas - strong exclusion hypotheses are right approach but proof tactics do not close goals

### Strategy Adjustments
- Must resolve assign_subscripts INL/INR fact from lift_sum wrapper in assumptions. Options: (1) Cases_on each assign_subscripts call, (2) define helper lift_sum_INL_imp lemma, (3) Cases_on assign_subscripts >> gvs[return_def,raise_def] inside each subgoal
- After ordinary lemma is proved, must rewrite parent assign_target_TopLevelVar_ArrayRef_branch_no_type_error to use boundary sub-lemmas instead of inline Cases_on x1 explosion
- Consider factoring out a single helper that works for all 5 type_value variants instead of repeating same 4-step pattern 5 times

### Oracle Feedback
- PLAN C3.1.7.3 decomposition into ordinary/uint256/append/pop is correct and strong hypotheses (op<>PopOp, !v.op<>AppendOp v) are needed
- Parent theorem rewrite to use boundary sub-lemmas is the right architecture - inline Cases_on x1 explosion was old broken approach
- storage_array_append/pop_len_value_has_type (C3.1.7.3.2) already proved - correct infrastructure

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6808_t001 - 21 goals after Cases_on final_tv >> gvs correct split but assign_subscripts INL fact not extracted from lift_sum assumption
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6824_t001 - rpt FIRST approach fails: no FIRST clause matches goal shapes because assign_subscripts result is wrapped in lift_sum
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6792_t001 - Cases_on final_tv >> gvs[CaseEq type_value, bind_def, lift_sum_def, ...] gives 6 clean goals with ordinary do-block body (no monadic expansion yet)
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2311-2351 - HashMapRef boundary lemma model that works (4 goals, no inner case split)
- source:semantics/vyperStateScript.sml:906-938 - ArrayRef branch definition with case (ao, final_tv) causing nested split
