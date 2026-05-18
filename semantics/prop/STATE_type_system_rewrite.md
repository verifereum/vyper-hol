# STATE_type_system_rewrite
Updated: 2026-05-18

## Cursor
- component: C4.1
- status: in_progress
- active_file: semantics/prop/vyperTypeSystemScript.sml
- next_action: Fix well_typed_binop_def lines 93-96: replace UAdd->UnsafeAdd, USub->UnsafeSub, UMul->UnsafeMul, UDiv->UnsafeDiv. This is the ROOT CAUSE of the 4 unprovable msg≠'binop' goals. Then restore the well_typed_binop_no_type_error proof in vyperTypeBuiltinsScript.sml to: strip_tac >> gen_tac >> Cases_on `bop` >> gvs[well_typed_binop_def, Excl is_*_type_def, is_*_type_inv, evaluate_type_def, type_to_int_bound_def, AllCaseEqs()] >> TRY (drule vht_ArrayTV_exists >> strip_tac) >> simp[evaluate_binop_def] >> TRY (rpt (COND_CASES_TAC >> simp[]))
- expected_goal_shape: After fix + gvs: ~56 goals resolved to concrete evaluate_binop calls. After simp[evaluate_binop_def]: ~14 goals with conditionals (Div/Mod/Exp) or bounded_int_op. After COND_CASES_TAC: all close. No more msg≠'binop' goals.
- verify_with: holbuild(targets=['vyperTypeBuiltinsTheory'], tactic_timeout=120, timeout=600)

## If This Fails
- If msg≠'binop' goals persist after fixing well_typed_binop_def, grep the bop Datatype for ALL constructors and verify each one appears in well_typed_binop_def. If new constructor-name mismatches found, fix those too. If no more mismatches but proof still fails, FAIL_TAC probe to inspect remaining goals.

## Do Not Retry
- gvs[evaluate_binop_def, AllCaseEqs()] after initial gvs: AllCaseEqs() does case splits that create spurious msg≠'binop' goals from TypeError catch-all branches. Use simp[evaluate_binop_def] instead.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m24329_t001
- fs instead of gvs for well_typed_binop_def expansion: fs without variable elimination creates 112 goals (double gvs). Use gvs with Excl for type classifiers.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m24179_t001
- gen_tac AFTER gvs to strip ∀msg: After gvs creates goals with ∀msg, gen_tac strips msg. But impossible In/NotIn/NotEq-int goals become unprovable since simp reduces to 'binop'≠msg which can't be discharged without F from assumptions. Must handle special cases BEFORE or use irule approach.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m24144_t001
- Attempting tactics before verifying definition constructor names: The UAdd/UnsafeAdd mismatch made the theorem false for 4 constructors. 14+ prior episodes of tactic thrashing could have been avoided by fixing the definition first.
  - evidence: source:semantics/prop/vyperTypeSystemScript.sml:93-96

## Reflection
### Tunnel Vision Check
- The UAdd/UnsafeAdd naming mismatch was already documented in LEARNINGS L0749 and claimed fixed, but was NEVER actually fixed. I should have checked this FIRST before any tactic work. 14+ prior episodes of tactic thrashing could have been avoided.
- The stale holbuild checkpoint made iterative proof development very slow - every edit silently replayed the old prefix. I should have known that FAIL_TAC probes bypass this by forcing fresh goal display.
- The CASE-EXPLOSION approach (gvs with AllCaseEqs() on evaluate_binop_def) creates msg≠'binop' goals because it resolves the case expressions including the catch-all TypeError branch. simp[evaluate_binop_def] is better than gvs for the second pass.

### What Went Wrong
- ROOT CAUSE: well_typed_binop_def uses constructor names UAdd/USub/UMul/UDiv which don't exist in the bop Datatype (those are UnsafeAdd/UnsafeSub/UnsafeMul/UnsafeDiv). After Cases_on bop, the 4 Unsafe* cases have no well_typed_binop clause, so gvs can't resolve them, and evaluate_binop_def's catch-all produces unprovable msg≠'binop' goals.
- LEARNINGS L0749 documents this exact bug but claims it was already fixed - it wasn't. I should have verified the actual file state.
- Spent most of the session fighting holbuild checkpoints that replay old proof prefixes. Adding trivial tactical differences (all_tac, whitespace) failed to break the checkpoint. Only FAIL_TAC probes produced informative goal state.

### Ignored Signals
- LEARNINGS entry L0749 explicitly says UAdd->UnsafeAdd fix is needed but claims done - I didn't verify
- The 4 remaining msg≠'binop' goals have EXACTLY the UintT/IntT assumptions that the Unsafe* operators cover - this should have immediately pointed to constructor name mismatch
- grep results showed UnsafeAdd in vyperASTScript.sml but I kept trying tactics instead of fixing the definition

### Strategy Adjustments
- ALWAYS verify definition constructor names match before attempting case-split proofs. grep the Datatype and compare.
- When getting unprovable goals like msg≠X, immediately suspect constructor name mismatches between Definitions.
- Don't trust LEARNINGS entries that claim something was 'already fixed' - verify in the actual source
- When holbuild checkpoint interferes, use FAIL_TAC probes to get goal state - they force fresh evaluation

### Oracle Feedback
- PLAN C4.1 architecture (case analysis over binop constructors) is sound. The issue is purely a definition constructor name mismatch that makes the theorem false for 4 of the 26 constructors.
- The per-operator boundary lemma approach is correct - once the definition fix is applied, simp[evaluate_binop_def] + COND_CASES_TAC should close all goals.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24328_t001 - probe2: 56 goals after first gvs, concrete evaluate_binop calls resolved
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24329_t001 - probe3: 4 msg≠'binop' goals remain after gvs[evaluate_binop_def,AllCaseEqs()], these are the unprovable ones from Unsafe* mismatch
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24333_t001 - probe4: 14 goals remain after simp[evaluate_binop_def], 10 conditionals + 4 msg≠'binop'
- source:syntax/vyperASTScript.sml:60-63 - bop Datatype uses UnsafeAdd/UnsafeSub/UnsafeMul/UnsafeDiv
- source:semantics/prop/vyperTypeSystemScript.sml:93-96 - well_typed_binop_def STILL uses UAdd/USub/UMul/UDiv (NEVER FIXED despite L0749 claiming it was)
