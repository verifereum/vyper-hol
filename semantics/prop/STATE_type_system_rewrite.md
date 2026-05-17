# STATE_type_system_rewrite
Updated: 2026-05-17

## Cursor
- component: C4.2
- status: in_progress
- active_file: semantics/prop/vyperTypeBuiltinsScript.sml
- next_action: Run holbuild(targets=['vyperTypeBuiltinsTheory']) to verify ecadd_no_type_error + extract_ec_point_uint256_2_not_none boundary lemma, then fix ecmul_no_type_error similarly (EL-index + boundary lemma). After that, fix any remaining build failures in well_typed_builtin_app_no_type_error dispatcher and remaining builtin theorems.
- expected_goal_shape: ecadd/ecmul should close via extract_ec_point_uint256_2_not_none boundary. If boundary lemma proof fails, the issue will be in Cases_on av >> fs[value_has_type_def] step or extract_ec_point_def/array_index_def simplification.
- verify_with: holbuild(targets=['vyperTypeBuiltinsTheory'], tactic_timeout=60, timeout=300)

## If This Fails
- Close episode with diagnosis, then continue to ecmul fix. If boundary lemma is wrong, probe with EVAL on extract_ec_point(ArrayV(SArrayV[])). If ecadd approach doesn't close, try adding LENGTH_word_to_bytes or more array_index details.

## Do Not Retry
- gvs[LIST_REL_CONS1] followed by Cases_on 't' for list decomposition in builtin proofs: gvs generates unpredictable variable names for list tails; after 2+ levels of Cases_on, 't' no longer exists. 8+ attempts across 3 sessions (E0160).
  - evidence: episode:E0160
- match_mp_tac LIST_EQ >> simp[] for list decomposition: LIST_EQ produces conjunction (LENGTH equality AND universal EL equality). >> applies simp to both subgoals but simp cannot solve the universal EL equality subgoal.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m22670_t001
- Using BaseTV(ArrayTV...) as type_value for ArrayT types: ArrayTV is a type_value constructor directly, not wrapped in BaseTV. evaluate_type(ArrayT ...) = SOME(ArrayTV ...), not SOME(BaseTV(ArrayTV...)).
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m22728_t001
- fs[AllCaseEqs()] + definition unfolding directly in consumer proofs for extract_ec_point/array_index: Leaves many subgoals about array_index internals. Use boundary lemma extract_ec_point_uint256_2_not_none instead.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m22730_t001

## Reflection
### Tunnel Vision Check
- Spent entire session on C4.2 builtin theorems (ecrecover + ecadd). Should have stepped back sooner when ecadd/ecmul both have the same gvs variable-naming problem - this is a pattern, not a one-off.
- The PLAN decomposition into C4.2.1-C4.2.4 was correct but I did the ecadd work inline instead of as separate boundary lemmas. Eventually converged to boundary lemma approach for extract_ec_point (the RIGHT approach per §3 abstraction levels).
- ecmul still has the old broken gvs-based proof - need to apply same EL-index + boundary lemma pattern.
- Other C4 components (C4.3 ABI, C4.4 Env/Acc, C4.5 type-builtin dispatcher) haven't been touched yet.

### What Went Wrong
- ecrecover_no_type_error: match_mp_tac LIST_EQ >> simp[] failed because >> applies simp to both LIST_EQ subgoals. Fixed with list_el_decomp_4 local helper. Took 2 attempts to get the helper proof right (variable naming after Cases_on).
- ecadd_no_type_error: 10+ failed attempts across multiple approaches: (1) gvs destroys ≠ TypeError goals (L0787); (2) Cases_on 't' after gvs[LIST_REL_CONS1] generates unpredictable variable names; (3) Wrong type_value constructor BaseTV(ArrayTV...) instead of ArrayTV; (4) rename1 syntax error with '=>' arrow; (5) Tried multiple proof structures before converging on boundary lemma + EL-index.
- Wasted time renaming variables instead of using EL-index approach from the start. The EL-index pattern from ecrecover should have been immediately applied to ecadd/ecmul.

### Ignored Signals
- L0787 (gvs destroys ≠ TypeError goals) was in global learnings but I kept trying gvs-based proofs for ecadd
- L0825 (list_el_decomp_n pattern) was already proved for n=4 before I started on ecadd, but didn't use it for ecadd's 2-element case immediately
- The PLAN's C4.2.2/C4.2.3 decomposition explicitly prescribes boundary lemmas - I should have extracted extract_ec_point boundary lemma immediately instead of trying inline expansion

### Strategy Adjustments
- Always use EL-index approach + boundary lemmas for fixed-arity builtin argument lists. Never use gvs[LIST_REL_CONS1] + Cases_on 't' pattern.
- When a proof pattern works (EL-index + boundary for ecrecover), immediately apply it to similar theorems (ecadd, ecmul) rather than trying approaches that are known to fail.
- For value decomposition, always use Cases_on 'EL i vs' >> fs[value_has_type_def] rather than decomposing the whole list first.
- ArrayTV is a type_value, not BaseTV(base_type). Use evaluate_type_def to derive ArrayTV from ArrayT.

### Oracle Feedback
- Strategist's C4.2 boundary lemma approach was correct - extract_ec_point_uint256_2_not_none is exactly the kind of boundary lemma prescribed.
- The C4.2.2/3/4 decomposition into runtime boundary + extraction + composition would have been faster if I had implemented it from the start rather than trying inline proofs.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22675_t002 - ecrecover_no_type_error build failure showing match_mp_tac LIST_EQ >> simp[] fails
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22683_t001 - list_el_decomp_4 proof correct (Cases_on t' not t)
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22730_t001 - ecadd probe showing remaining goal: value_has_type ArrayTV facts + evaluate_ecadd vs = INR(TypeError msg)
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22728_t001 - ecadd wrong type BaseTV(ArrayTV...) causing type unification error
