# STATE_type_system_rewrite
Updated: 2026-05-14

## Cursor
- component: C3.1
- status: in_progress
- active_file: semantics/prop/vyperTypeStatePreservationScript.sml
- next_action: Build-verify subgoal 1 close (add LENGTH xs = LENGTH is - 1 by Cases_on is >> gvs[LENGTH_REVERSE], then gvs[] should contradict compute_hashmap_slot NONE vs ≠ NONE). Then fix subgoal 2 (currently FAIL_TAC probe - needs write_storage_slot/assign_result/assign_subscripts dispatch).
- expected_goal_shape: Subgoal 1: F with compute_hashmap_slot NONE vs ≠ NONE after bridging. Subgoal 2: do-block with write_storage_slot/assign_result/assign_subscripts TypeError branches. Subgoals 3-4: read_storage_slot/assign_subscripts TypeError.
- verify_with: holbuild(targets=['vyperTypeStatePreservationTheory'])

## If This Fails
- If subgoal 1 LENGTH derivation fails: try qpat_x_assum REVERSE eq + LENGTH + DECIDE_TAC. If subgoal 2 doesn't close: insert FAIL_TAC probe to see exact residual goal shape, add targeted drule lemmas.

## Do Not Retry
- Inline x' = LAST is by Cases_on is >> gvs[REVERSE_DEF, LAST_DEF, HD]: gvs renames is to h::t' making the by-subgoal reference to is fail. Use HD_REVERSE_EQ_LAST helper lemma instead.
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m2860_t001
- metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq] for x' = LAST is inline: metis cannot solve directly because SNOC_LAST_FRONT_eq creates circular equation. Use HD_REVERSE_EQ_LAST helper lemma instead.
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m2864_t001
- drule SNOC_LAST_FRONT_eq >> gvs[REVERSE_SNOC_eq] to bridge x' = LAST is: drule gives circular is = SNOC(LAST is)(FRONT is) which gvs cannot eliminate. Use HD_REVERSE_EQ_LAST instead.
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m2870_t001
- gvs >> >- tac for subgoal handling after gvs expansion: >> and >- have same precedence, left-associative. gvs >> >- tac is a type error. Use gvs >- tac or gvs >- (tac1) >- (tac2) pattern.
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m2820_t001

## Reflection
### Tunnel Vision Check
- The gvs-in-assumptions + SNOC/HD bridge pattern works - the key insight is that REVERSE is = x'::xs + is ≠ [] gives x' = HD(REVERSE is) = LAST is via the HD_REVERSE_EQ_LAST helper, and gvs then eliminates x'.
- Could the entire HashMapRef branch be proved more simply via a boundary lemma instead of the inline do-block expansion? Consider whether finishing inline vs switching to boundary lemma is the right call.
- Is the PLAN decomposition still right? C3.1 is a named branch with specific approach - the remaining proof work is mechanical (bridge variables, dispatch TypeError subgoals with existing C2/drule lemmas). No architectural issue.

### What Went Wrong
- 5+ attempts to bridge x' = LAST is because gvs renames is to h::t' making direct variable references fail. The solution was adding HD_REVERSE_EQ_LAST as a helper lemma.
- The >> >- syntax error wasted one full iteration.
- Circular SNOC equation (is = SNOC(LAST is)(FRONT is)) blocked gvs elimination. HD_REVERSE_EQ_LAST avoids this by providing the non-circular fact HD(REVERSE is) = LAST is.

### Ignored Signals
- HD_REVERSE_EQ_LAST pattern was available from the start - metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq] works inside a lemma proof but not inline.
- The Value branch pattern (reverse $ gvs[bind_apply,AllCaseEqs(),return_def]) was the model all along.

### Strategy Adjustments
- Always add small helper lemmas for list identity facts that metis can prove but inline by-subgoals cannot.
- For gvs-expanded do-block branches: derive typing facts before gvs, then use specific variable-bridge lemmas.
- When encountering >> >- syntax errors, always use >- (tac) >> tac or >- tac >- tac pattern.

### Oracle Feedback
- PLAN C3.1 approach is correct. The variable-bridging issue is standard proof-engineering the strategist didn't anticipate.
- The gvs-in-assumptions approach for expanding do-blocks is the right one (confirmed by 4-subgoal creation after gvs).

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2878_t001 - x' = LAST is bridge works via HD_REVERSE_EQ_LAST + gvs elimination
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2860_t001 - gvs renames is to h::t', inline Cases_on approach fails
