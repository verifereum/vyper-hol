# STATE_type_system_rewrite
Updated: 2026-05-22

## Cursor
- component: C2.3.1
- status: ready
- active_file: semantics/prop/vyperTypeSystemScript.sml
- next_action: Before new proof edits, preserve the reviewed C2.3 gate/probe checkpoint if still present: inspect git status/diff, stage only relevant tracked files (`semantics/prop/vyperTypeStmtSoundnessScript.sml`, `semantics/prop/PLAN_type_system_rewrite.md`, `semantics/prop/DOSSIER_type_system_rewrite.md`, and handoff-rendered STATE if appropriate), and commit the fixed-array Pop probe/replan; do not stage untracked scratch files. Then begin `C2.3.1` and edit `well_typed_expr env (Pop ty tgt)` in `semantics/prop/vyperTypeSystemScript.sml` from arbitrary `?bd. type_place_target ... ArrayT ty bd` to dynamic `?n. type_place_target ... ArrayT ty (Dynamic n)`. Rebuild `vyperTypeStmtSoundnessTheory` and fix only mechanical Pop-typing fallout.
- expected_goal_shape: After C2.3.1 edit, proof failures should be mechanical uses of the Pop clause of `well_typed_expr_def`: old destructs expecting `?bd. type_place_target env tgt = SOME (Type (ArrayT ty bd))` must be updated to `?n. ... (Dynamic n)`. The local C2.3.2 probe theorem `assign_subscripts_fixed_array_pop_type_error_probe` should still prove by `simp[Once assign_subscripts_def, pop_element_def]` unless removed as documentation. The scheduled C2.3.2 boundary lemma after repair should prove by `simp[Once well_typed_expr_def]`.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If the definition repair causes non-mechanical failures outside Pop typing construction sites, checkpoint_progress on C2.3.1 with the holbuild output and ask the strategist before broad repairs. If the fixed-array probe no longer compiles due to imports or clutter, it may be removed per PLAN after preserving E0713 evidence. If query_plan no longer makes C2.3.1 beginable, follow Oracle next rather than editing.

## Do Not Retry
- Prove `well_typed_expr env (Pop elem_ty tgt)` implies `assign_operation_runtime_typed env (ArrayT elem_ty bd) PopOp` under the old arbitrary-bound rule.: C2.3.1 unfolded the exact definitions and the residual requires `bd = Dynamic n` from no premise; stronger tactics cannot invent that fact.
  - evidence: episode:E0712
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40240_t001
- Leave the Pop typing rule arbitrary-bound and add ad hoc dynamic assumptions inside the Expr_Pop Resume.: This hides the false static interface; fixed-array PopOp produces a TypeError at the assignment leaf, violating the no-TypeError public behavior path.
  - evidence: episode:E0713
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40254_t001
- Change `pop_element_def`/runtime semantics to accept fixed arrays as the first repair.: The strategist selected a localized static typing repair; changing runtime semantics is broader and not authorized by C2.3.1.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40257_t001
  - evidence: source:semantics/vyperValueOperationScript.sml:803-808
- Stage or commit untracked `test_*`, `test_conj*`, or `SuspBugProbeScript.sml` files.: They are pre-existing scratch/ad-hoc files unrelated to stable proof checkpoints. Stage only relevant tracked task/source/PLAN/DOSSIER/STATE/LEARNINGS changes.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40259_t002
- Begin C2.3.2/C2.3.3 before C2.3.1 definition repair.: query_plan makes C2.3.1 Oracle next; C2.3.2 boundary lemma depends on the repaired Pop typing rule, and C2.3.3 depends on both.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40259_t004

## Reflection
### Tunnel Vision Check
- Outside-the-box option not yet explored: instead of only changing `well_typed_expr`, one could alter runtime semantics to support fixed-array Pop, but the strategist explicitly rejected changing `pop_element_def`; repairing static typing is lower-risk and preserves runtime behavior.
- We are not optimizing the wrong theorem: the old Expr_Pop Resume cannot be proved soundly under arbitrary `bd`; the right object is the Pop typing rule/interface that supplies dynamic array side conditions.
- The PLAN decomposition is now the right abstraction: C2.3.1 definition repair, C2.3.2 extraction/runtime boundary lemma, C2.3.3 Resume integration. Do not jump straight to C2.3.3.
- Do not retry the failed static extraction theorem with stronger tactics; the residual goal is semantically missing data, not tactic weakness.
- A fresh expert should first question whether any downstream Pop typing users intentionally rely on fixed arrays. If so, they need to be repaired to dynamic bounds or escalated, not patched with assumptions.

### What Went Wrong
- C2.3's old direct Expr_Pop proof plan assumed the Pop typing rule supplied the dynamic-array premise required by `assign_operation_runtime_typed ... PopOp`. C2.3.1 disproved that extraction: after unfolding `well_typed_expr_def` and `assign_operation_runtime_typed_def`, the residual required `bd = Dynamic n` from only a target typing equality.
- C2.3.2 then showed this was not just a proof-interface nuisance: fixed-array leaf `PopOp` computes to `INR (TypeError "pop_element")` via `assign_subscripts_def` and `pop_element_def`.
- Stable C2.2.3 progress was committed as `b91df1d2a`, but the later C2.3.2 probe/replan changes are not yet committed at handoff. Git status still includes modified PLAN/DOSSIER/source/STATE plus many pre-existing untracked scratch files.

### Ignored Signals
- The existing `assign_operation_runtime_typed_def` explicitly made `PopOp` dynamic-array-only; the old C2.3 direct proof guidance underweighted that interface and treated Pop as a generic assignment consumer.
- The initial C2.3 query already warned of over-decomposition and stale dependency on C3.3; calling the strategist before beginning was correct and led to the Pop gate.
- After C2.3.1 was accepted, the scheduler still blocked C2.3.2 until an augment reclassified C2.3.1 as accepted negative evidence; do not assume review acceptance always updates frontier state automatically.

### Strategy Adjustments
- Treat the Pop issue as a definition repair, not a hard proof. The next leaf is C2.3.1: strengthen the non-frozen Pop typing rule to dynamic arrays in `vyperTypeSystemScript.sml`.
- Keep C2.3.1/C2.3.2 probe evidence as rationale/regression documentation, but do not depend on fixed-array negative facts for the final positive Expr_Pop proof after the rule is repaired.
- After the typing-rule repair, prove a Pop extraction boundary lemma before touching the Expr_Pop Resume; consumers should not repeatedly unfold the full `well_typed_expr_def` or `assign_subscripts_def`.
- Commit the reviewed C2.3.2 probe/replan checkpoint before beginning new edits if build status remains clean and only relevant tracked files are staged.

### Oracle Feedback
- Strategist accepted C2.2.3 (E0711) with no PLAN changes; the Attribute Resume proof matched the planned thin wiring interface.
- Strategist accepted C2.3.1 (E0712) as an expected negative static-extraction probe and then, after scheduler remained blocked, augmented the PLAN to treat it as accepted probe evidence.
- Strategist accepted C2.3.2 (E0713) as sufficient localized evidence; no full `eval_expr` counterexample is required because the internal Pop typing rule is non-frozen and the mismatch is localized. The PLAN now authorizes a definition repair under C2.3.1.

## Evidence Pointers
- episode:E0711 - Expr_Attribute Resume proved/reviewed; committed as b91df1d2a/b91df1d2a checkpoint context
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40227_t002 - `vyperTypeStmtSoundnessTheory` built after Expr_Attribute proof
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40233_t001 - commit `b91df1d2a` for Expr_Attribute checkpoint
- episode:E0712 - Pop static extraction probe failed with unconstrained `bd`; accepted as negative probe evidence
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40240_t001 - exact residual goal requiring `bd = Dynamic n`
- episode:E0713 - fixed-array PopOp probe proved TypeError leaf behavior
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40254_t001 - `vyperTypeStmtSoundnessTheory` built with fixed-array Pop probe theorem
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40255_t003 - diff showing only local fixed-array Pop probe added
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40257_t001 - strategist replaced Pop gate with definition-repair/proof plan
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40259_t004 - current query_plan: C2.3.1 is Oracle next/beginable
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40259_t002 - current git status: C2.3.2 probe/replan changes uncommitted plus untracked scratch files
