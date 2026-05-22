# STATE_type_system_rewrite
Updated: 2026-05-22

## Cursor
- component: C2.1.1.13.1
- status: ready
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Begin component C2.1.1.13.1. Normalize only the partial `Resume eval_all_type_sound_mutual[Expr_Subscript]` proof area around lines ~6867-6970: remove/quarantine the current shared-tail `FIRST [expr_subscript_place_tail_sound_stmt; old ordinary tail]`/positional branch-suffix experiment, keep the accepted local helpers above it, and restore a readable skeleton with early ordinary/place split and temporary local cheats if needed. Do not edit Expr_Attribute or later branches.
- expected_goal_shape: Current source is partial and likely fails in `Resume eval_all_type_sound_mutual[Expr_Subscript]`, either at QED with residual INL-base/place-static goals lacking the right tail equality/place facts, or in timeout-prone `gvs` after evaluator case splits. After cleanup, expected shape should be a controlled skeleton, not a completed proof.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If normalization itself fails to parse/build through the helper area, read lines ~6700-6975 and fix only the Expr_Subscript cleanup. If the proof structure still pushes into shared-tail residuals, checkpoint C2.1.1.13.1 or close stuck only if terminal; do not resume tactical patching or proceed to C2.1.1.13.2 before the source is normalized.

## Do Not Retry
- Continue trying to make the current `FIRST [irule expr_subscript_place_tail_sound_stmt; old ordinary tail]` shared success tail build by adding more `gvs`, branch suffixes, or exact-pattern rewrites.: E0677 showed this proof structure is wrong-shaped: it obscures which Subscript static disjunct is active, leaves residual goals without the needed evaluator-tail equality/place facts, and causes simplifier timeouts.
  - evidence: episode:E0677
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38663_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38683_t001
- Use broad `gvs[]` or `gvs[well_typed_expr_def,type_place_expr_def,AllCaseEqs()]` over the full mutual Resume context after evaluator case splits.: Repeated attempts timed out or stripped/rewrote the context so the proof lost branch-specific facts. Use explicit static disjunct splits and local helpers instead.
  - evidence: episode:E0677
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38663_t001
  - evidence: episode:E0673
- Patch the ordinary-base proof while assuming `expr_result_typed env e x`, `~is_HashMapRef x`, or ordinary base facts in the place-base static disjunct.: The place-base disjunct intentionally has `type_place_expr env e = SOME base_vt` and `place_expr_result_typed env base_tv base_vt`; HashMapRef/storage cases are intended and cannot be ruled out.
  - evidence: episode:E0674
  - evidence: episode:E0677
  - evidence: tool_output:TO_type_system_rewrite-20260521T174852Z_m38539_t001
- Proceed to Expr_Attribute or later visible cheats after any Expr_Subscript progress without closing/checkpointing the active planned component.: PLAN scope remains only the Expr_Subscript repair subtree; later branches are separately scheduled.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38689_t003

## Reflection
### Tunnel Vision Check
- Outside-the-box approach now authorized by PLAN: stop trying to prove the current Resume directly; temporarily re-skeletonize it with local cheats under C2.1.1.13.1, then prove clean helper boundaries bottom-up.
- A fresh expert should first question whether the helper conclusion matches the consumer. For the separate place projection, `expr_subscript_place_tail_sound_stmt` is insufficient because it concludes ordinary `expr_result_typed`; a new `place_expr_result_typed` helper is needed.
- The PLAN decomposition is now the right abstraction: local source cleanup plus exact boundary lemma plus two Resume halves. No definition change or mutual theorem weakening is indicated.
- Do not optimize a global theorem or induction variable. The evaluator induction is already fixed; the problem is local branch ordering and helper interface shape.

### What Went Wrong
- I treated a proof-structure mismatch as a local tactic/wiring problem for too long. The accepted helper was placed into a shared evaluator tail via `FIRST`, but the ordinary Subscript static typing has two semantically different disjuncts; the shared tail selected facts from the wrong branch.
- The current source was left partial around the Expr_Subscript Resume. It is not build-clean; next session must normalize the source under C2.1.1.13.1 before proving new semantic helpers.
- Using `>>` after `Cases_on` and then adding suffix tactics made branch targeting brittle. Some failures were holbuild instrumentation complaints about branch suffixes; others were genuine residual goals from unintended branch contexts.

### Ignored Signals
- Live goals in the place-base path lacked `expr_result_typed env e x` and had `type_place_expr env e = SOME vt`; this contradicted the old ordinary-base proof assumptions.
- Timeouts in small-looking `gvs[]` calls were a design signal: the mutual Resume context is too large for broad simplification after case splits.
- The separate Subscript place projection wants `place_expr_result_typed`, not `expr_result_typed`; trying to reuse expression-half infrastructure without a projection-specific helper is wrong-shaped for HashMapT results.

### Strategy Adjustments
- Follow the new PLAN exactly: first C2.1.1.13.1 source cleanup, then C2.1.1.13.2 projection-tail helper, then C2.1.1.13.3 ordinary half, then C2.1.1.13.4 separate place projection.
- In the ordinary half, split the `well_typed_expr_def` Subscript static disjunction before evaluator-tail analysis. Ordinary-base branch may use ordinary IH/old value proof; place-base branch must use base place IH and `expr_subscript_place_tail_sound_stmt`.
- For the reverse/place-projection half, add the exact helper `expr_subscript_place_projection_tail_sound_stmt` with a `place_expr_result_typed` success conclusion before wiring the Resume.
- Use targeted `simp_tac bool_ss [pair_case_thm,sum_case_def,PAIR_EQ]` only in small branches with a known equality; avoid whole-context simplification.

### Oracle Feedback
- Strategist accepted the risk mismatch and decomposed C2.1.1.13 into four beginable children. Key insight: split the Subscript static typing alternatives before deep evaluator analysis, and add a separate place-projection tail helper.
- The earlier strategist insight that Subscript is a real place expression held. Additional reality from E0677: the ordinary `well_typed_expr` half itself contains a place-base static disjunct, so the old single shared success tail is invalid.
- C2.1.1.13.1 is now Oracle next; do not start the helper proof until the partial Resume source is normalized.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38687_t001 - strategist review replaced the stuck single-leaf plan with C2.1.1.13.1-.4 and made C2.1.1.13.1 Oracle next
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38689_t003 - query_plan confirms no high-risk blockers and beginable now is C2.1.1.13.1
- episode:E0677 - terminal stuck/risk_mismatch closure documenting why shared-tail FIRST strategy is invalid
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38683_t001 - latest holbuild evidence of residual Expr_Subscript goal after shared-tail attempts
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38605_t001 - `expr_subscript_place_tail_sound_stmt` and local hashmap bounds helper were accepted before Resume wiring
