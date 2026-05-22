# STATE_type_system_rewrite
Updated: 2026-05-22

## Cursor
- component: C2.1.1.13.3
- status: ready
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Before new proof work, preserve the reviewed stable checkpoint: inspect `git status`/diff, stage only tracked task-owned files (`semantics/prop/vyperTypeStmtSoundnessScript.sml`, PLAN/DOSSIER/LEARNINGS/STATE as appropriate), do not stage the many untracked probe/test files, and commit the C2.1.1.13.2 proof if `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)` is still clean. Then begin_component('C2.1.1.13.3') and fill only the ordinary-expression half of `Resume eval_all_type_sound_mutual[Expr_Subscript]`.
- expected_goal_shape: C2.1.1.13.3 targets the first/ordinary conjunct inside the normalized `Expr_Subscript` Resume, currently around the placeholder `conj_tac >> rpt strip_tac >> cheat`. Expected proof shape: unfold/split the Subscript static typing enough to separate ordinary-base `well_typed_expr env e`/`subscript_type_ok` from place-base `type_place_expr env e = SOME base_vt`/`subscript_vtype ... = SOME (Type v9)`. Ordinary-base branch uses existing array/value evaluator-tail facts; place-base branch should call `expr_subscript_place_tail_sound_stmt` to obtain ordinary `expr_result_typed` for successful results. Preserve exact `get_Value` and monadic tail equalities until choosing the branch-specific helper.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If commit precheck fails, do not start C2.1.1.13.3; inspect the build goal and checkpoint/escalate if C2.1.1.13.2 regressed. If the C2.1.1.13.3 Resume proof requires re-unfolding the full evaluator tail in multiple branches or quoted ASSUME/MATCH_MP plumbing, checkpoint_progress on C2.1.1.13.3 with the exact holbuild goal and ask the strategist rather than adding tactical descendants.

## Do Not Retry
- Stage or commit the untracked probe/test files shown by git status (`SuspBugProbeScript.sml`, `test_backslash*.sml`, `test_conj*.sml`, etc.).: They are unrelated leftover untracked experiments; stable checkpoint should stage only relevant tracked task-owned files.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38787_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38788_t002
- Reopen C2.1.1.13.2 or re-prove `expr_subscript_place_projection_tail_sound_stmt` before starting C2.1.1.13.3.: The component is proved, reviewed, and verified by holbuild. Only commit/verification remains before moving to the next scheduled leaf.
  - evidence: episode:E0680
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38784_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38786_t001
- Use a shared `FIRST [irule expr_subscript_place_tail_sound_stmt; ...]` tail for Expr_Subscript Resume branches.: Prior episodes showed the shared tail loses the active ordinary/place static disjunct; PLAN requires explicit static split and branch-specific helper selection.
  - evidence: episode:E0677
  - evidence: episode:E0678
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38789_t003
- Run broad `rw[]`/`gvs[well_typed_expr_def,type_place_expr_def,AllCaseEqs()]` over the full mutual Resume context.: Broad simplification previously timed out or consumed branch-specific facts. Use controlled branch splitting and local helper application.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38720_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m38737_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box option for C2.1.1.13.3 if the Resume proof balloons: extract a small ordinary-base Subscript tail helper rather than fighting the mutual proof context. This would mirror the already proved place-tail helpers and keep the Resume as wiring only.
- We are not optimizing the wrong theorem now: C2.1.1.13.2 is complete; the next theorem is the ordinary half of the Subscript Resume, a direct consumer of existing helpers.
- The PLAN decomposition is still the right abstraction: helper/build gate first, ordinary Resume half, then place-projection Resume half. Do not jump to Expr_Attribute or builtins while Expr_Subscript placeholder cheats remain.
- Do not retry tactics that unfold `well_typed_expr_def`, `type_place_expr_def`, and evaluator tails globally over the whole Resume; if exact branch wiring is not straightforward, that is a helper/interface issue to checkpoint or escalate.
- A fresh expert would first question which static disjunct is active in `well_typed_expr env (Subscript ...)` and whether the goal wants ordinary `expr_result_typed` or place `place_expr_result_typed`; choosing the wrong helper is the main failure mode.

### What Went Wrong
- Initial STATE was stale after prior handoff: it said C2.1.1.13.2 was blocked pending review. This session reviewed E0679, began C2.1.1.13.2, and completed it. STATE must now point to C2.1.1.13.3, not the old blocked review gate.
- The projection helper proof took many small holbuild iterations because early edits copied the existing helper too literally: it initially tried to reason with the base expression type/result variable in places where the projection result vtype was already the right discriminator. The final successful proof explicitly derives the base annotation, then splits `result_vt` in the HashMap place case.
- Stable progress has been proved and reviewed but not committed because the user forced handoff. There are many unrelated untracked probe/test files in the worktree; they must not be staged.

### Ignored Signals
- The Type/Array branch needed the annotation fact `vtype_annotation_ok (Type t) (expr_type e)` from `type_place_expr_annotation_ok_stmt`; without it, case splitting on the wrong variable left `result_vt` insufficiently normalized.
- In HashMapT place projections, `result_vt = Type t'` returns a read `Value`, while `result_vt = HashMapT kt vt` returns a `HashMapRef` directly. Treating both through the storage-read path caused residual goals.
- `qpat_x_assum` patterns over monadic do-notation are brittle when simplification has reduced the tail; use local `mp_tac` before simplification or simplify the live tail directly rather than trying to match the pre-simplified shape.

### Strategy Adjustments
- Next session should not revisit C2.1.1.13.2 except for commit/verification. The reviewed source has no cheat in `expr_subscript_place_projection_tail_sound_stmt`; the remaining Subscript cheat is the scheduled Resume placeholder for C2.1.1.13.3/C2.1.1.13.4.
- For C2.1.1.13.3, keep branch selection before evaluator-tail simplification. The branch-specific helpers now available are `expr_subscript_place_tail_sound_stmt` for ordinary result from a place base, and `expr_subscript_place_projection_tail_sound_stmt` later for the reverse/place conjunct. Do not use the projection helper in the ordinary half unless the conclusion matches.
- If the ordinary half becomes large, consider first proving a tiny local adapter/helper for the ordinary-base evaluator tail analogous to the place-tail helper, but checkpoint/escalate if that changes the planned interface.

### Oracle Feedback
- Strategist insight held: flattening C2.1.1.13.2 into a single build-gate/helper leaf was the right abstraction; no definition changes were needed.
- The PLAN's warning not to weaken the helper to `expr_result_typed` was correct. Nested HashMap place results require `place_expr_result_typed`, and the final helper proves exactly that.
- The PLAN understated the tactical wrinkle that HashMapT result projections split by `result_vt`, not by stale local variable names after `gvs`; nevertheless the component remained Risk 2 and closed with the planned interface.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38737_t001 - holbuild passed after replacing timeout-prone `ifexp_branch_from_cond_ih` opener
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38784_t001 - `vyperTypeStmtSoundnessTheory` built after proving `expr_subscript_place_projection_tail_sound_stmt`
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38786_t001 - strategist accepted/reviewed C2.1.1.13.2 closure
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38789_t003 - current plan frontier: C2.1.1.13.3 beginable next
- episode:E0680 - closed proved episode for C2.1.1.13.2
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6253-6262 - targeted IfExp proof opener now in source
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6868-6979 - proved projection-tail helper now in source
