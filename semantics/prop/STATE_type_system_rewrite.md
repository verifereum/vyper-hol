# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.1.1.2.1
- status: ready
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: First inspect git status/diff and, if still build-clean and diffs are only the reviewed stable predicate/PLAN/DOSSIER/STATE/LEARNINGS changes, make an unsigned checkpoint commit. Then begin_component('C0.1.1.2.1') and carry forward the already-proved `extcall_generated_driver_ih_def`/`extcall_generated_driver_ih_elim_expr` component; after that follow scheduler to C0.1.1.2.2.1 static success-tail eliminator.
- expected_goal_shape: C0.1.1.2.1 is a carry-forward component: source should already contain `extcall_generated_driver_ih_def` and proved `extcall_generated_driver_ih_elim_expr` immediately before `send_args_runtime_typed_dest`, with no `extcall_expr_sound_from_generated_prefix_delayed_ih` and no E0044 inserted `extcall_expr_sound_from_generated_prefix_driver_pred` body. For C0.1.1.2.2.1, expected goal is the static branch-local eliminator whose conclusion is the full conditional driver premise including `context_well_typed cx` and `functions_well_typed cx`.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)

## If This Fails
- If the carry-forward component is not build-clean, inspect whether failed E0044 helper text reappeared and restore E0043 source shape; checkpoint_progress with build evidence. If branch-local eliminator proof requires direct consumer-side `MATCH_MP_TAC extcall_generated_driver_ih_elim_expr` or long generated-prefix witness plumbing outside the eliminator lemma, stop and close the active component as stuck/risk_mismatch rather than tuning.

## Do Not Retry
- Reinsert the E0044 monolithic `extcall_expr_sound_from_generated_prefix_driver_pred` and try to prove success tails with direct `irule`/`MATCH_MP_TAC extcall_generated_driver_ih_elim_expr`.: This forced a large existential over all generated prefix states and brittle witness lists in the consumer helper; strategist replaced it with branch-local eliminators.
  - evidence: episode:E0044
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1179_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1206_t001
- Unfold `extcall_generated_driver_ih_def` in the expression helper or final Resume during prefix/error splitting.: The predicate exists to keep the huge generated prefix out of routine cleanup; unfolding it outside boundary lemmas recreates E0041/E0044 failures.
  - evidence: episode:E0041
  - evidence: episode:E0044
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1137_t001
- Use broad `simp`/`gvs`/`AllCaseEqs()` over goals containing generated ExtCall prefix or driver predicate structure.: Repeatedly timed out or created huge goals; use targeted rewrite/branch-local boundary lemmas instead.
  - evidence: episode:E0039
  - evidence: episode:E0041
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1104_t001
- Drop `context_well_typed cx` or `functions_well_typed cx` from branch-local driver-IH eliminator conclusions to make statements shorter.: E0044 weakened/partially simplified conditional goals did not match the continuation lemma; the new PLAN explicitly requires the full premise shape.
  - evidence: episode:E0044
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1173_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1211_t001
- Stage all files with `git add -A` or include untracked `tmp_helper.txt` / `LEARNINGS_type_system_rewrite.legacy.md`.: Operator forbids unrelated/ad-hoc files; untracked tmp/legacy files were noted and should be left alone unless explicitly requested.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1216_t001

## Reflection
### Tunnel Vision Check
- Fresh expert should first question whether the next component C0.1.1.2.1 is only a bookkeeping/carry-forward closure, not a place for new proof search; the real next proof work is C0.1.1.2.2.1 after scheduler advances.
- Outside-the-box approach not yet tried: instead of proving static/nonstatic eliminators via the broad eliminator theorem, unfold `extcall_generated_driver_ih_def` directly inside each branch-local eliminator and specialize/label as in E0043; this may avoid `MATCH_MP_TAC` existential witness headaches.
- The PLAN decomposition is now likely the right abstraction: generated-prefix witness plumbing is quarantined inside static/nonstatic boundary lemmas, while the expression helper remains consumer-level. If even those branch-local lemmas are hard, the predicate definition may be wrong-shaped and should be re-planned.
- Do not optimize the old monolithic expression helper. E0044 proved the theorem statement may be semantically right but the proof interface is wrong for a straightforward task.
- A fresh expert would inspect the exact statement order of `extcall_generated_driver_ih_elim_expr_static_success` before writing tactics, ensuring its conclusion matches `extcall_success_continuation_sound_cond_driver_ih` without dropped `context_well_typed`/`functions_well_typed` antecedents.

### What Went Wrong
- The monolithic predicate-based helper assumption failed: hiding the generated driver IH as an atomic predicate solved early simplifier timeouts, but success tails still required reconstructing the full generated monadic prefix to use `extcall_generated_driver_ih_elim_expr`. Evidence: episode:E0044 and tool_output:TO_type_system_rewrite-20260601T081233Z_m1179_t001.
- I tried to force the broad eliminator directly in the consumer helper (`irule`/`MATCH_MP_TAC` plus explicit `qexistsl` witnesses). That recreated the forbidden generated-prefix plumbing and ran into brittle state-type/record-update constraints. Evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1182_t001, tool_output:TO_type_system_rewrite-20260601T081233Z_m1198_t001, tool_output:TO_type_system_rewrite-20260601T081233Z_m1206_t001.
- After closing E0044, the strategist accepted the failure and replaced the subtree with branch-local static/nonstatic eliminators. C0.1.1.2.0 was then re-closed/reviewed as build-clean, but the stable changes have not been committed yet.
- Current STATE on disk is stale relative to the latest PLAN: it still points to old C0.1.1.2.2 monolithic helper. This handoff updates the cursor to the new scheduler state.

### Ignored Signals
- The first continuation-lemma subgoal at E0044 already showed a large existential over continuation witnesses; that was a decomposition smell, not just a tactic-order issue.
- Repeated type-constraint failures while building explicit prefix witnesses were a proof-interface signal: generated-prefix states do not belong in the expression helper consumer proof.
- I underweighted the task instruction to stop if not straightforward; after two eliminator matching failures, the right action was to close/escalate, which was eventually done.
- Untracked `semantics/prop/tmp_helper.txt` and `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` still exist; do not `git add -A`.

### Strategy Adjustments
- Follow new PLAN exactly: begin C0.1.1.2.1 first (carry-forward), then prove C0.1.1.2.2.1 static and C0.1.1.2.2.2 nonstatic branch-local eliminators before reintroducing the expression helper.
- Inside branch-local eliminators only, it is allowed to reconstruct generated-prefix witnesses or unfold/specialize `extcall_generated_driver_ih_def`; outside those lemmas, keep the predicate opaque.
- For branch-local lemmas, preserve the full continuation premise shape: include `context_well_typed cx` and `functions_well_typed cx` in the antecedent so the conclusion matches `extcall_success_continuation_sound_cond_driver_ih` exactly.
- When proving the later expression helper, use old `extcall_expr_sound_from_generated_ih` only as linear prefix/error-case template; success tails should call `drule_all extcall_generated_driver_ih_elim_expr_static_success` or nonstatic, never the broad eliminator directly.
- Commit stable reviewed changes with `git commit --no-gpg-sign` only after checking status/diff and build-clean state; stage only relevant tracked files under `semantics/prop`, never untracked tmp/legacy files unless explicitly instructed.

### Oracle Feedback
- Held: E0041/E0043 oracle insight that the generated driver IH must be opaque was correct; the predicate and broad eliminator are proved and retained.
- Missed reality: the broad eliminator was still too low-level for the monolithic expression helper; E0044 showed that consumer-side use forced generated-prefix witness plumbing.
- New binding oracle guidance from TO_type_system_rewrite-20260601T081233Z_m1211_t001: prove static/nonstatic success-tail eliminators as the consumer API, then retry the expression helper using those branch-local lemmas.
- E0045 review accepted the restored buildable skeleton; scheduler now wants C0.1.1.2.1 next, not direct work on C0.1.1.2.2.1 until the carry-forward component is begun/closed/reviewed if needed.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1218_t004 - current PLAN/frontier: no high risk, beginable now C0.1.1.2.1, then branch-local eliminators
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1211_t001 - strategist review replacing failed monolithic helper with static/nonstatic success-tail eliminators
- episode:E0044 - monolithic predicate-based helper closed stuck/risk_mismatch; direct broad eliminator use in consumer is ruled out
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1209_t001 - holbuild success after reverting failed E0044 helper; buildable skeleton restored
- episode:E0045 - C0.1.1.2.0 buildable skeleton checkpoint proved/reviewed
- episode:E0043 - `extcall_generated_driver_ih_def` and broad `extcall_generated_driver_ih_elim_expr` proved
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1153_t001 - build success after proving predicate and broad eliminator
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1216_t001 - git status: tracked task/source files modified; untracked tmp/legacy files should not be staged
