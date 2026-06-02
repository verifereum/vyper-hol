# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.5.4.4.3
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Read `vyperTypeStmtSoundnessScript.sml` around the inserted wrapper theorem `extcall_after_state_update_tail_sound_cond_driver_ih_get_tenv` (~lines 9743-9790), then run `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)` to see the current exact failure. Current source is partial/uncommitted and likely not build-clean because the last edit changed the old-helper application to `MATCH_MP_TAC extcall_after_state_update_tail_sound_cond_driver_ih` but was not rebuilt before handoff.
- expected_goal_shape: A small wrapper-lemma proof goal, not the generated ExtCall Resume prefix. The theorem statement has the live tail equation using `evaluate_abi_decode_return (get_tenv cx) ret_type returnData`; after `get_tenv cx = env.type_defs` and `gvs[]`, the remaining obligation should be applying `extcall_after_state_update_tail_sound_cond_driver_ih` with compact premises: runtime/functions/accounts/well_typed_opt/well_formed/driver-type/conditional-driver-IH/tail equation.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If failure is a small premise-ordering/matching issue in the wrapper, repair the wrapper proof only using explicit `qspecl_then ... mp_tac`, `impl_tac`, `conj_tac`, and live assumptions; checkpoint_progress after useful partial evidence. If proof again requires generated ExtCall prefix facts or broad Resume-context simplification, close C0.5.4.4.3 as stuck/risk_mismatch and call plan_oracle review with E0268 evidence.

## Do Not Retry
- Use broad `gvs[]`/`simp[]` in the large `Expr_Call_ExtCall_nonstatic_success` Resume goal to rewrite `get_tenv cx` to `env.type_defs`.: E0267 showed this times out or fails in the huge post-RESUME context; the rewrite belongs in C0.5.4.4.3's small wrapper theorem.
  - evidence: episode:E0267
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4910_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4914_t001
- Manually instantiate the generated optional-driver IH with a long `qspecl_then` list over ExtCall prefix variables.: This is forbidden generated-prefix adapter plumbing and failed again during E0267.
  - evidence: episode:E0267
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4916_t001
  - evidence: episode:E0262
- Use unguarded `rpt conj_tac >> TRY (first_assum ACCEPT_TAC)` in the wrapper proof.: It over-solved/left the tactic stream in a bad state and produced holbuild `no goals` instrumentation failures; use explicit premise order instead.
  - evidence: episode:E0268
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4930_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4947_t001
- Treat C0.5.4.4.2's exposed payload as sufficient to start/finish C0.5.4.5 without the live-tenv wrapper.: E0267 proved the exposed payload alone still leaves the old helper's tail-equation mismatch in the huge Resume goal.
  - evidence: episode:E0267
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4905_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4922_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box: instead of wrapping the old helper with backward `irule`, prove a more direct tail theorem by copying the old helper proof but with `get_tenv cx`; this may avoid brittle theorem application entirely while staying prefix-free.
- We may be optimizing the old helper interface too literally. A fresh expert should ask whether the wrapper conclusion should be exactly the consumer goal or only a smaller lemma rewriting the tail equation under the `(if ... else ...)` term.
- The PLAN decomposition is currently plausible: C0.5.4.4.3 is a prefix-free boundary lemma and is the right abstraction before returning to the huge Resume goal. Do not jump back to C0.5.4.5 until the wrapper builds.
- Do not keep trying generated-IH extraction tactics. The active problem is now a small wrapper theorem; if it becomes large or prefix-shaped, the wrapper statement is wrong.
- Fresh expert question: can `extcall_after_state_update_tail_sound_cond_driver_ih_get_tenv` be proved by `qspecl_then [...] mp_tac old_helper >> simp[]` with the full antecedent discharged as one implication, avoiding `irule` existential subgoals and holbuild's no-goals instrumentation issue?

### What Went Wrong
- E0267 showed C0.5.4.5 was not actually Risk 2 under the exposed-payload-only interface: direct use of the env.type_defs helper in the large Resume goal failed on the `get_tenv cx` tail equation and local simplification timed out.
- The strategist repaired this by adding C0.5.4.4.3, a live-tenv wrapper lemma. I inserted the wrapper theorem, but did not finish it before handoff.
- Several wrapper proof shapes with `irule extcall_after_state_update_tail_sound_cond_driver_ih` plus explicit witnesses reached the intended compact old-helper obligation, but the tactic script either exposed premise-ordering issues or triggered holbuild `no goals` instrumentation failures after subgoals were solved early.
- Current source is partial and uncommitted; the last edit to use `MATCH_MP_TAC extcall_after_state_update_tail_sound_cond_driver_ih` was not rebuilt. PLAN/DOSSIER also have uncommitted tracked diffs from E0267 review and E0268 checkpoint.

### Ignored Signals
- The old helper's theorem shape after `irule` produces an existential-packed antecedent, so blindly combining `rpt conj_tac`, `qexistsl`, and `TRY` is brittle and can confuse the checkpoint/instrumentation path.
- The wrapper proof is small enough that broad `gvs[]` or `metis_tac[]` should not be necessary after the initial `get_tenv` rewrite; when `metis_tac[]` timed out on a structured conjunction, the proof needed explicit premise management.
- The success subresume remains cheated; clean focused builds before C0.5.4.5 only mean the partial wrapper is absent or the source was restored, not task completion.

### Strategy Adjustments
- Next session should stay on C0.5.4.4.3. Do not begin C0.5.4.5 until the wrapper theorem is proved, reviewed, and committed if prompted.
- Use an explicit forward application of `extcall_after_state_update_tail_sound_cond_driver_ih`: specialize it, prove its antecedent with `impl_tac`/controlled `conj_tac`, then use the resulting conclusion; this may avoid `irule`/existential matching quirks.
- If the current `MATCH_MP_TAC` edit fails badly, restore just the wrapper proof body to the last readable `irule`/explicit-witness shape from E0268 or rewrite the proof by copying the old helper proof directly with the live `get_tenv` equation.
- Keep edits confined to `semantics/prop/vyperTypeStmtSoundnessScript.sml`; do not stage untracked `LEARNINGS_type_system_rewrite.legacy.md` or `tmp_helper.txt`; commit with `--no-gpg-sign` only after focused build is clean and strategist review accepts a proved component.

### Oracle Feedback
- Held: E0267 review correctly identified the real interface mismatch as `get_tenv cx` versus `env.type_defs` and introduced the right small boundary-lemma component C0.5.4.4.3.
- Held: C0.5.4.4.3 should not mention generated prefix operations; all wrapper attempts so far stayed prefix-free.
- Still unvalidated: the wrapper is claimed Risk 2/straightforward, but tactic structuring around the old helper has not yet built. If simple explicit application fails again, escalate rather than tactic-thrashing.

## Evidence Pointers
- episode:E0267 - C0.5.4.5 stuck: old env.type_defs helper mismatch and generated-prefix route forbidden
- episode:E0268 - nonterminal checkpoint for C0.5.4.4.3 wrapper insertion/proof attempts
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4922_t001 - strategist introduced live-tenv wrapper plan
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4925_t001 - inserted wrapper theorem statement/source location
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4926_t001 - naive old-helper application timed out on structured conjunction
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4935_t001 - FAIL_TAC probe showed compact existential-packed old-helper obligation after four premises
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4940_t001 - explicit specialization exposed conditional-driver-IH premise ordering
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4947_t001 - `irule`/explicit witness proof shape hit holbuild no-goals instrumentation failure
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4949_t002 - git status at handoff: source/PLAN/DOSSIER modified plus untracked legacy/temp files
