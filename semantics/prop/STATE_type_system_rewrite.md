# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.5.4.4.1
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Retry the required strategist review for closed stuck episode E0264 before any begin_component/build/edit: plan_oracle(mode='review', component_id='C0.5.4.4.1', evidence_ids=['TO_type_system_rewrite-20260602T195240Z_m4864_t001','TO_type_system_rewrite-20260602T195240Z_m4866_t001','TO_type_system_rewrite-20260602T195240Z_m4867_t001','TO_type_system_rewrite-20260602T195240Z_m4868_t001'], planning_reason='review closed episode E0264'). Two review attempts already failed with OracleBudgetExceeded; query_plan shows this review is the only allowed next action.
- expected_goal_shape: No active HOL goal. Source was restored to HEAD after the failed C0.5.4.4.1 probe and focused holbuild was clean, with the planned `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]: cheat` still present. PLAN gate is blocked by unresolved E0264; no beginable frontier exists until strategist review succeeds.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If E0264 review again fails due OracleBudgetExceeded/tooling, do not edit/build; retry review if permitted, otherwise report blocked(tooling_bug/unknown) with TO_type_system_rewrite-20260602T195240Z_m4870_t001, TO_type_system_rewrite-20260602T195240Z_m4872_t001, and query_plan evidence TO_type_system_rewrite-20260602T195240Z_m4871_t001. If review returns a repaired PLAN, follow the new Oracle next exactly.

## Do Not Retry
- Recover the optional-driver IH inside `Expr_Call_ExtCall_nonstatic_success` by broad simplification of the generated prefix or whole ExtCall prefix.: E0257 already showed this recreates the forbidden generated-prefix simplification and times out; the success subresume must not reconstruct the driver premise locally.
  - evidence: episode:E0257
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4781_t001
- Apply `drule_all extcall_success_continuation_sound_cond_driver_ih` directly in the current success subresume without a compact conditional driver IH and matching tail equation.: The live branch equation is the post-update tail and the helper requires the optional-driver IH separately; direct matching failed.
  - evidence: episode:E0257
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4772_t001
- Replay static proof's parent-boundary sequence `qmatch_abbrev_tac; first_x_assum drule; disch_then drule` in the nonstatic parent success branch.: E0262 showed the nonstatic generated optional-driver IH has a different/extra prefix shape and the second `drule` does not match.
  - evidence: episode:E0262
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4825_t001
- Use long manual `qspecl_then` lists over generated ExtCall prefix variables to derive the compact driver IH.: This is forbidden generated-prefix adapter plumbing, stalled on prefix subgoals, and violates the proof-interface discipline.
  - evidence: episode:E0262
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4828_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4849_t001
- Retry C0.5.4.4.1's sufficient stronger conjunction plus `first_x_assum irule` over the same generated optional-driver universal in the same late parent success context.: E0264 directly tested this refined plan; it timed out and exposed the same huge generated-prefix/whole-tail goal instead of a compact IH.
  - evidence: episode:E0264
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4864_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4866_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach to consider next: stop trying to extract the optional-driver IH from the generated mutual IH inside the late success branch. A fresh expert should ask whether the driver case can be factored before ExtCall prefix generation, or whether a small helper around `eval_all_type_sound_mutual` can expose the optional driver IH without the generated prefix.
- We may be optimizing the wrong boundary: the parent suspend payload might be too late. The concrete success branch has already accumulated a huge generated prefix; the right abstraction may be an earlier branch-local helper or a direct continuation proof that avoids exposing the generated universal.
- The PLAN decomposition after E0264 is not yet trustworthy; its key de-risking claim (goal-directed `irule` over the generated optional-driver IH) failed. Do not treat this as a tactic-search problem until the strategist reviews E0264.
- Fresh expert question: why is the optional driver theorem tied to the whole ExtCall prefix at all? Can we prove a standalone theorem about `well_typed_opt env drv` and the mutual theorem's expression case, or carry the needed IH from the original mutual induction before entering ExtCall prefix code?

### What Went Wrong
- C0.5.4.1, C0.5.4.2, and C0.5.4.3 carry-forward leaves were reviewed/closed and source stayed build-clean; commits were made with `--no-gpg-sign` for E0260/E0261 bookkeeping.
- C0.5.4.4 old parent-boundary approach failed: static-style `qmatch_abbrev_tac; first_x_assum drule; disch_then drule` did not match the nonstatic generated IH shape, and manual `qspecl_then` over generated variables became forbidden brittle prefix plumbing. Source was restored and build-clean; episode E0262 records this.
- The oracle decomposed C0.5.4.4 into C0.5.4.4.1/.2, but scheduler initially made C0.5.4.5 beginable. E0263 was closed as plan_incomplete/scheduling conflict with no proof edits; oracle then repaired dependencies so C0.5.4.4.1 became next.
- C0.5.4.4.1 probe failed exactly at its failure condition: sufficient stronger conjunction plus goal-directed `first_x_assum irule` over the generated optional-driver IH timed out and exposed the large generated-prefix/whole-tail goal. Source was restored and focused holbuild clean; E0264 was closed stuck/risk_mismatch.
- The required E0264 review failed twice with OracleBudgetExceeded, leaving the PLAN gate blocked with no beginable components.

### Ignored Signals
- The generated optional-driver IH's antecedent is not just a small prefix: even goal-directed `irule` leaves a huge goal containing the whole generated ExtCall prefix and continuation tail, a strong signal that the interface is wrong-shaped for late-branch extraction.
- The plan's instruction to avoid generated-prefix plumbing was correct, but the replacement still relied on the same generated universal becoming manageable by unification; E0264 shows that assumption was under-validated.
- A clean focused build is only source stability here; the nonstatic success subresume remains cheated and must not be mistaken for proof progress.

### Strategy Adjustments
- Next session must not begin any component or edit/build until the E0264 strategist review succeeds or explicitly repairs the plan. query_plan currently confirms this as the only legal action.
- When review succeeds, prefer a redesigned interface that does not rely on late `irule` over the generated universal. Ask for a higher-level helper/boundary if the returned plan still looks like generated-prefix extraction.
- Keep source edits confined to `semantics/prop/vyperTypeStmtSoundnessScript.sml`; do not alter evaluator/semantics definitions and do not edit outside `semantics/prop`.
- Do not stage untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`. Current tracked diffs are PLAN/DOSSIER from recorded episodes/reviews; leave them for the next stable checkpoint unless instructed by commit prompt.

### Oracle Feedback
- Held: E0262 review correctly recognized that C0.5.4.5 must wait for a compact optional-driver IH boundary and repaired the earlier scheduling conflict after E0263.
- Missed: The refined C0.5.4.4.1 plan claimed goal-directed `irule` over the generated optional-driver IH would instantiate prefix variables without explicit plumbing; E0264 falsified this in the actual goal state.
- Tooling blocker: Two required E0264 review calls failed with OracleBudgetExceeded (TO_type_system_rewrite-20260602T195240Z_m4870_t001 and TO_type_system_rewrite-20260602T195240Z_m4872_t001), so the session ended blocked.

## Evidence Pointers
- episode:E0262 - old C0.5.4.4 parent-boundary/static-style and manual generated-prefix attempts failed and source was restored
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4825_t001 - static-style nonstatic parent derivation failed at `disch_then drule`
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4849_t001 - manual/generated-prefix route still exposed large prefix/equality obligations
- episode:E0263 - C0.5.4.5 was closed stuck only as scheduling/dependency mismatch, not theorem failure
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4858_t001 - begin_component C0.5.4.5 showed it required boundary from C0.5.4.4
- episode:E0264 - C0.5.4.4.1 goal-directed generated-IH probe failed and source restored
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4864_t001 - C0.5.4.4.1 `irule` probe timed out and exposed huge generated-prefix goal
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4868_t001 - focused holbuild clean after restoring source
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4871_t001 - query_plan shows no frontier and E0264 review as only allowed action
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4870_t001 - first E0264 review failed OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4872_t001 - second E0264 review failed OracleBudgetExceeded
