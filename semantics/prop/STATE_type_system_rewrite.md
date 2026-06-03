# STATE_type_system_rewrite
Updated: 2026-06-03

## Cursor
- component: C0.5.4.5.1.2
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit, build, or begin proof work unless the user/maintainer has supplied a new explicit unblock. First query_plan(); if it still shows no beginable frontier and no new instruction changes the proof-interface constraints, report end_session(outcome='blocked'). If a new unblock exists, call plan_oracle with that instruction and the C0.5.4.5.1.2 evidence to request a low-risk executable frontier.
- expected_goal_shape: No authorized proof goal under the current PLAN. The remaining source obligation is the final `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]`; applying `extcall_nonstatic_success_tail_sound_cond_driver_ih` leaves the missing compact optional-driver IH premise as a large existential/conditional package.
- verify_with: Only after a future PLAN creates a beginable low-risk component: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600). Current PLAN gate blocks holbuild because high-risk blockers have no frontier.

## If This Fails
- If a future authorized plan again requires broad cleanup or brittle generated-IH plumbing, stop immediately. Use checkpoint_progress for partial, nonterminal evidence; close_component(result='stuck', diagnosis_tag='risk_mismatch' or 'plan_incomplete') only for a terminal failure, then call plan_oracle review.

## Do Not Retry
- Generic `res_tac`, `imp_res_tac`, or `metis_tac[]` over the full Resume context to instantiate the generated optional-driver IH.: Timed out even with prefix facts present and was invalidated by strategist/maintainer constraints; it searches the generated context rather than exposing a compact branch-local premise.
  - evidence: episode:E0320
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m5852_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m5856_t001
- Goal-directed generated-IH consumption by `first_x_assum`, `last_x_assum`, `qpat_x_assum`, or ASSUM_LIST numeric indexing.: E0323 showed selector-based application did not cleanly find/apply the huge generated IH; ASSUM_LIST indexing is brittle and timed out, violating the task stop condition.
  - evidence: episode:E0323
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m5881_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m5897_t001
- Close the Resume by only applying `extcall_nonstatic_success_tail_sound_cond_driver_ih` and simplifying/conjoining the result.: The theorem matches the postcondition but leaves the missing conditional driver-premise existential package; simplification timed out on a large design-signal goal.
  - evidence: episode:E0324
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m5907_t001
- Revive outside-Resume bridge theorem or build a generated-prefix adapter replaying the ExtCall prefix into the optional-driver IH.: Earlier bridge attempts were brittle, parser/name-fragile, and timed out; maintainer clarification forbids long generated-prefix adapter plumbing under the current task constraints.
  - evidence: episode:E0315
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m5784_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m5788_t001
- Broad `simp`/`gvs`/`AllCaseEqs()` cleanup over the whole ExtCall prefix or long `qspecl_then` lists over generated binders/ASSUME-quoted assumptions.: Explicitly forbidden by maintainer clarification and repeatedly associated with large goals, timeouts, no-goals replay, and generated-context fragility.
  - evidence: source:semantics/prop/TASK_type_system_rewrite.md
  - evidence: episode:E0311
  - evidence: episode:E0317

## Reflection
### Tunnel Vision Check
- Outside-the-box approach still needed: change the proof-generator/Resume interface or proof boundary so the optional-driver expression IH is exposed as a compact branch-local premise before the ExtCall success tail, rather than buried in a generated continuation assumption.
- A fresh expert should question C0.5.4.5.1’s decomposition: producer and consumer were split, but the producer premise is not actually obtainable under current constraints. Optimizing the tail theorem or suffix tactics is likely the wrong target.
- The semantic theorem still appears likely true; the failure is proof-interface access to the generated optional-driver IH, not the validity of `extcall_nonstatic_success_tail_sound_cond_driver_ih`.
- Do not retry tactics. Evidence now spans resolution, goal-directed assumption selection, context indexing, and direct tail theorem application. This is a boundary/interface issue requiring maintainer/strategist action.
- Fresh expert first question: can the mutual induction/Resume be refactored so the recursive eval_expr call for `THE drv` is named and exported locally at the exact branch point, without replaying the whole generated prefix?

### What Went Wrong
- The PLAN assumption that the generated optional-driver IH could be consumed goal-directed after reaching the concrete success branch was false. E0323 showed first/last/qpat selection failed and ASSUM_LIST indexing timed out.
- C0.5.4.5.1.4/tail consumption was scheduled as if the driver premise existed. E0324 showed direct use of the tail theorem matches the postcondition but leaves exactly the missing driver-premise package; simplifying that package timed out and produced a >4KiB design-signal goal.
- The latest strategist augment confirmed the current leaf is terminally blocked under the scoped proof interface; no low-risk child proof is authorized until an ancestor-level interface change or maintainer relaxation exists.
- A user-requested holbuild check at session start could not be performed because the PLAN gate blocked builds while high-risk components have no frontier.

### Ignored Signals
- E0311/E0315/E0320/E0323 all pointed to the same generated-IH interface problem; treating later suffix proof leaves as tactical was stale after E0323.
- The >4KiB conditional driver-premise package after tail-theorem application was a decomposition smell, not a request for stronger simplification.
- The task says the proof should be straightforward and to stop on design/plan issues; continuing local suffix experiments would violate that stop condition.
- The source is intentionally partial and stable through a cheat; it should not be treated as completion or committed as a completed proof.

### Strategy Adjustments
- Next session should perform no proof action unless new maintainer/strategist instructions explicitly change the proof interface or constraints.
- Any future plan should produce a fact that exactly matches the conditional driver premise consumed by `extcall_nonstatic_success_tail_sound_cond_driver_ih`, with ExtCall prefix operations already discharged in a stable, branch-local way.
- Keep the current useful partial source: local tail theorem plus value-extraction/calldata prefix facts. Do not retain or revive failed generated-IH suffixes.
- If a stable checkpoint commit is considered, first inspect git status/diff; stage only relevant task-owned files and commit with `git commit --no-gpg-sign`. Do not claim final completion while cheats remain.

### Oracle Feedback
- Held: the strategist correctly preserved the local tail theorem and prefix facts as useful carry-forward evidence.
- Missed earlier: the claim that generated IH could be consumed goal-directed as Risk 2 was falsified by E0323 under holbuild/tactic constraints.
- Corrected later: the latest augment `TO_type_system_rewrite-20260602T195240Z_m5921_t001` explicitly classifies C0.5.4.5.1.2 as terminal blocked proof-interface status and says to report blocked rather than continue proof search.
- Current binding state: query_plan still shows no scheduled leaf frontier and no beginable component; proof work/builds are gated.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260602T195240Z_m5923_t003 - latest query_plan: high-risk blockers remain, no scheduled leaf frontier, no beginable component
- tool_output:TO_type_system_rewrite-20260602T195240Z_m5921_t001 - strategist augment: C0.5.4.5.1.2 is terminal blocked proof-interface status; do not prove/build under current constraints
- tool_output:TO_type_system_rewrite-20260602T195240Z_m5919_t001 - attempted holbuild was blocked by PLAN gate due to high-risk components with no frontier
- tool_output:TO_type_system_rewrite-20260602T195240Z_m5920_t003 - git diff/source shows stable local tail theorem and prefix facts, but final Resume still ends in cheat
- tool_output:TO_type_system_rewrite-20260602T195240Z_m5920_t004 - grep confirms remaining cheats in vyperTypeStmtSoundnessScript.sml including ExtCall nonstatic success
- tool_output:TO_type_system_rewrite-20260602T195240Z_m5923_t002 - dossier for C0.5.4.5.1.2 summarizing E0305/E0307/E0317/E0319/E0322 evidence
- episode:E0323 - generated optional-driver IH consumption by goal-directed selection/context indexing failed; suffix reverted
- episode:E0324 - direct tail theorem application failed, leaving missing driver-premise package; suffix reverted
- episode:E0322 - stable prefix facts audited and retained
