# STATE_callable_entry_initial_state
Updated: 2026-06-03

## Cursor
- component: none
- status: ready
- active_file: none
- next_action: No proof components remain. If this task is resumed, first run query_plan() and git status; if PLAN still has no frontier and only unrelated untracked docs remain, propose end_session(outcome='complete') with the existing build/integrity evidence.
- expected_goal_shape: No HOL goal expected; PLAN reports all components C1-C4 done, no scheduled frontier, no Oracle next.
- verify_with: holbuild(targets=['vyperTypeInitialStateTheory'], timeout=600) -- note: after all components are closed the harness may block new builds; use existing success evidence TO_callable_entry_initial_state-20260603T143413Z_m0112_t001 unless an active component/frontier is reopened.

## If This Fails
- If query_plan unexpectedly shows remaining work, begin exactly Oracle next before any edit/build. If holbuild is authorized and fails, inspect the goal/error, record checkpoint_progress for the relevant component if partial evidence is meaningful, and do not redesign without plan_oracle.

## Do Not Retry
- Run holbuild when PLAN has no active component and no executable frontier.: The harness blocks builds after all components are closed; use existing authorized build evidence or reopen/begin a component only if PLAN changes.
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0116_t001
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0112_t001
- Stage or commit unrelated untracked docs/PROGRESS-*.md files for this task.: They are unrelated pre-existing/untracked docs; task-owned source and memory files were already committed separately.
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0127_t001
- Rework C3 using lower-level eval_stmts_no_type_error or reprove entry invariants.: C3 already builds with the planned direct corollary proof via C2 plus typed_stmts_no_type_error.
  - evidence: episode:E0006
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0082_t001
- Force `initial_machine_state` as the unused C4 `am` existential witness.: The existential `am` is irrelevant to the obligations; using it caused a polymorphic type constraint failure. Use `ARB` and choose the actual `st` witness separately if this proof is revisited.
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0105_t001
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0112_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not needed for completion but worth noting: C4 could have used a named empty typing_env helper to avoid duplicating the record literal; current one-off proof is acceptable for a satisfiability corollary.
- The PLAN decomposition was the right abstraction: C1 boundary lemmas made C2 assembly-style, C3 a direct corollary, and C4 a separate empty-witness theorem rather than forcing a fake callable entry.
- No indication of optimizing the wrong theorem/definition remains; all frozen theorem statements were preserved and proved.
- Do not continue tactic search on this task; PLAN has no frontier and all required components are done/reviewed.
- A fresh expert would first question final proof-integrity: confirm no cheats in vyperTypeInitialStateScript.sml, no non-DISK_THM oracle tags in available theorem indexes, and no task-owned uncommitted changes.

### What Went Wrong
- Final verification with holbuild after all components closed was blocked by the PLAN gate, so the final completion proposal relied on the last authorized successful build for C4 rather than a new post-commit build. Evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0116_t001 and tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0112_t001.
- C4 had routine tactic/namespace issues: unqualified vfmState/vyperState definitions were not in scope, `initial_machine_state` witness parsing hit a polymorphic constraint, and lookup_scopes_def needed qualification. These were tactical, not statement/decomposition issues.
- Earlier C2 review had been blocked by OracleBudgetExceeded; retrying a minimal review request resolved it at session start.

### Ignored Signals
- The final query_plan clearly reported no beginable component and allowed end_session complete; trying a new holbuild afterward was unnecessary and predictably blocked by the harness gate.
- The C4 existential variable `am` is unused in the conclusion's conjuncts; trying to force `initial_machine_state` as that witness was unnecessary. `ARB` avoided the type constraint issue, while `st` separately used `initial_state initial_machine_state [FEMPTY]`.
- Untracked docs/PROGRESS files were unrelated and should remain unstaged; only task-owned source/memory files were committed.

### Strategy Adjustments
- For post-component reviews, keep plan_oracle requests minimal with evidence IDs only; this avoided the earlier OracleBudgetExceeded issue.
- When proving existential satisfiability with records, prefer robust witnesses (`ARB` for irrelevant existentials, explicit record literals for typing_env) and qualify external theory definitions (`vfmStateTheory.*`, `vyperStateTheory.*`) when simplification names are not imported.
- Use the structured PLAN gate as source of truth: once no frontier remains, do not attempt further builds/edits unless the harness/PLAN reopens a component.

### Oracle Feedback
- Strategist insight held for C3: `callable_entry_no_type_error` was discharged directly by `callable_entry_establishes_type_soundness_preconditions` plus `typed_stmts_no_type_error` with no lower-level soundness proof.
- Strategist insight held for C4: an empty context/state/env witness makes the preconditions satisfiable and simplifies by definitions; no callable lookup is needed.
- Strategist insight held overall: reusable C1 boundary lemmas prevented duplication and kept the frozen main theorem proof short.

## Evidence Pointers
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0112_t001 - last authorized holbuild success for vyperTypeInitialStateTheory after C4 proof
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0122_t001 - grep found no cheat/CHEAT in semantics/prop/vyperTypeInitialStateScript.sml
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0122_t002 - grep found no non-DISK_THM oracle tags in available *Theory.txt files
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0127_t001 - final git status only had unrelated untracked docs/PROGRESS files
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0129_t003 - PLAN reports all components done and no frontier
- episode:E0006 - C3 proved/reviewed
- episode:E0007 - C4 proved/reviewed
