# STATE_type_system_rewrite
Updated: 2026-05-20

## Cursor
- component: C2.0.2.2.1
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Stay on C2.0.2.2.1. Inspect `for_cons_body_ih_exception_projection` around line ~1693. Do not edit `eval_for_cons_type_sound_core`. Replace the current incomplete proof/statement with a safer projection boundary, preferably one that returns the exact full specialized body-IH conjunction (`state_well_typed st_body /\ accounts_well_typed st_body.accounts /\ no_type_error_result (INR exn) /\ ?env_exn. ...`) as a whole without opening/reconstructing the existential in tactic context; then rebuild.
- expected_goal_shape: Current holbuild failure is in `for_cons_body_ih_exception_projection`: after specializing the body IH with `assume_tac` and `gvs[sum_case_def]`, source attempts `qexists_tac `env_exn` >> ACCEPT_TAC (LIST_CONJ [...])`; holbuild shows the remaining goal is `env_extends ... env_exn /\ env_consistent env_exn cx st_body /\ return_exception_typed env_exn ret_ty exn` with exact assumptions present, but validation fails with `Thm.GEN: variable occurs free in hypotheses`.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If the full-conjunction projection refactor still reduces to exact-assumption/GEN/CHOOSE endpoints, do not continue endpoint tactic retries. Use `close_episode(result="stuck", diagnosis_tag="risk_mismatch", component_id="C2.0.2.2.1", evidence_ids=[...])`, then call `plan_oracle(mode="review", component_id="C2.0.2.2.1", evidence_ids=[...])` for a replacement interface.

## Do Not Retry
- More endpoint variations after destructing the body-IH existential, such as `first_assum ACCEPT_TAC`, `qpat_assum ACCEPT_TAC`, `metis_tac[]`, `rw`, `disch_then ACCEPT_TAC`, `qexists_tac` followed by exact assumptions, or explicit `ASSUME`/`LIST_CONJ`.: These repeatedly reduced to exact-looking assumptions/goals but failed validation (`no theorem proved`, `FOL_FIND no solution`, `Thm.GEN variable occurs free in hypotheses`). The problem is the proof boundary, not the final tactic.
  - evidence: tool_output:TO_type_system_rewrite-20260520T182357Z_m34627_t001
  - evidence: tool_output:TO_type_system_rewrite-20260520T182357Z_m34644_t001
  - evidence: tool_output:TO_type_system_rewrite-20260520T182357Z_m34650_t001
- Opening the existential from the body IH with `gvs[sum_case_def]` and then reconstructing `?env_exn` in the same proof context.: This creates a free `env_exn` in hypotheses and triggers GEN/validation problems when trying to prove the existential-conjunction goal. Keep the existential packaged across theorem boundaries instead.
  - evidence: tool_output:TO_type_system_rewrite-20260520T182357Z_m34648_t001
  - evidence: tool_output:TO_type_system_rewrite-20260520T182357Z_m34657_t001
- Editing `eval_for_cons_type_sound_core` or deleting `suspend "ReturnException_tail"` before the helper boundary is proved.: PLAN explicitly gates the core patch behind C2.0.2.2.2; entering the core proof re-enters the known hostile CHOOSE context.
  - evidence: tool_output:TO_type_system_rewrite-20260520T182357Z_m34658_t004
  - evidence: episode:E0546

## Reflection
### Tunnel Vision Check
- Outside-the-box approach: avoid any projection that splits a conjunction; instead prove a theorem whose conclusion is definitionally identical to the body-IH specialized consequent and let downstream lemmas use `cj`/rewrite on the theorem object, not in a tactic goal.
- We may be optimizing the wrong helper: `for_cons_body_ih_exception_projection` may be unnecessary if `for_cons_non_loop_exception_suffix` can take the full specialized body-IH result as an antecedent, with a separate theorem only for ReturnException weakening.
- The PLAN decomposition is close but C2.0.2.2.1's abstraction may still leak implementation details (existential witness reconstruction). A fresh expert should question the theorem statement before touching tactics.
- If the next attempt again reaches exact assumptions with `env_exn` free in hypotheses, stop and escalate; do not try more variants of `ACCEPT_TAC`, `metis_tac`, or `simp`.

### What Went Wrong
- I treated the packaged projection as a routine strengthening, but even after broadening the conclusion, the proof still destructs the body-IH existential and reconstructs a conjunction from a fresh witness; that repeats the same HOL4 validation brittleness seen in E0549.
- I kept trying endpoint variants (`metis_tac[]`, `rw`, `disch_then ACCEPT_TAC`, `qexists_tac`, explicit `ASSUME`/`LIST_CONJ`) after the goal clearly had exact assumptions. This was tactic thrashing, not proof progress.
- The current source is partial: `for_cons_body_ih_exception_projection` is inserted and incomplete; `vyperTypeStmtSoundnessTheory` does not build.

### Ignored Signals
- Repeated `no theorem proved` / `Thm.GEN variable occurs free in hypotheses` on exact-looking goals is a proof-interface problem, not a missing final tactic.
- The PLAN warning to keep the existential packaged was underweighted: opening it via `gvs[sum_case_def]` and then trying to rebuild `?env_exn` is exactly what causes validation trouble.
- The older do-not-retry warning about exact-assumption endpoints applied just as much to the new projection lemma as to the old suffix helper.

### Strategy Adjustments
- Next session should first change the theorem boundary so the final proof does not need to split/reconstruct the existential. Candidate: prove/consume a theorem whose conclusion is exactly the full specialized body-IH result, or make the later suffix consume the full result directly.
- Avoid `mp_tac`/`strip_tac` and avoid introducing a free `env_exn` unless it is hidden inside a theorem conclusion, not a tactic-context hypothesis.
- Do not edit the core theorem or remove `suspend "ReturnException_tail"` until C2.0.2.2.1 and C2.0.2.2.2 are closed/reviewed.

### Oracle Feedback
- Strategist insight that helper-first staging is required remains correct; query_plan now properly gates C2.0.2.3 behind C2.0.2.2.2.
- The current C2.0.2.2.1 statement may still be too low-level because it asks the proof to project and reconstruct existential evidence. A fresh review may need to replace it with a full-specialization lemma rather than another endpoint tactic.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260520T182357Z_m34658_t004 - plan/frontier: active component remains C2.0.2.2.1; next work must stay there
- tool_output:TO_type_system_rewrite-20260520T182357Z_m34659_t001 - checkpoint E0551 recorded for non-terminal progress on C2.0.2.2.1
- tool_output:TO_type_system_rewrite-20260520T182357Z_m34657_t001 - current exact witness-conjunction endpoint fails with `Thm.GEN variable occurs free in hypotheses`
- tool_output:TO_type_system_rewrite-20260520T182357Z_m34650_t001 - `metis_tac[]` failed on exact `no_type_error_result` assumption after body-IH specialization
- tool_output:TO_type_system_rewrite-20260520T182357Z_m34648_t001 - after `assume_tac`/`gvs[sum_case_def]`, goal is no-TypeError plus packaged existential with exact facts in assumptions
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:1693 - inserted incomplete `for_cons_body_ih_exception_projection` theorem
