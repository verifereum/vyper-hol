# STATE_type_system_rewrite
Updated: 2026-05-21

## Cursor
- component: C2.0.2.3.2.1.1
- status: ready
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Begin component C2.0.2.3.2.1.1. Add theorem `for_cons_ordinary_exception_return_typed_from_body_ih` before `eval_for_cons_type_sound_core`, using the exact body-IH premise shape from `eval_for_cons_type_sound_core`. Prove it by specializing the body IH at `stp`, `INR y`, `st_body`, discharging pushed-state premises, then using existing `for_cons_ordinary_exception_return_typed_from_case_premise` or `return_exception_typed_extend_local_env_extends` outside the suspended core endpoint. Current source has a partial failing endpoint patch around lines 4639-4651; after helper is proved, component C2.0.2.3.2.1.2 should replace that endpoint with a helper call.
- expected_goal_shape: For C2.0.2.3.2.1.1 helper: after specializing the body IH, expect a standalone theorem goal containing the specialized conclusion with `case (INR y) of ... ?env_exn ...`; this is safe to consume in the standalone helper. The helper conclusion must be exactly `return_exception_typed env ret_ty y`, with no local `env_exn` witness or `case` in the conclusion.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If proving the standalone helper still leaves an existential/case premise at the helper conclusion or hits CHOOSE validation, use checkpoint_progress for C2.0.2.3.2.1.1 and escalate/close stuck only if the helper boundary itself is terminally invalid. Do not retry endpoint-local case/existential consumption.

## Do Not Retry
- Universal body-IH transport inside `eval_for_cons_type_sound_core` (`for_cons_body_ih_premise_transport`, theorem-level MATCH_MP of whole body IH, or any path that leaves `!stp res_body st_body. ...`).: Repeatedly reproduces CHOOSE-origin validation and leaves/accepts a full universal body-IH premise in the suspended core endpoint.
  - evidence: episode:E0569
  - evidence: episode:E0571
  - evidence: tool_output:TO_type_system_rewrite-20260521T121230Z_m35175_t001
- Endpoint-local destruction or acceptance of `case (INR y) of ... ?env_exn ...`, including `qexists env_exn`, explicit `conj_tac`/`ACCEPT_TAC`, `LIST_CONJ`, `disch_then ACCEPT_TAC`, `mp_tac >> simp[sum_case_def]`, or MATCH_MP through existing case-premise helpers inside `eval_for_cons_type_sound_core`.: E0571 shows the visible concrete assumption can be alpha-equivalent to the goal yet still fail with CHOOSE/Q_TAC validation in the suspended/instrumented endpoint context.
  - evidence: episode:E0571
  - evidence: tool_output:TO_type_system_rewrite-20260521T121230Z_m35230_t001
  - evidence: tool_output:TO_type_system_rewrite-20260521T121230Z_m35255_t001
- Broad `gvs[sum_case_def]` over the large For-cons endpoint context.: Timed out previously; any remaining simplification should be in the standalone helper or tightly local, not over the endpoint context.
  - evidence: tool_output:TO_type_system_rewrite-20260521T121230Z_m35197_t001
- Continuing to patch the current partial endpoint source as if it were a valid prefix.: Current source around lines 4639-4651 is a failed partial attempt using `for_cons_ordinary_exception_return_typed_from_case_premise`; next plan replaces this with helper-first work.
  - evidence: tool_output:TO_type_system_rewrite-20260521T121230Z_m35277_t001
  - evidence: tool_output:TO_type_system_rewrite-20260521T121230Z_m35279_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not yet tried: bypass the endpoint’s case/existential entirely by deriving the return-typed fact from the universal body IH in a standalone helper before entering the suspended core proof; this is now the PLAN.
- We were optimizing the endpoint tactic instead of the proof boundary. The theorem/invariant and induction variable are not the issue; the abstraction boundary is.
- The PLAN decomposition is now the right abstraction if the helper proves: body-IH specialization and existential elimination happen once in a standalone theorem, while the endpoint only applies a non-existential fact.
- If the helper itself fails in the same way, a fresh expert should question the helper statement alignment with `eval_for_cons_type_sound_core`’s body-IH premise, not resume endpoint thrashing.
- A fresh expert should first inspect the partial source around lines 4639-4651 and the new PLAN component statement, then add the helper before touching the endpoint.

### What Went Wrong
- I kept trying to solve an endpoint-local proof-shape problem with endpoint-local tactics. E0571 shows that in this suspended/instrumented core context even alpha-equivalent assumptions and trivial implications over the concrete `case (INR y)`/existential can fail validation.
- The semantic fact was never in doubt: the body IH gives an extended environment with `return_exception_typed env_exn ret_ty y`, and environment extension transports it back to `env`. The mistake was choosing a boundary that still required consuming the CHOOSE witness inside `eval_for_cons_type_sound_core`.
- The current file is left in a partial failing state around `eval_for_cons_type_sound_core` lines 4639-4651. This was intentional evidence for E0571, not a valid proof prefix.

### Ignored Signals
- Repeated CHOOSE/Q_TAC validation failures on visually trivial goals were a strong signal that the decomposition, not the tactic, was wrong.
- The large endpoint context and prior `gvs[sum_case_def]` timeout indicated the endpoint should not own existential/case reasoning.
- Existing standalone helpers that successfully consume similar existential/case facts outside the endpoint showed the right direction earlier; the failed endpoint kept reintroducing the same boundary problem.

### Strategy Adjustments
- Follow the new PLAN exactly: first prove a non-existential body-IH return-typing helper as C2.0.2.3.2.1.1, then patch the endpoint as C2.0.2.3.2.1.2.
- The helper conclusion should be only `return_exception_typed env ret_ty y`; no `?env_exn`, no `case (INR y)`, no popped-state suffix. Popped state/account/env/no-type-error are already available in the endpoint.
- When patching the endpoint later, split easy non-existential conjuncts and call the helper for return typing. Do not select or destruct the concrete body-IH case premise locally.

### Oracle Feedback
- The previous projection insight held partially: it eliminated the universal body-IH subgoal, but missed that local consumption of the concrete existential/case premise is also validation-sensitive.
- The latest oracle review is better aligned with evidence: it rebases to a standalone non-existential boundary helper and explicitly says endpoint goals mentioning `?env_exn` or `case (INR y)` mean the boundary is too weak.
- The overall For-cons invariant and statement theorem are still considered valid; no definition or invariant redesign is currently needed.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35280_t003 - current PLAN/frontier: no high-risk components; beginable next is C2.0.2.3.2.1.1
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35279_t001 - strategist review replaced stuck endpoint plan with helper-first components C2.0.2.3.2.1.1 and C2.0.2.3.2.1.2
- episode:E0571 - terminal stuck evidence for endpoint-local existential/case consumption
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35277_t001 - latest failed endpoint: visible assumption 27 matches case goal up to binder names but qpat acceptance fails with Q_TAC/FIRST_ASSUM validation
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35270_t001 - existing case-premise helper applied in endpoint still leaves alpha-equivalent case premise and fails with CHOOSE
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35255_t001 - even trivial `P ==> P` after moving `return_exception_typed` assumption fails with CHOOSE in endpoint
