# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.2.3.2.2.3
- status: ready
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Begin/report C0.2.3.2.2.3 only after the documentation update episode is closed/reviewed. Do not do proof search. Report that the static ExtCall driver-tail is intentionally stabilized with a local cheat and remains blocked by the generated optional-driver IH proof-interface.
- expected_goal_shape: `vyperTypeStmtSoundnessTheory` builds with an intentional ExtCall cheat at the original static ExtCall tail proof point. There is no longer a diagnostic `FAIL_TAC "c0_2_3_2_2_2_1_isolated_static_driver_success"` or `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_driver_tail]` block in the stable source.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)

## If This Fails
- If a future build fails at Finalise with “No resumption proof found”, check that no orphan `suspend "Expr_Call_ExtCall_static_driver_tail"` or corresponding Resume mismatch has been reintroduced.
- If a future PLAN asks for local proof-producing work on the static driver tail, first cite E0200 and request/require an ancestor-level proof-boundary redesign; do not retry generated-prefix matching/simplification locally.

## Do Not Retry
- Directly prove compact `static_driver_ih` by `asm "generated_driver_ih" irule` after branch isolation.: It does not match the generated IH conclusion even in the isolated concrete static success branch; this is a proof-interface mismatch, not a missing simp lemma.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3864_t001
  - evidence: episode:E0200
- Assert the concrete generated-prefix conjunction and use `asm "generated_driver_ih" (drule_then (qspecl_then [...] mp_tac))`.: Branch-local forward chaining failed and still relies on brittle generated-prefix reconstruction.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3879_t001
  - evidence: episode:E0200
- Use `asm "generated_driver_ih" mp_tac >> simp[]` or broad simplification over the full generated prefix.: Timed out under the fixed 2.5s tactic limit and violates maintainer/PLAN restriction against broad generated-prefix traversal.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3882_t001
  - evidence: episode:E0176
  - evidence: episode:E0191
- Wrap driver-specific exact facts or compact-IH assertion in `TRY`.: Earlier evidence showed `TRY` can hide that desired facts/IH were never produced, making downstream markers misleading.
  - evidence: episode:E0196
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3834_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3835_t001
- Begin downstream ExtCall/RawCallTarget consumers before a reviewed producer for compact/static driver IH exists.: Those consumers depend on the compact driver IH; the current stable source has only an intentional ExtCall cheat.
  - evidence: episode:E0200
  - evidence: episode:E0201

## Reflection
### Tunnel Vision Check
- Branch isolation was useful but not sufficient: exact prefix facts do not make the generated optional-driver IH a usable local proof interface.
- The correct next proof-producing route, if any, is an ancestor-level proof-boundary redesign that exposes the optional-driver IH natively, not another local tactic under the old driver-tail producer.
- The current source is intentionally stable/buildable with a cheat; that is preferable to leaving diagnostic `FAIL_TAC` markers or orphan Resume blocks.

### What Went Wrong
- E0199 showed the proof can linearly reach a concrete static ExtCall driver-success branch with `generated_driver_ih`, run/update facts, and updated-state driver evaluation.
- E0200 showed the planned compact-IH producer is not straightforward: direct matching failed, explicit generated-prefix conjunction/forward chaining failed, and broad simplification timed out/violates the maintainer restriction.
- E0201 restored the source to a stable intentional-cheat baseline. Trying to put `cheat` only inside the Resume body failed Finalise; replacing the original suspend point with a local cheat built successfully.

### Strategy Adjustments
- Keep all edits under `semantics/prop`; do not change evaluator/semantics definitions.
- Do not perform further proof search for `Expr_Call_ExtCall_static_driver_tail` under the current decomposition.
- Future work requires maintainer-approved architecture changes inside `semantics/prop` or an explicit relaxation allowing generated-prefix adapter/plumbing.
- Commit only reviewed, build-verified stable checkpoints; use `git commit --no-gpg-sign`.

### Oracle Feedback
- E0201 was reviewed and accepted: stable cleanup is valid and does not claim to solve ExtCall.
- Proceed only to the status/report leaves, not downstream proof components.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3934_t001 - `vyperTypeStmtSoundnessTheory` builds after replacing the diagnostic static-driver-tail marker with an intentional local cheat.
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3921_t001 - `cheat` inside the Resume body failed Finalise with no resumption proof.
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3923_t001 - `RESUME_TAC >> cheat` inside the Resume body also failed Finalise.
- episode:E0201 - reviewed source cleanup/stabilization episode for C0.2.3.2.2.1.
- episode:E0199 - branch isolation proved/reviewed; concrete static driver-success facts were exposed.
- episode:E0200 - terminal risk_mismatch episode for compact-IH producer.
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3864_t001 - direct `generated_driver_ih` irule did not match compact IH.
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3879_t001 - explicit branch-prefix conjunction plus drule specialization failed.
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3882_t001 - local `mp_tac >> simp[]` over generated IH timed out.
