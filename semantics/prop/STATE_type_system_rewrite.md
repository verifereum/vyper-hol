# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.1.1.1
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Resolve the pending strategist-review gate created by E0036: call plan_oracle(mode='review', component_id='C0.1.1.1', evidence_ids=['TO_type_system_rewrite-20260601T081233Z_m0988_t001','TO_type_system_rewrite-20260601T081233Z_m0989_t001'], planning_reason='review closed episode E0036'). If accepted, immediately query_plan/begin the oracle-next C0.1.1.2 and replace `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]: cheat` with the direct-helper wrapper from plan TO_type_system_rewrite-20260601T081233Z_m1022_t001.
- expected_goal_shape: Before the pending review is cleared, query_plan reports Beginable now: none and Allowed next action is the E0036 plan_oracle review. After review acceptance, C0.1.1.2 should be beginable; its target proof is a short wrapper: split expression/place conjunct, place branch closes with type_place_expr_Call_ExtCall_NONE, expression branch applies extcall_expr_sound_from_generated_ih using generated eval_exprs IH and optional-driver IH.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)

## If This Fails
- If the pending plan_oracle review again returns OracleBudgetExceeded, do not edit/build; report/handle as planning-tool budget blocker or wait for reset. If the C0.1.1.2 direct-helper wrapper fails after begin_component, checkpoint_progress with exact holbuild goal; do not resurrect prefix-splitting/suspend experiments.

## Do Not Retry
- Retry the C0.1.1.2 prefix-skeleton plan by unfolding `evaluate_def`, splitting `eval_exprs`/`args_res`, and creating static/nonstatic nested suspend labels.: E0035 showed this path is not straightforward: broad simps timed out, nested suspends/placeholders caused parse/build structure failures, and the latest oracle invalidated this strategy in favor of a direct helper wrapper.
  - evidence: episode:E0035
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m0995_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m0998_t001
- Use assumption-enabled `simp[Once well_typed_expr_def]` or plain `simp[]` in the full ExtCall Resume context.: These time out on the large generated-prefix context. If call typing must be destructed, use `simp[NoAsms, Once well_typed_expr_def]` and targeted rewrites only.
  - evidence: episode:E0035
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m0995_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m0998_t001
- Run holbuild or edit source before clearing the pending E0036 strategist-review gate.: query_plan reports Beginable now: none and allowed next action is exactly the plan_oracle review for E0036; edits/builds are not authorized until that gate clears.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1027_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1029_t004
- Proceed to RawCallTarget or raw_call_return_type_well_formed before ExtCall is closed.: PLAN dependencies keep downstream obligations queued behind ExtCall; doing sibling work would hide the central blocker.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m0990_t002
  - evidence: plan:C0.2
  - evidence: plan:C0.3

## Reflection
### Tunnel Vision Check
- Fresh expert should question the old premise that ExtCall must be split into static/nonstatic suspended leaves: the latest oracle explicitly replaced that with a direct wrapper around extcall_expr_sound_from_generated_ih.
- Another outside-the-box route now authorized is to treat extcall_expr_sound_from_generated_ih as the abstraction boundary and avoid evaluator unfolding entirely inside the Resume.
- Do not optimize the monadic prefix theorem body or nested suspend mechanics; the active target is now matching generated IHs to an existing helper, similar to the IntCall wrapper.
- The apparent contradiction with older do-not-retry notes matters: do not manufacture a compact driver premise by broad prefix reconstruction, but do use the existing boundary theorem as the latest PLAN instructs.
- Fresh expert should first inspect lines ~17069-17116 IntCall and line ~17118 ExtCall, not the failed prefix experiments.

### What Went Wrong
- The first earlier-boundary refactor (E0031/E0032) was build-coherent but still suspended too early; FAIL_TAC showed the generated ExtCall prefix survived under the new label.
- The prefix-splitting repair (E0035) was not straightforward: `simp[Once well_typed_expr_def]` timed out unless assumptions were ignored, and plain `simp[]` after specializing the list IH timed out on the full prefix.
- Using `(impl_tac >- simp[]) >> strip_tac` did consume the generated eval_exprs IH and reached useful INL facts, but attempts to introduce nested suspend labels/branch cheats caused downstream parse/build errors; this path was reverted.
- A carry-forward audit E0036 was closed, but its required strategist review failed with OracleBudgetExceeded, leaving query_plan blocked with no beginable component.

### Ignored Signals
- Repeated >4KiB goals and timeout/store failures were design/interface signals, not invitations to tune simplifiers.
- Nested `suspend` inside the existing Resume caused parse/resume-structure trouble; continuing to fiddle with syntax would be tactic thrashing.
- The source STATE is stale relative to PLAN/DOSSIER; query_plan is authoritative and currently requires the E0036 review gate before C0.1.1.2 can begin.

### Strategy Adjustments
- First legal action next session is clearing the pending E0036 strategist review; do not build/edit before that unless the harness/plan gate changes.
- After review, follow latest plan TO_type_system_rewrite-20260601T081233Z_m1022_t001: direct-helper wrapper, no evaluator unfolding, no static/nonstatic suspends.
- Use the completed IntCall Resume as the template for capturing generated IHs and applying a local helper theorem.
- When destructing call typing, use `simp[NoAsms, Once well_typed_expr_def]` if needed; avoid assumption-enabled simplification in the huge Resume context.
- Keep all edits under semantics/prop and do not proceed to RawCallTarget or builtin lemma until ExtCall closes.

### Oracle Feedback
- Held: broad simplification / generated-prefix reconstruction is unsafe; E0035 confirmed timeouts/resource failures.
- Held: helper interface audit found the required local theorems; E0034/E0036 support relying on local ExtCall helper names.
- Missed/changed: the earlier oracle strategy to make focused static/nonstatic suspend leaves was build/parser fragile in this context; latest oracle replaced it with direct application of extcall_expr_sound_from_generated_ih.
- Latest binding insight: the ExtCall Resume should be a short wrapper around extcall_expr_sound_from_generated_ih plus type_place_expr_Call_ExtCall_NONE, structurally analogous to Expr_Call_IntCall.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1029_t004 - current query_plan: no beginable component until E0036 strategist review; C0.1.1.2 is oracle-next afterward
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1026_t001 - plan_oracle review for E0036 failed with OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1022_t001 - latest replacement plan: use extcall_expr_sound_from_generated_ih direct-helper wrapper, no prefix splitting
- episode:E0035 - prefix-skeleton/suspend attempt failed and was reverted; contains useful NoAsms/impl_tac evidence
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1020_t001 - source verified buildable after reverting failed C0.1.1.2 experiment to `Expr_Call_ExtCall_result: cheat`
- episode:E0034 - helper interface audit proved and reviewed; local ExtCall helper names confirmed
- tool_output:TO_type_system_rewrite-20260601T081233Z_m0989_t001 - strategist accepted E0034 audit
