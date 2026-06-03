# STATE_type_system_rewrite
Updated: 2026-06-03

## Cursor
- component: C0.6
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Run `holbuild(targets=['vyperTypeStmtSoundnessTheory'], timeout=600)` immediately to verify the current last edit (`mp_tac raw_call_bytes_slot_size_bound >> impl_tac >- first_assum ACCEPT_TAC`). Do not edit before seeing whether the remaining RawCall size/value subgoals close or change.
- expected_goal_shape: Current source is partial. Last verified failure was inside `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` after the successful RawCall prefix: assumptions include `run_ext_call ... = SOME (T,x1,x2,x3)`, `flags.rcf_max_outsize <> 0`, updated state well-typed/env-consistent, and remaining goals about dynamic bytes/tuple result typing or `word_size flags.rcf_max_outsize + 1 <= dimword(:256)` plus `LENGTH (TAKE flags.rcf_max_outsize x1) <= flags.rcf_max_outsize`. The top-level `∃ $var. ¬$var` in holbuild output is only a wrapper after a deeper unsolved subgoal.
- verify_with: holbuild(targets=['vyperTypeStmtSoundnessTheory'], timeout=600)

## If This Fails
- If only small size/value goals remain, finish with explicit use of `raw_call_bytes_slot_size_bound`, `listTheory.LENGTH_TAKE`, `value_has_type_def`, `evaluate_type_def`, and `raw_call_return_type_def`. If the goal is large/awkward or requires more theorem plumbing, call `checkpoint_progress` or close C0.6 stuck with diagnosis `missing_helper`/`risk_mismatch` and ask plan_oracle for a compact RawCall tail-result helper. Do not commit while the target is broken.

## Do Not Retry
- Do not use `drule raw_call_args_runtime_typed_dest` in the RawCall success branch.: It failed with a matching/predicate assertion; explicit `mp_tac raw_call_args_runtime_typed_dest >> impl_tac >- simp[]` matches the current assumptions and progressed.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6018_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6022_t001
- Do not use `drule raw_call_bytes_slot_size_bound` for the remaining dynamic bytes size goals.: It failed to find/match the antecedent in the simplified goal. The current unverified source uses explicit `mp_tac ... >> impl_tac >- first_assum ACCEPT_TAC`; verify that first.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6058_t001
- Do not chase or try to solve the top-level `∃ $var. ¬$var` wrapper by changing the opening `rpt gen_tac >> strip_tac`.: A temporary probe showed the Resume goal opens normally; the existential wrapper is holbuild's report after a deeper unsolved branch. The real goals are nested in the instrumented log.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6040_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6043_t001
- Do not commit current tracked changes.: `vyperTypeStmtSoundnessTheory` is not build-clean after partial C0.6 edits; git status shows tracked PLAN/STATE/source modifications and untracked scratch files.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6060_t002
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6061_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not yet tried: extract a local `raw_call_tail_result_sound_simp` helper analogous to `raw_log_tail_result_sound_simp` and `selfdestruct_tail_result_sound_simp`; this may be the right abstraction if the current inline proof keeps producing value-typing plumbing.
- A fresh expert should question whether C0.6 should be a single Resume proof or should first prove a RawCall tail boundary lemma over the post-`eval_exprs` monadic chain.
- The current proof may be optimizing the wrong theorem: instead of finishing all RawCall result cases inline, the stable boundary is likely the full mutual postcondition of the RawCall tail after typed args are extracted.
- Do not chase the holbuild wrapper goal `∃ $var. ¬$var`; inspect nested failed subgoals/logs. That wrapper caused temporary confusion but is not the mathematical goal.
- PLAN decomposition is still acceptable as C0.6 active leaf, but if the next rebuild still leaves complex value/slot-size goals, escalate for helper rather than continuing tactic search.

### What Went Wrong
- The RawCall proof began inline as planned and made progress, but result typing for `raw_call_return_type` dynamic bytes/tuple cases required a local slot-size bound. I copied the `bytes_slot_size_bound` pattern from the helper file into `vyperTypeStmtSoundnessScript.sml` as `raw_call_bytes_slot_size_bound`; the first copy had the wrong tuple-size equality and was fixed to match the proven helper shape.
- I initially tried `drule raw_call_args_runtime_typed_dest`; it failed because HOL could not match antecedents automatically. Switching to `mp_tac raw_call_args_runtime_typed_dest >> impl_tac >- simp[]` worked.
- I tried `drule raw_call_bytes_slot_size_bound`; it failed to match the numeric antecedent in the simplified goal. The current unverified edit switches to `mp_tac raw_call_bytes_slot_size_bound >> impl_tac >- first_assum ACCEPT_TAC`.
- Several holbuild failures reported the top-level wrapper `∃ $var. ¬$var` at `strip_tac`; the real evidence is in the nested failed subgoals in the instrumented log, especially the size/value typing goals.

### Ignored Signals
- The repeated small failures around dynamic bytes/tuple typing are a signal for a boundary lemma, not necessarily a request for more inline simplification.
- The PLAN explicitly says stop if a compact helper is needed. If the next rebuild still leaves nontrivial value typing, do not keep adding brittle `gvs`/`decide_tac` combinations inline.
- The legacy helper file already had a `bytes_slot_size_bound` proof; this should have been checked before attempting to invent/fix the tuple-size arithmetic locally.

### Strategy Adjustments
- Next session should first rebuild from the current source, because the last edit has not been verified.
- If rebuilding reaches the same three value/size goals, either finish them explicitly using the new local `raw_call_bytes_slot_size_bound` or factor a helper. Avoid broad `AllCaseEqs()` over the whole RawCall prefix.
- If a helper is extracted, model it after `raw_log_tail_result_sound_simp`: assumptions should include runtime consistency, typed argument facts, the concrete RawCall tail equation, and conclusion exactly the full mutual postcondition.
- Keep all edits in `semantics/prop`; do not stage untracked `LEARNINGS_type_system_rewrite.legacy.md` or `tmp_helper.txt`; do not commit until `vyperTypeStmtSoundnessTheory` builds cleanly and C0.6 is reviewed.

### Oracle Feedback
- Held: the strategist's linear tail rebase was necessary; after C0.5.5 review, C0.6 is correctly active and C0.7 must wait.
- Held so far: branch-local RawCall decomposition is viable through argument evaluation, typed-argument destructors, delegate/run_ext_call error cases, and state/env/accounts preservation after updates.
- Potential miss: treating RawCallTarget as one Risk-2 Resume may understate the need for a compact RawCall tail-result helper for return-type/value-typing cases. Escalate if the next rebuild confirms this.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6005_t001 - PLAN after tail rebase: C0.6 is beginable/active, C0.7 depends on it
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6006_t001 - begin_component C0.6 injected guidance and authorized edits/builds
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6010_t001 - first RawCall success probe; shows post-eval_exprs RawCall monadic goal
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6026_t001 - inline proof discharged many branches but left RawCall dynamic result size/value goals
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6043_t001 - instrumented log shows top wrapper plus nested three real size/value goals
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6053_t001 - after adding/fixing slot-size helper, same remaining real goals still visible
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6058_t001 - `drule raw_call_bytes_slot_size_bound` failed to match; current unverified source changed this to `mp_tac ...`
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6061_t001 - checkpoint E0331 recorded non-terminal C0.6 progress; active component remains C0.6
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:10701 - local `raw_call_bytes_slot_size_bound` added near RawCall helpers
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:18247 - partial RawCallTarget Resume proof replaces the former `cheat` but is not build-clean
