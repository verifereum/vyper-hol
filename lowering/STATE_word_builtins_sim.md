# STATE_word_builtins_sim
Updated: 2026-10-25

## Cursor
- component: C1.7
- status: in_progress
- active_file: lowering/exprSimWordBuiltinsScript.sml
- next_action: Inspect git status/diff: all eight frozen proofs now implemented and both targets clean (E0016). Reverify targets, close C1.7 proved and request oracle review, then commit stable source changes. Proceed to scheduled C1.8 final dependency audit; no more arithmetic/integration proof work needed.
- expected_goal_shape: No failing theorem. All eight proofs are one-line applications of word_builtin_below_sim or word_modular_names_sim. Pending inherited-cheat audit and stable commit.
- verify_with: holbuild(targets=["exprSimBuiltinsTheory","exprSimMainTheory"], timeout=900)

## If This Fails
- Inspect actual failure before edits. For inherited dependency mismatch, query C1.8 guidance; if genuinely new proof blocker, checkpoint evidence or close C1.7 stuck and request review. Do not alter frozen statements.

## Do Not Retry
- Using is_uint_type to infer uint width <=256: Predicate only identifies UintT shape; successful evaluate_type gives the required bound.
  - evidence: tool_output:TO_word_builtins_sim-20261025T190154Z_m0702_t001
  - evidence: tool_output:TO_word_builtins_sim-20261025T190154Z_m0714_t001

## Reflection
### Tunnel Vision Check
- The typed consumer abstraction solved the repetition problem; do not further optimize arithmetic or redesign composition now.
- Fresh expert should first audit inherited cheated dependencies, not reprove the eight now-checked statements. Allowed exceptions remain lower_value_word_shape/compile_binop_shape.
- Outside-box audit route: generated Theory.txt indexes are absent here; readable .holbuild/obj/lowering/*Theory.dat encode oracle tags and dependencies. Could use a checked ML diagnostic if needed rather than search unavailable indexes.

### What Went Wrong
- Initial tactical failures mostly came from rpt strip_tac splitting disjunctions/conclusions followed by >- operating globally. Parenthesizing complete per-branch continuations fixed the modular and stack helpers.
- Quoted variables eliminated by gvs (especially args/bt in names adapter) became fresh unintended variables. Preserve list-level interfaces until after deriving EVERY facts.
- is_uint_type alone does not constrain width. Obtain k<=256 from successful evaluate_type in typed value LIST_REL before uint_value_word_rep.
- Inherited cheat tags appear in Theory.dat as expected; their precise permitted route still needs final audit.

### Ignored Signals
- Avoid repeated tactic variations when a general typed consumer removes shared plumbing; strategist augmentation validated exactly that abstraction.
- simp may normalize the goal using ann equality without rewriting the source precondition; gvs at final matching resolves both.

### Strategy Adjustments
- typed_builtin_args_values and compile_typed_word_builtin_sim now encapsulate all readiness/invariant/evaluator plumbing.
- word_name_sim_ok uses well_typed_Name_lookup, word_value_type_typed and compile_name_word_sim, never compile_name_sim.
- Use EVERY word_value_type (MAP expr_type args) to retain argument-list abstraction across modular name typing inversion.

### Oracle Feedback
- Augmented C1.7 typed consumer proposal held exactly: four short typed integrations and shared public adapters finished all eight frozen proofs.
- No new falsehood evidence or definition redesign required. Remaining work is audit/review/commit, not proof search.

## Evidence Pointers
- episode:E0016 - all integrations and frozen proofs built; final audit pending
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0772_t001 - exprSimBuiltinsTheory and exprSimMainTheory clean
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0785_t001 - exact frozen statements preserved; only ancestor and eight bodies changed
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0773_t001 - no cheat/TRY/ORELSE/hh in helper source
- tool_output:TO_word_builtins_sim-20261025T190154Z_m0781_t001 - Theory.dat inherited cheat tags; audit precise route
- source:lowering/exprSimWordBuiltinsScript.sml - helper adapters now complete
- source:lowering/exprSimBuiltinsScript.sml - all eight task proofs complete
