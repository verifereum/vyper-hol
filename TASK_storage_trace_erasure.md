# TASK: Prove evaluator storage-trace prefix and erasure laws

## Meta
- Scope: semantics/prop/vyperStorageTraceScript.sml only.
- Existing source instrumentation has checked builds. Do not change interpreter,
  state, oracle, creation, typing or compiler definitions or theorem statements.
- Owner is concurrently migrating other theories. Leave those files untouched.
- Frozen definition and three frozen theorem statements below. Existing failing
  proofs are intentional starting attempts, not admissions.

## Theorem Statement (FROZEN)
```sml
Definition storage_trace_frame_def:
  storage_trace_frame (f : evaluation_state -> 'a evaluation_result) <=>
    !st observations.
      f (st with storage_trace := observations) =
      case f (st with storage_trace := []) of
        (res,st') =>
          (res,st' with storage_trace := observations ++ st'.storage_trace)

Theorem evaluate_storage_trace_frame:
  (!cx s. storage_trace_frame (eval_stmt cx s)) /\
  (!cx ss. storage_trace_frame (eval_stmts cx ss)) /\
  (!cx it. storage_trace_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. storage_trace_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. storage_trace_frame (eval_expr cx e)) /\
  (!cx es. storage_trace_frame (eval_exprs cx es)) /\
  (!cx t. storage_trace_frame (eval_base_place cx t)) /\
  (!cx t. storage_trace_frame (eval_target_place cx t)) /\
  (!cx t v. storage_trace_frame (assign_tuple_targets cx t v)) /\
  (!cx ts vs. storage_trace_frame (assign_tuple_target_list cx ts vs)) /\
  (!cx es. storage_trace_frame (eval_expr_results cx es))

Theorem storage_trace_frame_prefix:
  storage_trace_frame f /\ f st = (res,st') ==>
  ?observations. st'.storage_trace = st.storage_trace ++ observations

Theorem storage_trace_frame_erasure:
  storage_trace_frame f ==>
  FST (f st) = FST (f (erase_storage_trace st)) /\
  erase_storage_trace (SND (f st)) =
    erase_storage_trace (SND (f (erase_storage_trace st)))
```
Do not modify this statement. Prove it as-is, or produce a counterexample.
This applies to the definition and all three statements in this section.

## Completion Criteria
- Prove all three frozen theorems without cheats, axioms or new assumptions.
- Build vyperStorageTraceTheory using the command below.
- Intermediate helper statements may be designed inside the permitted theory;
  search existing definitions/theorems before adding a helper. Export useful
  shared facts, and avoid duplicated results.
- Commit only the permitted source file and this task file. Never stage other
  owner changes or push. End commits with Bot: sol (OpenAI GPT-6.1 Sol).

## Build
`holbuild -j4 build vyperStorageTraceTheory`
The definition and first full mutual statement parsed in the owner's focused
build; its existing proof fails with the eleven expected obligations. The two
corollary statements have not yet been parsed by a build.

## Background
The evaluator appends physical root, lock, consumed-outcome and adopted-backend
observations to evaluation_state.storage_trace. The log must survive errors and
must never influence runtime results, requests, gas readings or backend effects.
The frozen property states prefix independence for any initial trace, and the
corollaries expose prefix retention and erasure of that initial trace.

## Domain Constraints
- Keep the default 2.5s tactic timeout. No timeout override or bypass, no TRY or
  ORELSE around proof search, no new admission. Never invoke run/repl/Holmake.
- No premise concerning typing, storage layout, keccak, successful execution,
  oracle shape or a restricted program may be added.
- Cover all mutually recursive evaluator forms, including failed calls,
  internal calls, concrete opaque calls, oracle outcomes, creation and gas.
- This proves ghost noninterference/prefix retention, not oracle-off equivalence
  or the final compiler storage correctness theorem.

## Available Resources
- semantics/vyperStateScript.sml: evaluation_state, record_storage_event,
  record_storage_backend, erase_storage_trace, monadic primitives and places.
- semantics/vyperInterpreterScript.sml: evaluate_def/evaluate_ind, gas readings,
  locking, raw/ordinary/send calls and all eleven evaluator functions.
- semantics/vyperCallOutcomeScript.sml: actual take/adopt equations and frames,
  including failed non-message adoption.
- semantics/vyperCreateScript.sml: oracle and concrete creation helpers.
- semantics/prop/vyperCallOutcomeFrameScript.sml: existing generic monadic frame
  kit. Its arbitrary result-trace closure is different from this prefix law;
  do not assume it proves the new property.
- semantics/prop/vyperEvalOutcomeSuffixScript.sml: existing evaluator frame
  organization and mutual-induction consumers, for reference only.

## Notes
The owner will check the final source diff and frozen statements independently.
Do not repair failing out-of-scope ancestors or amend a statement to hide a
failure. Report such a blocker or a counterexample instead.
