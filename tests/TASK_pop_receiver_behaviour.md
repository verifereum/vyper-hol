# TASK: Check the source HashMap-pop behaviours

## Meta
Owner sol. Edit and commit only tests/vyperPopReceiverTestScript.sml and this task's state. Other files are parent-owned. Use --oracles codex/gpt-6-astra. The new public generic source fixture and translated source terms are frozen.

## Theorem Statement (FROZEN)
Do not modify either statement. Prove as-is or produce a counterexample.

```sml
Theorem hashmap_pop_returns_old_last_element:
  FST nested_pop_result = INR (ReturnException (IntV 23))

Theorem hashmap_pop_writes_remaining_array:
  FST (read_storage_slot nested_pop_context F
    (THE (compute_hashmap_slot 0w [BaseT (UintT 256)] [ValueSubscript (IntV 7)]))
    (ArrayTV (BaseTV (UintT 256)) (Dynamic 4)) (SND nested_pop_result)) =
  INL (ArrayV (DynArrayV [IntV 11]))
```

## Completion Criteria
Replace both preparation cheats, removing their preserved-proof comments afterwards. Preserve the exact definitions of nested_pop_context and nested_pop_result and the exact source-target theorem. Keep the source fixture and checker input frozen: the test must execute the actual full-checker-accepted frontend output, seed [11,23], return 23 and leave [11]. No hypotheses, new axioms, remaining cheats, alternate evaluator, timeouts or instrumentation changes. Consumed local supporting lemmas and CV registration of the existing definitions, including one generated test-local CV precondition, are allowed; flag them. Do not change any production semantics or unrelated source files. Avoid extra helper definitions unless the existing definitions cannot support the proof; ask the parent before introducing one.

Commit only owned proof/task files; each commit ends with Bot: sol (OpenAI GPT-6.1 Sol).

## Build
`timeout 900 holbuild --max-heap 7000 -j2 build vyperPopReceiverTestTheory`
Default instrumentation, checkpoints and tactic limits only. No --skip-proof-steps, --skip-checkpoints, --no-cache, raised timeout or TRY/ORELSE around search. No full-project build. A cheated preparation build is not proof validation. Leave final external audits and fixture freshness to the parent once the target passes; do not open a duplicate validation frontier at completion.

## Background
Frontend output and the full checker already pass; hashmap_pop_source_target built via REFL_TAC. EVAL_TAC on the return theorem exceeds the default 2.5s. Direct cv_auto_trans nested_pop_result_def fails because eval_stmts contains higher-order list_CASE. Rewriting the result definition with eval_stmts_eq_cont_cps and using cv_auto_trans fails to find an induction for its precondition. The existing CPS/CV execution is available and must be used faithfully, or split the kernel evaluation into bounded steps. No proof work is needed on the interpreter's frame theorem; it has already been repaired and built on this branch.

## Domain Constraints
No changes to public theorem statements, source AST or checked fixture. Do not replace the actual source run with hand-constructed operations. Do not assume storage or account results. No dependency source repairs or scope growth without a reproduced failure and parent authorization.

## Available Resources
- tests/vyperPopReceiverTestScript.sml: fixed context/result and exact target check.
- tests/fixtures/check_contract/nested_pop.vy and .json: fresh generic source.
- semantics/vyperSmallStepScript.sml: eval_stmts_eq_cont_cps, eval_cps_eq, cont_pre_IS_SOME_cont, existing CPS CV translations; call_external_function_pre_def illustrates explicit precondition registration.
- tests/vyperStoragePopTestScript.sml: existing storage CV examples.
- repository AGENTS.md and docs/HOL4_PROOF_CONTROL_LESSONS.md.

## Notes
The parent owns all final audits, PR/review, source generation and manifest work. Do not inspect .holbuild checkpoints/stage internals. Sources, logs and exported theory outputs are allowed. Freeze all existing declarations: only proof text, consumed local lemmas and CV registration may change.

Independent assessment: both corrected statements are PROVABLE. The existing route is cv_auto_trans_pre on the result equation rewritten with eval_stmts_eq_cont_cps, a [cv_pre] proof using cont_pre_IS_SOME_cont and conjunct 2 of eval_cps_eq. Case-split the opaque eval_stmts result pair and its success/exception sum; DoneK, cont_def, nextk_def and one OWHILE_THM prove CPS termination without evaluating the interpreter. See the existing call_external_function_pre proof. The preparation target built in 2.889s with the two temporary cheats; this is parse/checker preparation only.
