# TASK: Bound the external-call frame proof step

## Meta
Owner sol. Proof-only repair in the current branch. Edit/commit only semantics/vyperInterpreterScript.sml and this task's state. Other files are parent-owned. Use --oracles codex/gpt-6-astra.

## Theorem Statement (FROZEN)
Do not modify this statement. Prove it as-is, or produce a counterexample.

```sml
Theorem eval_ext_call_preserves_non_accounts:
  eval_ext_call cx static skip_check sig opts vs st = (res, st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
```

## Completion Criteria
Replace the preparation cheat with a checked proof under the default 2.5s tactic limit. The original proof is preserved immediately above the theorem; remove that temporary comment when replaced. Preserve every existing theorem statement and definition. No new axioms, cheats, definitions, stronger hypotheses, timeout changes or TRY/ORELSE around search. Ordinary consumed local lemmas may split the proof; flag them in the result. Do not repair any other theorem without an observed failure and parent scope authorization. The adjacent eval_send_preserves_non_accounts built successfully in the preparation run and is out of scope.

Commit only owned proof files. Each commit ends with: Bot: sol (OpenAI GPT-6.1 Sol).

## Build
`timeout 3600 holbuild --max-heap 7000 -j2 build vyperInterpreterTheory`
Use default instrumentation/checkpoints/tactic limits. No --skip-proof-steps, --skip-checkpoints, --no-cache or raised timeout. A preparation build with a cheat is not proof validation. No full-project build. Parent owns final frontend/checker/interpreter fixture checks and external audits.

## Background
The existing final gvs[AllCaseEqs()] step times out after 2.5s when building the current theorem. The statement is unchanged. Its independent assessment found no missing assumptions. The full preparation target built in 19.239s with only this theorem temporarily cheated; adjacent send and all other retained proofs built.

## Domain Constraints
Preserve the exact two-field conclusion. Oracle failure may change outcomes and requests, so do not assume failure preserves the entire state. Do not change call semantics or source ASTs, add stronger frame hypotheses or introduce an alternate evaluator. Stop on any needed source/statement change or additional out-of-scope failing theorem.

## Available Resources
- semantics/vyperInterpreterScript.sml: eval_ext_call_def, preserved proof and nearby existing frame proofs.
- semantics/vyperCallOutcomeScript.sml: take_call_outcome/adopt_call_outcome.
- semantics/vyperStateScript.sml: read/write/update/log state operations.
- docs/HOL4_PROOF_CONTROL_LESSONS.md and repository AGENTS.md.

## Notes
The parent has checked load/disk and the frozen statement independently. Do not inspect .holbuild checkpoints/stage internals. Dependency sources, logs and exported outputs are allowed. Once the exact target has built and its proof is accepted, leave external validation to the parent; avoid a duplicate final-validation frontier that the harness cannot schedule.
