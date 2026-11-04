# TASK: Prove the source/target GAS summary adapters

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem gas_explicit_append:
  gas_explicit (left ++ right) gs =
    gas_explicit left gs ++ gas_explicit right (DROP (LENGTH left) gs)

Theorem gas_summary_conseq:
  gas_summary (ctx, func) source (es, s0) Q R /\
  (!res es_end t. Q res es_end t ==> Q' res es_end t) /\
  (!res es_end r. R res es_end r ==> R' res es_end r) ==>
  gas_summary (ctx, func) source (es, s0) Q' R'

Theorem gas_summary_no_source_read:
  (!tail. source (es with gas_obs := tail) =
            (res, es_end with gas_obs := tail)) /\
  gas_path ctx func s0 n r /\
  ((?t. r = OK t /\ Q res (es_end with gas_obs := []) t) \/
   (exit_result r /\ R res (es_end with gas_obs := []) r)) ==>
  gas_summary (ctx, func) source (es, s0) Q R

Theorem gas_summary_next_read:
  gas_path ctx func s0 1 (OK t) /\
  gas_prefix 1 s0.vs_gas_readings = [w] /\
  Q (INL (IntV (&w2n w))) (es with gas_obs := []) t ==>
  gas_summary (ctx, func) next_gas_reading (es, s0) Q R
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
The two prepared definitions `gas_explicit_def` and `gas_summary_def` are frozen too.

## Completion Criteria

- Remove all four task placeholders and build `gasSummaryTheory` at the default tactic limit.
- Preserve every existing source, compiler, stage and lowering judgment definition. This task proves additive adapters; it does not migrate the shared expression/body contracts or complete `compile_msg_gas_sim`.
- Report any new helper definition or exported restatement. Keep substantive changes confined to `lowering/gasSummaryScript.sml`.

## Build

`holbuild -j2 build gasSummaryTheory`

## Background

Every target GAS consumes a reading, including compiler-generated call/precompile reads and reads after exhaustion. Only explicit source msg.gas consumes a source reading. The consuming expression/value/statement judgments need one shared summary of the corresponding source and target executions, with their concrete entry preconditions checked before choosing source readings.

The summary fixes the marks, source result and source final non-gas state before every arbitrary unused source suffix. `gas_explicit` selects T-marked values from the existing zero-padded target prefix. Actual target paths use the checked `gas_path` relation, whose count fixes all target suffixes through `gas_count_suffix`. The source witness, target path and outcome post are unconditional: an existentially chosen source result cannot disable correctness. This adapter adds no assumption to any existing theorem. Its canonical source post-state contains no unused gas suffix.

The no-source-read adapter is for generated reads: a source computation can update other fields without consuming gas. The explicit-read adapter is for the msg.gas leaf. Concrete call, precompile and leaf proofs must still establish their actual paths and value/memory posts. Neither adapter assumes a static equality of the initial source/target reading lists.

## Domain Constraints

- Existing source semantics, Venom/assembly execution, gas replay/count/path definitions, and all shared expression/value/statement/memory/stage definitions are frozen.
- This strict core does not implement the existing exempt-result boundary. The later wrapper migration must preserve that boundary separately and certify construct-local marking/branch correspondence; do not add an outcome guard to this summary or weaken Q/R to make a proof pass.
- No new admission, axiom, unsupported subset, no-GAS restriction, stage premise, source premise or top-level change.
- Do not replace actual paths by continuation compatibility or infer counts from oracle lengths. Exhausted target reads and callee reads remain covered by the checked path/count interfaces.
- Do not move concrete state/frame/frontier/history preconditions inside an existential in a downstream consumer. This task changes no downstream consumer.
- Default2.5s tactics; no timeout override and no TRY/ORELSE/FIRST around proof search. No let-bindings in new theorem statements.
- Reuse the existing prefix/path interfaces. Do not implement a second oracle or source-consumption design.
- Leave Alan working files untracked. Commit only substantive source changes with trailer `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- `lowering/gasSummaryScript.sml`
- `lowering/fragGasPathScript.sml`
- `venom/proofs/gasCountScript.sml`
- `venom/proofs/gasOracleReplayScript.sml`
- `semantics/vyperInterpreterScript.sml`
- `semantics/vyperStateScript.sml`
- `lowering/exprSimScript.sml`
- `lowering/stmtSimScript.sml`
- `lowering/fragExecScript.sml`
- `venom/defs/venomStateScript.sml`

## Notes

The first independent audit found an existential-outcome loophole in the initial guarded draft. That draft was never consumed or handed to Alan, and its pending parser job17150 was intentionally canceled. The strict replacement removes the guard entirely. Independent re-audit found all four exact schemas PROVABLE, verified every resource and TASK/source statement equality, and confirmed that every witness now requires an actual path and Q/R. The internal contract ruling approves this unconditional core and keeps exemptions at later outer construct boundaries. Parser job17176 completed with exit0, saving exactly the four expected task placeholders and both definitions, with no parser warnings. These are prepared statements, not proofs. Checked prerequisite8ca162e1b passed owner forced default and CI replay of `gasCountTheory`/`fragGasPathTheory` and clean kernel tag checks. Existing shared judgments remain unchanged; wrapper/exemption, RetQ tail-invariance and actual-prefix memory-safety obligations remain outside this additive task.
