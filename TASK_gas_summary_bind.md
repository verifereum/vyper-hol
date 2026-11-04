# TASK: Compose strict GAS summaries through source monadic sequencing

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem gas_summary_bind:
  gas_summary (ctx, func) source (es, s0)
    (\res es_mid t.
       ?v. res = INL v /\
           gas_summary (ctx, func) (next v) (es_mid, t) Q R)
    (\res es_end r. ?exc. res = INR exc /\ R (INR exc) es_end r) ==>
  gas_summary (ctx, func) (bind source next) (es, s0) Q R
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All existing definitions are frozen.

## Completion Criteria

- Prove the single frozen theorem without admissions.
- Build gasSummaryComposeTheory at the default tactic limit.
- Keep source evaluation, actual path and postconditions unconditional in the strict summary.

## Build

```sh
holbuild -j2 build gasSummaryComposeTheory
```

## Background

This composition rule serves the existing lowering migration's sequential source operands, expression lists and call arguments. The strict core chooses source result/non-gas final state before every arbitrary unused source suffix. All target reads count; only explicit source events are selected. The rule preserves exact actual target paths, including exhausted reads, and short-circuits a source exception when the first target path exits.

## Domain Constraints

- Edit only lowering/gasSummaryComposeScript.sml. Additional helper theorems there are allowed; no new definitions.
- Preserve the frozen theorem and all existing statements/definitions, executable/source semantics, shared lowering judgments and stage contracts.
- No new admissions, axioms, oracle theorems, timeout overrides or TRY/ORELSE/FIRST search wrappers.
- Do not infer an actual path from continuation compatibility or consumption from list-length differences.
- Existing ancestor admissions are dependencies only, not a way to assume this new composition conclusion.
- Do not alter the strict core to guard obligations under an existential source outcome.

## Available Resources

- `lowering/gasSummaryComposeScript.sml`
- `lowering/gasSummaryScript.sml`
- `lowering/fragGasPathScript.sml`
- `venom/proofs/gasCountScript.sml`
- `venom/proofs/gasOracleReplayScript.sml`
- `semantics/vyperStateScript.sml`
- `semantics/vyperInterpreterScript.sml`

## Notes

The parser/prerequisite build passed gasSummaryComposeTheory (169.974s), saving the one exact preparation placeholder. Independent read-only audit found the exact schema PROVABLE, including source tail quantifiers, actual DROP suffix, zero padding and first-exit propagation. Forced default/CI replay and kernel-tag audit are owner checks after return.
