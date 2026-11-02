# TASK: Count actual GAS execution and compose genuine fragment paths

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-02
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem gas_count_suffix:
  (!fuel ctx inst s.
     gas_count_suffix (gas_count_step fuel ctx inst s) s
       (step_inst fuel ctx inst s)) /\
  (!fuel ctx bb s.
     gas_count_suffix (gas_count_block fuel ctx bb s) s
       (exec_block fuel ctx bb s)) /\
  (!fuel ctx fn s.
     gas_count_suffix (gas_count_blocks fuel ctx fn s) s
       (run_blocks fuel ctx fn s))

Theorem gas_count_fuel_mono:
  (!n m ctx inst s r.
     step_inst n ctx inst s = r /\ (!e. r <> Error e) /\ n <= m ==>
     gas_count_step n ctx inst s = gas_count_step m ctx inst s) /\
  (!n m ctx bb s r.
     exec_block n ctx bb s = r /\ (!e. r <> Error e) /\ n <= m ==>
     gas_count_block n ctx bb s = gas_count_block m ctx bb s) /\
  (!n m ctx fn s r.
     run_blocks n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
     gas_count_blocks n ctx fn s = gas_count_blocks m ctx fn s)

Theorem gas_path_suffix:
  gas_path ctx fn s n r ==> gas_count_suffix n s r

Theorem gas_path_normal:
  gas_path ctx fn s n (OK t) ==>
  ~t.vs_halted /\
  !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r

Theorem gas_path_exit:
  gas_path ctx fn s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r

Theorem gas_path_then:
  gas_path ctx fn s n (OK t) /\ gas_path ctx fn t m r ==>
  gas_path ctx fn s (n + m) r
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

The new definitions in `gasCountScript.sml` and `fragGasPathScript.sml` are frozen too. They count every actual GAS, including exhausted zero reads and callee reads; they do not infer counts from list-length differences or continuation simulation.

## Completion Criteria

- Prove all six frozen statements, removing their new placeholders.
- Build both new theories with the default tactic limit.
- Preserve the actual execution equations, existing gas replay theorem and all shared lowering judgments. This task is additive infrastructure for the approved full lowering migration, not a completed msg.gas simulation.
- Report every new helper definition or restatement. If a frozen statement is false, give a concrete counterexample without adding a premise.

## Build

`holbuild -j2 build gasCountTheory fragGasPathTheory`

## Background

The existing fragment judgment only relates continuations. It does not establish that an endpoint is reached by an actual finite path, so it cannot supply a sound gas-consumption witness. The approved lowering contract needs actual prefixes and exact target suffixes for normal, return, break, continue and terminal outcomes. Every target GAS counts; only source explicit-msg.gas events are selected by the later construct proofs. Source semantics stays unchanged.

The new counters follow the existing runner's actual result branches. The path uses real instruction executions and parallel-PHI block entry. INVOKE remains available, with the counter including its actual callee run. Padded prefix values use the existing `gas_prefix`; the counter counts GAS even after the initial oracle is empty.

## Domain Constraints

- Scope substantive edits to the two new theories. Existing semantic/compiler/judgment definitions are frozen. No stage/source/top-level premise or executable change is authorized.
- No new admission, axiom, no-GAS restriction, static count shortcut, opcode-absent proof or replacement of actual execution by `frag_exec`.
- All six task placeholders must be removed. Pre-existing admitted ancestors outside scope may remain dependencies; do not expand the task to remove them or misreport them as clean.
- Default2.5s per tactic, no timeout override and no TRY/ORELSE/FIRST around proof search.
- No let-bindings in new theorem statements. Reuse existing semantic and replay helpers before adding duplicate opcode lemmas.
- Commit only substantive source edits, leaving Alan working files untracked. End each commit message with `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- `venom/proofs/gasCountScript.sml`
- `lowering/fragGasPathScript.sml`
- `venom/proofs/gasOracleReplayScript.sml`
- `venom/defs/venomExecSemanticsScript.sml`
- `venom/proofs/venomExecProofsScript.sml`
- `venom/compiler/memSafeRunScript.sml`
- `lowering/fragExecScript.sml`
- `lowering/abiEncoderObserverScript.sml`
- `venom/defs/venomStateScript.sml`
- `venom/defs/stateEquivScript.sml`

## Notes

An independent read-only audit classified the exact counter definitions and all six statement schemas PROVABLE. The owner will verify frozen statements and force default/CI replay after return. The prerequisite parse outcome is recorded before launch. This task does not migrate `expr_sim`, `stmt_frag`, source gas lists, or the top-level call theorem.
