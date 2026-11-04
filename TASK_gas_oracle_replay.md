# TASK: Prove finite-run GAS oracle replay

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/proofs/gasOracleReplayScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem gas_oracle_replay:
  (!fuel ctx inst s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (step_inst fuel ctx inst s)
         (step_inst fuel ctx inst
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail))) /\
  (!fuel ctx bb s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (exec_block fuel ctx bb s)
         (exec_block fuel ctx bb
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail))) /\
  (!fuel ctx func s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (run_blocks fuel ctx func s)
         (run_blocks fuel ctx func
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail)))
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

`holbuild -j2 build gasOracleReplayTheory` succeeds with no CHEAT warnings in the target theory. Preserve the frozen statement, use existing infrastructure where possible, and add no admissions or axioms. A false claim requires a checked counterexample, not a silent restatement.

## Build

```sh
holbuild -j2 build gasOracleReplayTheory
```

## Background

Venom GAS pops an ordered oracle, including inside INVOKE callees. Passes that reorder or drop reads need to construct an input oracle from the output execution. This replay property allows those constructions to compose while retaining an arbitrary unused suffix. The empty oracle reads zero, matching assembly.

## Domain Constraints

- No edits to semantics, existing theorem statements, holproject.toml, or existing proofs. Add proof helpers only as needed for this theorem.
- Default 2.5s tactic timeout. No timeout overrides; no TRY/ORELSE around search tactics.
- Build through holbuild only; no interactive g/e sessions.
- No no-GAS or supported-subset premise. Include malformed instructions and nested calls.
- Keep proof machinery in venom/proofs/gasOracleReplayScript.sml or narrowly named helper theories in venom/proofs/. Do not change shared state relations or pass contracts.

## Available Resources

- venom/defs/venomExecSemanticsScript.sml: exec_gas, run_defs, setup_callee, merge_callee_state, eval_phis, bind_outputs and run_block.
- venom/defs/venomStateScript.sml: state updates and gas-reading projections.
- venom/defs/stateEquivScript.sml: lift_result and state relations.
- venom/proofs/oracleExecPropsScript.sml: targeted opcode dispatch and gas-preservation lemmas.
- venom/proofs/oracleStatePropsScript.sml: oracle-field transport.
- venom/proofs/venomExecProofsScript.sml and venom/proofs/venomInstProofsScript.sml: execution helpers.
- venom/simulation/proofs/: mutual-run and frame transport examples.

## Notes

An independent checker inspected GAS, every step_inst_base branch, call/precompile extraction, setup/merge, PHIs and mutual recursion and returned PROVABLE for this exact strengthened actual-prefix and final-suffix statement with no extra premise. That was a definition audit, not a proof build. Parent will perform forced replay and review afterward. The placeholder parse build's result must be read before claiming the statement parsed.
