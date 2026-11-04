# TASK: Connect memory-safe counted fragment paths to actual runs

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering

## Theorem Statement (FROZEN)
```sml
Theorem gas_path_mem_exec:
  !ctx fn s n r.
    gas_path_mem ctx fn s n r ==>
    gas_path ctx fn s n r /\
    ((?t. r = OK t /\ ~t.vs_halted /\
          !fuel out.
            run_from fuel ctx fn t = out /\ (!e. out <> Error e) ==>
            ?fuel'. run_from fuel' ctx fn s = out /\
                    (mem_safe_run fuel ctx fn t ==>
                     mem_safe_run fuel' ctx fn s)) \/
     (exit_result r /\
      ?fuel. run_from fuel ctx fn s = r /\ mem_safe_run fuel ctx fn s))
```
Do not modify this statement. Prove it as-is, or produce a counterexample.
The gas_path_mem_edge definition and gas_path_mem inductive clauses in lowering/fragGasPathMemScript.sml are also frozen.

## Completion Criteria
- Prove gas_path_mem_exec without admissions, axioms, new premises, or definition changes.
- Build fragGasPathMemTheory with the default 2.5s step limit.
- Consumed local proof helpers are allowed; no unrelated existing theory edits, no new general framework.

## Build
holbuild -j4 build fragGasPathMemTheory

## Background
Lowering needs both exact GAS event counts and the existing memory consumer guarantees. The new path refines gas_path with the actual runner's memory checks, at the SAME fuel as its step and gas count, including INVOKE's callee checks and the existing revert-forward exception. The theorem must erase to gas_path and provide conditional normal continuation safety or an actual safe terminal run. It cannot obtain either by weakening the existing consumer or assuming the program has no memory/calls/GAS.

The exact definitions and whole frozen conclusion were independently audited PROVABLE against current dependencies, including normal/terminal calls, block entry/PHIs, exhausted fuel and revert-forward. No extra well-formedness or label-distinctness assumption is needed: the path carries concrete lookups and actual steps. Preserve every branch of that definition.

## Domain Constraints
Change only lowering/fragGasPathMemScript.sml plus prover task state. Keep all frozen statements/definitions byte for byte. No TRY/ORELSE around search tactics, no timeout overrides, no new cheat/axiom. Put internal consumed helpers in this theory and mark them local. No source-semantic or compiler definition changes.

## Available Resources
- lowering/fragGasPathMemScript.sml
- lowering/fragGasPathScript.sml
- lowering/fragExecMemScript.sml
- lowering/fragExecScript.sml
- venom/compiler/memSafeRunScript.sml
- venom/compiler/unitTransformDefsScript.sml
- venom/proofs/gasCountScript.sml
- venom/proofs/venomExecProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml

## Notes
The owner parse build passed (fragGasPathMemTheory, including its temporary placeholder) at the default step limit. The exact statement and definitions were independently audited PROVABLE. The temporary placeholder in this NEW theorem must be removed completely.

Other unbuilt producer changes in gasSummaryScript.sml and msgGasPostScript.sml are outside this task and do not enter this theory's ancestor graph. Do not edit or validate those siblings.
