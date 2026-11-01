# TASK: Repair getter machine typing after gas-observation integration

## Meta
Status: planned
Priority: P1
Created: 2026-11-01
Location: semantics/prop/vyperTypeExternalCallMachineScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem call_external_function_selected_getter_success_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\ machine_supply am orc /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  evaluate_defaults cx am gobs
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) =
    SOME (dflt_vs, gobs') /\
  bind_arguments (type_env_all_modules mods) args (vals ++ dflt_vs) = SOME scope /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_well_typed am'
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All other existing theorem statements and executable definitions are frozen too.

## Completion Criteria

1. Restore this proof without admissions and build vyperTypeExternalCallMachineTheory.
2. No new admissions, axioms, assumptions, executable definitions, timeout increases, or TRY/ORELSE around proof search.
3. Keep existing history and substantive theorem coverage. Do not push, rebase, reset, squash, merge, or edit other files except consumed local proof helpers in this same script.
4. Remove the temporary placeholder and obsolete commented original after proving it.
5. Commit only the proof script and this TASK file. Never commit .alan/, PLAN_, STATE_, LEARNINGS_, LOG_, DOSSIER_, blobs, tool outputs, or other scaffolding. Every commit ends with exact trailer: Bot: sol (OpenAI GPT-6.1 Sol)

## Build

```sh
holbuild --max-heap 8000 -j2 build --skip-checkpoints --skip-proof-steps vyperTypeExternalCallMachineTheory
```

Development may use standard checkpoints; final check replays without checkpoints. Keep default tactic timeout when proof-step instrumentation is enabled.

## Background

Main added threaded gas observations to callable entry/default evaluation. This integration preserves an existing supply-domain/Halt treatment and shared pending-deletion API. The theorem parsed and all preceding proofs built; its post-merge proof fails at the component subgoal. An independent audit found the frozen claim PROVABLE from the actual interpreter and existing component results.

## Domain Constraints

No new source-supply premise or oracle assumptions. No changes to executable semantics. Existing inherited admissions outside this task are allowed dependencies; introduce none. Never weaken the desired claim or delete theorem coverage. Do not touch oracle-storage interfaces.

## Available Resources

- semantics/prop/vyperTypeExternalCallMachineScript.sml (target and preceding component lemmas)
- semantics/prop/vyperTypeContractSoundnessScript.sml (getter body execution)
- semantics/prop/vyperTypeInitialStateScript.sml (entry typing)
- semantics/prop/vyperTypeEntryReadinessScript.sml (default readiness)
- semantics/vyperInterpreterScript.sml (call_external_function/evaluate_defaults)
- semantics/prop/supply/source/vyperSourceSupplyFieldsScript.sml (machine/source supply)
- .holbuild/logs/current/vyper-hol/vyperTypeExternalCallMachineTheory/build.log

## Notes

This is a migration repair, not a new interface. Preserve all existing public statements and use the supplied script as source of truth.
