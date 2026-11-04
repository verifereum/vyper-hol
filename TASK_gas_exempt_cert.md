# TASK: Certify source errors and focused target prefixes

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem gas_exempt_cert_execution:
  !memory tops ctx func source es s0 marks err ee leaf finish.
    gas_exempt_cert memory tops (ctx, func) source (es, s0)
      marks (err, ee) (leaf, finish) ==>
    (!tail. source
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INR (Error err), ee with gas_obs := tail)) /\
    gas_focus_path (ctx, func) s0 (LENGTH marks) (leaf, finish) /\
    unspecified_behaviour_exempt tops err
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
The definitions of gas_exempt_cert, gas_exempt_origin, gas_value_prefix,
gas_focus_path, gas_invoke_entry, gas_marked_exec, gas_summary and
gas_summary_at are also frozen. Preserve their exact mathematical clauses.

Validate any shared helper machinery before starting the root proof. Put
reusable helpers next to their definitions, without duplicating existing ones.

## Completion Criteria
1. The named theory builds at the default step limit with no new admissions.
2. Remove the root theorem's new placeholder. Add no axiom, cheat, restriction,
   strengthened premise, or executable semantics change.
3. Search existing theorems before adding helpers; export reusable helpers beside
   their definitions. Preserve all other statements and existing proofs.
4. No TRY/ORELSE around search; no timeout or project configuration change.

## Build
```sh
holbuild -j4 build gasExemptCertTheory
```
Use proof steps, cache and checkpoints. Do not use run or repl.

## Background
A source exemption may arise inside an unfinished internal call. This product
certifies the actual source error, its unchanged exemption gate, and an actual
target focus prefix without claiming completion of that INVOKE. It is a consumed
transport product below the shared lowering judgments, not the whole migration.

## Domain Constraints
Source semantics, compiler behavior and existing strict summary definitions
stay unchanged. Keep all 18 certificate constructors and the full concrete
origin child's post/cursor/history evidence. Preserve the supplied event marks.

## Available Resources
- lowering/gasExemptCertScript.sml: exact relation and root
- lowering/gasExemptOriginScript.sml: concrete origin execution/classification
- lowering/gasNormalPrefixScript.sml: full normal child witness
- lowering/typeBuiltinSourceScript.sml: singleton raw source failure
- lowering/gasSummaryScript.sml: fixed marked executions
- lowering/gasSummaryComposeScript.sml: existing source/target composition
- lowering/fragGasFocusScript.sml: actual invoke entry and focus suffix
- lowering/fragGasPathMemScript.sml: completed safe target segments
- semantics/vyperStateScript.sml: actual source monad
- semantics/vyperInterpreterScript.sml: actual source evaluator

## Notes
Definitions built without admissions. Independent exact declaration audit:
PROVABLE. The root parse build passed with its one expected new placeholder.
Do not modify this task file or its frozen statement.

