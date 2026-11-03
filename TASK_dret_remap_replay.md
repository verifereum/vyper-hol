# TASK: Repair the existing DRET remapping witness proof at the default step limit

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem dret_remap_output:
  !remap. FLOOKUP remap 0 = SOME 64 ==>
  ~lift_result (alloca_remap_rel dret_fn {} remap)
    (alloca_remap_rel dret_fn {} remap)
    (alloca_remap_rel dret_fn {} remap)
    (case step_inst_base dret_inst dret_s1 of
       OK s => if s.vs_halted then Halt s else OK s
     | Halt s => Halt s | Abort a s => Abort a s
     | IntRet vs s => IntRet vs s | Error e => Error e)
    (case step_inst_base dret_inst dret_s2 of
       OK s => if s.vs_halted then Halt s else OK s
     | Halt s => Halt s | Abort a s => Abort a s
     | IntRet vs s => IntRet vs s | Error e => Error e)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All existing definitions and other theorem statements are frozen too.

## Completion Criteria

- Repair the existing proof without admissions.
- Build allocaRemapRegressionTheory with the default tactic limit.
- Preserve the existing concrete counterexample coverage and proof conclusions.

## Build

```sh
holbuild -j2 build allocaRemapRegressionTheory
```

## Background

Forced replay encountered a 2.5-second timeout in the theorem's broad initial simplification at line509. The concrete DRET witness and its statement are unchanged; only an earlier unrelated GAS proof gained an exec_gas rewrite. The current complete proof must be preserved and repaired, not replaced with a placeholder. This prerequisite is retained evidence of an encountered remapping bug.

## Domain Constraints

- Scope edits to proof bodies and necessary helper theorems in venom/passes/shared/proofs/allocaRemapRegressionScript.sml.
- Preserve every existing statement and definition; no executable or source-semantic edits, new definitions, premises, admissions or axioms.
- No timeout overrides, TRY/ORELSE/FIRST search wrappers, or weakening of witness coverage. Remove such wrappers if repairing a proof containing one; do not perform broad unrelated cleanup.
- Do not replace existing proofs with cheats. Report other prerequisite failures rather than expanding scope.
- Additional helper theorems may be added only where needed for this frozen root or a directly blocking proof in the same file.

## Available Resources

- `venom/passes/shared/proofs/allocaRemapRegressionScript.sml`
- `venom/passes/shared/defs/allocaRemapDefsScript.sml`
- `venom/passes/shared/defs/pointerConfinedDefsScript.sml`
- `venom/defs/venomExecSemanticsScript.sml`
- `venom/defs/venomStateScript.sml`
- `venom/defs/venomLayoutScript.sml`
- `venom/defs/dretShapeDefsScript.sml`
- `venom/defs/stateEquivScript.sml`

## Notes

The theory was reached by forced replay; the existing theorem parsed and was previously buildable. An independent read-only exact-statement audit found the theorem PROVABLE under only its current FLOOKUP premise: both DRET executions return the same descriptor, but the copied byte at32 differs from the untouched remapped byte at64 required by alloca_mem_agrees. All resource files were inspected and exist. Owner forced default/CI checks follow the returned proof.
