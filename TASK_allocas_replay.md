# TASK: Replay the existing non-alloca allocation-map preservation proof

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem step_inst_base_allocas[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    v.vs_allocas = s.vs_allocas
Theorem remap_preserved_no_pointer_ops[local]:
  !fn roots remap inst s1 s2 v1 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (!op v. MEM op inst.inst_operands /\ op = Var v ==>
            v NOTIN pointer_derived_vars fn roots) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the existing step_inst_base_allocas proof without changing its statement.
- Repair the existing remap_preserved_no_pointer_ops proof so full replay continues.
- Build allocaRemapProofsTheory at the default tactic limit.
- Preserve all other existing proofs, definitions and statements.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

A forced default replay at eaf96a2fa timed out at the classification gvs after opcode case splitting, with 101 goals. An independent read-only audit found this exact statement PROVABLE under current GAS-popping semantics and checked all relevant allocation-field producers. The existing proof remains intact.

## Domain Constraints

- Edit only these two proofs and necessary helper theorems in venom/passes/shared/proofs/allocaRemapProofsScript.sml. A needed declarative Ancestors entry is allowed if it introduces no dependency cycle. Preserve the completed allocation-map proof repair.
- All existing definitions and statements, including local declarations, are frozen. No new definitions, axioms, admissions, strengthened premises, opcode exclusions or supported-subset changes.
- Preserve all completed gas, CFG and DRET proofs.
- Default 2.5-second tactic limit; no timeout override and no TRY/ORELSE/FIRST around search.
- Report another prerequisite failure before expanding scope.
- Commit substantive source changes only; no generated TASK/PLAN/DOSSIER records.
- End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- `venom/passes/shared/proofs/allocaRemapProofsScript.sml`
- `venom/props/venomMemPropsScript.sml` (step_inst_base_preserves_allocas)
- `venom/proofs/venomMemProofsScript.sml`
- `venom/defs/venomInstScript.sml`
- `venom/defs/venomExecSemanticsScript.sml`
- `venom/defs/venomStateScript.sml`
- `venom/passes/shared/defs/allocaRemapDefsScript.sml`
- `venom/passes/shared/defs/passResidualFrameScript.sml`
- `venom/passes/shared/defs/pointerConfinedDefsScript.sml`
- `venom/passes/shared/proofs/allocaRemapSSAScript.sml`
- `venom/passes/shared/proofs/passSharedTransferScript.sml`
- `venom/passes/shared/proofs/passSharedFieldScript.sml`

## Notes

This exact statement parsed in the forced failing build. The owner separately checks frozen schemas, forced default/CI replay and dependency tags after return.

The first root now passes incrementally as 24293f5fd, but full replay stopped in the second exact existing root while discharging a GAS-readings agreement premise of the scalar bridge. An independent audit of the complete second statement, its residual frame, GAS step and SSA/pointer producers found PROVABLE under the current definitions. No new invariant or assumption is authorized or needed. This amendment permits only that second proof and necessary helper theorems; all old schemas and completed proofs remain frozen.
