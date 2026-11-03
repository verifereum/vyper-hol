# TASK: Bound non-memory-operation memory preservation replay

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem step_inst_base_mem_preserves_no_mem_ops[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    mem_write_ops inst = NONE ==>
    v.vs_memory = s.vs_memory
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the actual default-limit failure in step_inst_base_mem_preserves_no_mem_ops.
- Build allocaRemapProofsTheory at the default tactic limit without new admissions.
- Preserve every statement, definition, shared tactic, unrelated proof and completed remap repair.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Fresh full forced owner27548 at28e330c68 failed in this earlier root at line1334, gvs[is_effect_free_op_def,is_alloca_op_def,is_terminator_def,is_ext_call_op_def,write_effects_def,all_effects_def,empty_effects_def], tactic timeout after2.5seconds. The complete exact schema/all admitted opcodes and operand shapes has been independently checked against current semantics/effects and found PROVABLE without any new hypothesis. Existing proof remains in place.

Prior descriptor, memory-copy and BUMP repairs reached full incremental export under their separate completed tasks. Those tasks are stopped. Do not amend their generated records or infer a fresh forced certificate from incremental replay.

## Domain Constraints

- Edit only step_inst_base_mem_preserves_no_mem_ops and necessary local helper theorems in venom/passes/shared/proofs/allocaRemapProofsScript.sml.
- All statements, definitions, shared ML tactics, other proof bodies and existing remap repairs are frozen.
- No new definition, axiom, admission, premise, opcode exclusion, semantic change, timeout override or TRY/ORELSE/FIRST around proof search.
- Report any new outside-root failure before editing it. No blind unchanged retries or speculative cleanup.
- Commit substantive source only; leave generated task records untracked. End messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/allocaRemapProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml
- venom/defs/venomInstScript.sml
- venom/defs/venomInstProofs3Script.sml

## Notes

Existing theorem has parsed and built previously. Owner performs frozen-schema/scope review plus fresh forced default/CI/public checks after return; those checks are not extra Alan completion gates.
