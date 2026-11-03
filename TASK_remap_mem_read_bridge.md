# TASK: Bound observed memory-read descriptor bridge replay

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

Theorem no_mem_read_effect_from_no_mem_read_ops[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    mem_read_ops inst = NONE /\
    inst.inst_opcode <> MEMTOP /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    Eff_MEMORY NOTIN read_effects inst.inst_opcode
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

- Repair the observed default-limit no_mem_read_effect_from_no_mem_read_ops failure.
- Build allocaRemapProofsTheory at the default tactic limit without new admissions, validating the retained memory-preservation root as well.
- Preserve all statements, definitions, shared tactics, unrelated proof bodies and completed repairs.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Prior task27613's scoped memory-preservation repair passed replay, but the complete theory then failed its frozen neighbor no_mem_read_effect_from_no_mem_read_ops, gvs classification over101opcode goals,2.5seconds. That task is stopped. Its two local writer helpers and bounded root repair are retained explicitly as partial source without a full-theory certificate.

Both complete exact schemas have now independently been audited PROVABLE against every admitted opcode/arity/effect in current definitions. The read bridge audit includes LOG's actual count/list/reversal producer, malformed descriptors, MEMTOP exclusion and base INVOKE failure; no additional hypothesis or executable change is needed. Existing proof is retained.

## Domain Constraints

- Source edits only within the two frozen roots and necessary local helper theorems in venom/passes/shared/proofs/allocaRemapProofsScript.sml, and only after an actual demonstrated failure. Start at the read bridge; do not alter the retained writer helpers or root unless a new actual replay failure requires it.
- All statements, definitions, shared tactics, other proof bodies and completed remap repairs are frozen.
- No new definition, axiom, admission, premise, opcode exclusion, semantic change, timeout override or TRY/ORELSE/FIRST around proof search.
- Report any new outside-root failure before editing. No blind unchanged retries or speculative cleanup. Do not amend generated records from the prior task.
- Commit substantive source only; leave generated task records untracked. End messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/allocaRemapProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml
- venom/defs/venomInstScript.sml
- venom/proofs/venomInstProofs3Script.sml

## Notes

Statements have parsed and built previously. Owner handles full schema/scope audits and fresh forced default/CI/public checks after return; those are not extra Alan completion gates.
