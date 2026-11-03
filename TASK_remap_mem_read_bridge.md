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

Theorem step_inst_base_error_transfer[local]:
  !fn roots remap inst s1 s2 err.
    alloca_remap_rel fn roots remap s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    step_inst_base inst s1 = Error err ==>
    ?err'. step_inst_base inst s2 = Error err'

Theorem immutable_op_immutables_agree[local]:
  !inst s1 s2 v1 v2.
    is_immutable_op inst.inst_opcode /\
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    s1.vs_immutables = s2.vs_immutables /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) ==>
    v1.vs_immutables = v2.vs_immutables
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

- Repair the observed default-limit no_mem_read_effect_from_no_mem_read_ops failure.
- Build allocaRemapProofsTheory at the default tactic limit without new admissions, validating the retained memory-preservation root as well.
- Preserve all statements, definitions, shared tactics, unrelated proof bodies and completed repairs.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Second owner amendment: replay28072 repaired CALLDATACOPY error transfer and then failed immutable_op_immutables_agree at rpt(CASE_TAC >> simp[]) on ILOAD,2.5seconds. Its complete exact schema and both admitted producers were independently audited PROVABLE at frozen e31296aea; owner verified the whole schema and venom/defs are unchanged since that audit. This amendment adds that fourth exact frozen root and only its observed proof failure/local helpers. No new memory, well-formedness or output-arity premise is allowed. Preserve all pending reader-classification/descriptor obligations; the source-only reader classifier candidate is retained unverified. Obtain updated strategist plan; preceding run is stopped, not complete.

Owner amendment: replay27899 made no source edits and reached step_inst_base_error_transfer[CALLDATACOPY], line4334, error_inline_tac over2.5seconds. The complete exact Error-transfer schema, including all opcodes and malformed envelope/error cases, was already independently audited PROVABLE at the descriptor/BUMP task; its schema and executable definitions remain unchanged. This amendment adds that complete frozen root and only actually demonstrated failing resumes to the authorized repair scope. No extra premise or semantic change. Obtain an updated strategist plan before editing; the prior run is stopped, not complete.

Prior task27613's scoped memory-preservation repair passed replay, but the complete theory then failed its frozen neighbor no_mem_read_effect_from_no_mem_read_ops, gvs classification over101opcode goals,2.5seconds. That task is stopped. Its two local writer helpers and bounded root repair are retained explicitly as partial source without a full-theory certificate.

Both complete exact schemas have now independently been audited PROVABLE against every admitted opcode/arity/effect in current definitions. The read bridge audit includes LOG's actual count/list/reversal producer, malformed descriptors, MEMTOP exclusion and base INVOKE failure; no additional hypothesis or executable change is needed. Existing proof is retained.

## Domain Constraints

- Source edits only within the four frozen roots and necessary local helper theorems in venom/passes/shared/proofs/allocaRemapProofsScript.sml, and only after an actual demonstrated failure. The observed outside-root CALLDATACOPY Error-transfer failure is now explicitly in scope. Repair that actual failing resume, preserving the shared error_inline_tac and unfailed resumes. Do not alter the retained writer helpers/root or read bridge unless actual replay demonstrates a failure.
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
