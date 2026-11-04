# TASK: Bound observed memory-descriptor and BUMP error replay

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem mem_ops_ofst_is_operand[local]:
  !inst ops.
    (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) ==>
    MEM ops.iao_ofst inst.inst_operands

Theorem step_inst_base_error_transfer[local]:
  !fn roots remap inst s1 s2 err.
    alloca_remap_rel fn roots remap s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    step_inst_base inst s1 = Error err ==>
    ?err'. step_inst_base inst s2 = Error err'
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

- Repair the actual default-limit failures in mem_ops_ofst_is_operand and step_inst_base_error_transfer[BUMP], preserving every schema.
- Build allocaRemapProofsTheory at the default tactic limit with no new admissions.
- Preserve every definition, shared tactic, unrelated proof body and all completed remap repairs.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Fresh full forced owner replay26780 at ac40973b8 stopped at mem_ops_ofst_is_operand line1273, simp[mem_write_ops_def,mem_read_ops_def,AllCaseEqs()] over2.5seconds. An earlier actual replay26198 at11:16:47 also recorded step_inst_base_error_transfer[BUMP] error_inline_tac over2.5seconds; that unresolved budget failure was not edited by the prior task. Both complete exact schemas have now been independently checked against their current definitions and found PROVABLE, including every descriptor opcode/arity/LOG reverse and every admitted Error-transfer opcode and malformed envelope. BUMP's actual producer evaluates both input values before its intentionally aliased output update, and needs no new hypothesis. Existing proofs are retained.

The MCOPY task completed ac40973b8 and the fields/errors task completed74c3b706f/1d006c6f7; none is running now. Use this isolated task and do not amend or reuse their generated PLAN/STATE.

## Domain Constraints

- Edit only mem_ops_ofst_is_operand and the actually failing step_inst_base_error_transfer[BUMP] resume, plus necessary local helpers in venom/passes/shared/proofs/allocaRemapProofsScript.sml.
- The full Error-transfer schema is frozen, and its prelude and all other completed resumes (including LOG) remain unchanged.
- All existing definitions, statements, shared tactics and unrelated proof bodies are frozen, including completed MCOPY/immutable/pure2/memory/pointer repairs.
- No new definition, axiom, admission, premise, opcode exclusion, semantic change, timeout override, or TRY/ORELSE/FIRST around search.
- Report any newly failing outside-scope root or resume before editing it; no speculative cleanup or blind unchanged retries.
- Commit substantive source only; leave generated task records untracked. End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/allocaRemapProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml
- venom/defs/venomInstScript.sml

## Notes

Existing statements have parsed and built previously, but fresh replay exposes performance bugs. Owner checks all frozen schemas and independently performs forced default/CI replay and public dependency checks after return; those owner-only checks are not extra Alan completion gates.
