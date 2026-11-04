# TASK: Bound existing MCOPY remap preservation replay

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem mcopy_preserves_remap[local]:
  !fn roots remap inst s1 s2 v1 bb v.
    alloca_remap_rel fn roots remap s1 s2 /\
    allocas_in_memory s1 /\ allocas_in_memory s2 /\
    FINITE roots /\ roots SUBSET alloca_roots fn /\
    wf_function fn /\ ssa_form fn /\
    pointer_confined fn roots /\ all_mem_via_pointer fn roots /\
    alloca_safe_access fn roots s1 /\ alloca_safe_access fn roots s2 /\

    step_inst_base inst s1 = OK v1 /\
    inst.inst_opcode = MCOPY /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    v IN pointer_derived_vars fn roots /\
    (?ops. (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
           ops.iao_ofst = Var v) /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair actual default-limit proof failures in this existing root and its resumes, preserving every conclusion and assumption.
- Build allocaRemapProofsTheory at the default tactic limit with no new admissions.
- Preserve every existing definition, statement, shared tactic, unrelated proof and completed MEMTOP/SHA3/LOG/pointer/immutable/memory repair.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Fresh forced owner replay at 4be5ef199 stopped in mcopy_preserves_remap[rd] at broad instruction-dispatch expansion (line3290). An independent whole-schema/all-resume/all-producer audit found PROVABLE including zero size, overlapping source/destination, equal runtime addresses, arbitrary outputs, materialized safe bounds, both pointer-derived Var addresses and size nonaliasing. No new premise or semantic change is needed. The existing proof is retained.

The prior completed TASK_pointer_bounds_replay was extended with this root, but its completed PLAN cannot augment: HARNESS_GATE_DEADLOCK refused every legal planning action before any source edit. This fresh task isolates only the newly exposed MCOPY root; do not reuse or edit that other task's generated PLAN/STATE. There is no other live proof run in this worktree.

## Domain Constraints

- Edit only mcopy_preserves_remap and its actual failing resumes, plus necessary local helpers in venom/passes/shared/proofs/allocaRemapProofsScript.sml.
- All existing definitions, theorem statements, shared tactics, unrelated proof bodies and completed repairs are frozen.
- No new definition, axiom, admission, assumption, opcode exclusion or executable/source semantic change.
- Default2.5-second step limit; no timeout override or TRY/ORELSE/FIRST around search.
- Report a new failing root outside this theorem before editing it. No speculative cleanup or blind unchanged retries.
- Commit substantive source only; leave generated task records untracked. End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/allocaRemapProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml
- venom/defs/venomStateScript.sml
- venom/defs/venomInstScript.sml
- venom/passes/shared/proofs/passSharedSubstScript.sml

## Notes

The exact statement has parsed and prior owner checks built this theory, but current forced replay exposed the budget bug. Owner checks complete frozen schemas and independently performs forced default/CI replay and public dependency checks after return; these owner-only checks are not your completion gate.
