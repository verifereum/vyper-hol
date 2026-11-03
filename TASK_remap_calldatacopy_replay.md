# TASK: Bound observed calldata-copy remap replay

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem remap_preserved_mem_ops[local]:
  !fn roots remap inst s1 s2 v1 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    allocas_in_memory s1 /\ allocas_in_memory s2 /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    wf_function fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\

    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> ISTORE /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (?ops. (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
           ?v. ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn roots) /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the demonstrated default-limit failure in remap_preserved_mem_ops[calldatacopy], retaining its exact complete schema.
- Build allocaRemapProofsTheory at the default tactic limit, or report a precise new outside-scope blocker without editing it.
- Preserve every existing definition, statement, shared tactic and unrelated proof body, including the retained unverified BUMP edit.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Replay26857 stopped at line2787, fs[step_inst_base_def,AllCaseEqs()] in remap_preserved_mem_ops[calldatacopy], with a tactic timeout after2.5seconds. The complete exact remap_preserved_mem_ops statement, all admitted opcodes and every resume have been independently checked against the current definitions: PROVABLE without additional hypotheses. The existing proof stays in place.

The preceding descriptor repair passed the build prefix, while a retained BUMP error-transfer edit remains unverified because this earlier failure prevented reaching it. Their task is stopped. Neither edit is certified as a full-theory result. This isolated task repairs only the newly demonstrated calldata-copy blocker; do not amend generated records from the other task.

## Domain Constraints

- Edit only remap_preserved_mem_ops[calldatacopy] and necessary local helper theorems in venom/passes/shared/proofs/allocaRemapProofsScript.sml.
- All existing theorem statements, definitions, shared tactics, other resumes and unrelated proof bodies are frozen, including prior MCOPY, descriptor and BUMP edits.
- No new definition, axiom, admission, hypothesis, opcode exclusion, semantic change, timeout override, or TRY/ORELSE/FIRST around proof search.
- Report any newly failing outside-scope root or resume before editing it; no unchanged retries or speculative cleanup.
- Commit substantive source only, leaving generated task records untracked. End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/allocaRemapProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml
- venom/defs/venomInstScript.sml

## Notes

The schema has parsed previously; the current failure is in proof replay. Owner independently checks the frozen schema, source scope, forced default/CI replay and public dependencies after return. Those owner checks are not extra Alan completion gates.
