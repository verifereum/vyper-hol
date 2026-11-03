# TASK: Bound actual remap memory and error replay failures

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

- Repair observed default-limit failures in these exact roots, starting with remap_preserved_mem_ops[extcodecopy] and the retained unverified step_inst_base_error_transfer[BUMP].
- Build allocaRemapProofsTheory at the default tactic limit with no new admissions. Report any failure outside these three audited roots without editing it.
- Preserve definitions, statements, shared tactics and proof bodies without an actually demonstrated failure.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Replay27073 passed the repaired CALLDATACOPY region, then stopped at remap_preserved_mem_ops[extcodecopy] line2942, fs[step_inst_base_def,AllCaseEqs()], tactic timeout after2.5seconds. Existing calldatacopy_success_iff and its resume repair are committed475e6a99b/6c2dc219a. The complete exact remap_preserved_mem_ops schema and every admitted opcode/resume were independently audited PROVABLE without extra hypotheses. The other two complete schemas were also independently audited PROVABLE. No executable definitions have changed since those audits.

Descriptor repair passed a prior prefix, while retained BUMP source has not been reached after an earlier observed error_inline_tac timeout. The preceding tasks are stopped. Use this isolated task; do not amend their generated plans or infer a full certificate from their partial prefix results.

## Domain Constraints

- Source edits only in venom/passes/shared/proofs/allocaRemapProofsScript.sml: the three frozen roots, their resumes with actual demonstrated failures, and necessary local helper theorems.
- Start at the observed EXTCODECOPY failure; validate and repair the already observed BUMP failure after its upstream blockers are resolved. Further actually observed failures within these three complete audited roots are in scope; do not edit merely suspicious or unfailed resumes.
- Every definition and theorem statement is frozen. Shared ML tactics, unrelated proof bodies and completed nonfailing repairs remain unchanged.
- No new definition, axiom, admission, hypothesis, opcode exclusion, semantic change, timeout override or TRY/ORELSE/FIRST around proof search.
- Report any new failure outside the three audited roots before editing it. No blind unchanged retries.
- Commit substantive source only; leave generated records untracked. End messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/allocaRemapProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml
- venom/defs/venomInstScript.sml

## Notes

All exact schemas have parsed previously. Owner performs full schema/scope review and forced default/CI/public checks after return; those checks are not extra Alan completion gates.
