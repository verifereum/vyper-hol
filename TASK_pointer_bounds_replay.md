# TASK: Bound existing pointer allocation-bound preservation replay

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem step_preserves_ptrs_in_alloca_bounds[local]:
  !fn roots inst bb s v.
    ptrs_in_alloca_bounds fn roots s /\
    pointer_arith_in_region fn roots /\
    pointer_confined fn roots /\
    phi_pv_all_var fn roots /\
    fn_inst_wf fn /\
    ssa_form fn /\ FINITE roots /\ roots SUBSET alloca_roots fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    step_inst_base inst s = OK v /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (is_alloca_op inst.inst_opcode ==>
      inst.inst_outputs = [HD inst.inst_outputs] /\
      HD inst.inst_outputs IN roots /\
      inst.inst_id NOTIN FDOM s.vs_allocas /\
      ?alloc_size. inst.inst_operands = [Lit alloc_size] /\
                   0 < w2n alloc_size /\
                   s.vs_alloca_next + w2n alloc_size < dimword (:256)) ==>
    ptrs_in_alloca_bounds fn roots v
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair actual default-limit proof failures within this root and its resumes without changing its statement.
- Build allocaRemapProofsTheory with the default tactic limit and no new admissions.
- Preserve all definitions, other statements, shared tactics, unrelated proof bodies and previously completed remap/GAS repairs.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Fresh remaining preserving-target validation rebuilt this dependency and stopped at the unchanged nonoutput_case opcode split, despite an earlier observed full owner default/CI replay passing. A fresh independent whole-statement audit checked all pointer-preserving, ALLOCA, PHI, DALLOCA, GAS and malformed successful-step cases: PROVABLE unchanged. This is a proof-budget repair, not a semantic or stage-contract amendment.

## Domain Constraints

- Edit only the named proof and its resumes, plus necessary local helpers in venom/passes/shared/proofs/allocaRemapProofsScript.sml. Repair actual encountered proof-budget failures; no speculative cleanup.
- All existing definitions, theorem statements and shared tactics are frozen. Preserve the completed thirteen remap repair roots and all unrelated proofs.
- No new definition, axiom, admission, assumption, opcode exclusion or source/executable semantics change.
- Default2.5-second tactic limit; no override or TRY/ORELSE/FIRST around search.
- A newly failing root outside this named theorem must be reported before expanding scope.
- Commit substantive source only, leave generated task records untracked. End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- venom/passes/shared/proofs/allocaRemapProofsScript.sml
- venom/defs/venomExecSemanticsScript.sml
- venom/defs/venomStateScript.sml
- venom/defs/venomInstScript.sml
- venom/passes/shared/proofs/passSharedSubstScript.sml
- venom/passes/concretize_mem_loc/proofs/concretizeMemLocTransitionProofsScript.sml

## Notes

The exact statement has parsed in current forced validation. Actual failure: nonoutput_case resume, line5231 Cases_on inst.inst_opcode then gvs[is_alloca_op_def],101goals. Existing proof retained. Existing exported allocation-map and nonoutput-variable preservation lemmas and region-extension facts are already available in this theory. No exact historical repair was found. Owner audits frozen schemas and forced default/CI replay plus public dependency tags after return.
