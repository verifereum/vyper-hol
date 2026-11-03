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

Theorem remap_rel_update_pv[local]:
  !fn roots remap s1 s2 out val1 val2 aid orig_off sz new_off.
    alloca_remap_rel fn roots remap s1 s2 /\
    out IN pointer_derived_vars fn roots /\
    out NOTIN roots /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    val1 - n2w orig_off = val2 - n2w new_off /\
    orig_off <= w2n val1 /\ w2n val1 < orig_off + sz /\
    new_off <= w2n val2 /\ w2n val2 < new_off + sz /\
    orig_off + sz < dimword (:256) /\
    new_off + sz < dimword (:256) ==>
    alloca_remap_rel fn roots remap
      (update_var out val1 s1)
      (update_var out val2 s2)
```

Do not modify these statements. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair actual default-limit proof failures within the three frozen roots and their resumes without changing any statement.
- Build allocaRemapProofsTheory with the default tactic limit and no new admissions.
- Preserve all definitions, other statements, shared tactics, unrelated proof bodies and previously completed remap/GAS repairs.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

Fresh remaining preserving-target validation rebuilt this dependency and stopped at the unchanged nonoutput_case opcode split, despite an earlier observed full owner default/CI replay passing. A fresh independent whole-statement audit checked all pointer-preserving, ALLOCA, PHI, DALLOCA, GAS and malformed successful-step cases: PROVABLE unchanged. This is a proof-budget repair, not a semantic or stage-contract amendment.

## Domain Constraints

- Edit only the three named proofs and their resumes, plus necessary local helpers in venom/passes/shared/proofs/allocaRemapProofsScript.sml. Repair actual encountered proof-budget failures; no speculative cleanup.
- All existing definitions, theorem statements and shared tactics are frozen. Preserve all unrelated proofs, including completed remap repair roots except the specifically reauthorized remap_preserved_no_pointer_ops.
- No new definition, axiom, admission, assumption, opcode exclusion or source/executable semantics change.
- Default2.5-second tactic limit; no override or TRY/ORELSE/FIRST around search.
- A newly failing root outside these three named theorems must be reported before expanding scope.
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


## Audited prefix extension

The first run stopped without a source diff before reaching the pointer-bound root: remap_preserved_no_pointer_ops[MEMTOP] exceeded the default limit in broad instruction-dispatch simplification, then one unchanged replay stopped in remap_rel_update_pv at fs[] after 58 goals. A fresh independent whole-statement audit of both exact roots and all current producers returned PROVABLE. MEMTOP uses equal memory lengths; GAS readings are retained by the residual frame; all other scalar and pointer cases satisfy the existing assumptions. Pointer-variable update needs only its supplied displacement/allocation/bounds witnesses and out-not-root condition; no new finiteness or other premise is needed. This amendment authorizes only those additional existing proof bodies and necessary local helpers. Preserve all definitions and statements, shared tactics, other proof bodies and completed repairs. No blind unchanged retries or speculative cleanup. Owner handles forced default/CI builds and public dependency checks after return.
