# TASK: Prove layout-converting memory copy

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/typedMemoryCopyScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_store_memory_typed_run:
  !cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((), sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- The theorem and recursive helper cases have kernel proofs with no new cheats, axioms or oracle dependencies beyond inherited ancestor admissions.
- Changed/added theories build with the default 2.5-second proof-step budget and ordinary checkpoints enabled.
- No executable changes, checker restrictions, or new assumptions on stage/top-level theorems.
- Existing proven statements remain available. New internal helper statements are weakly frozen and may be corrected where necessary; report every new definition or changed statement.
- A counterexample must be checked against the actual executable producer; do not silently weaken the frozen theorem.

## Build

From the project root:

```bash
holbuild -j2 build typedMemoryCopyTheory
```

Build only changed/added theories, never a full dependent cone or the bytecode rollup. Do not increase tactic timeouts or use --skip-proof-steps for proof development. Use existing shared machinery before introducing more; prove reusable machinery before its consumers.

## Background

Memory-backed assignment can widen a source aggregate's bounds, changing offsets and strides. The shared typed copier must preserve its value at the destination layout. This theorem is the execution/frame interface needed by AnnAssign, local Assign and tuple unpacking. Storage/transient copying and aggregate returns are separate work.

## Domain Constraints

- Default 2.5-second proof steps; split expensive tactics instead of raising budgets.
- No TRY/ORELSE around search tactics. No interactive proof state.
- Keep the original compiler and source semantics unchanged.
- Do not edit unrelated proofs, the build manifest or other worktrees.
- Do not push or open a PR. Commit meaningful built milestones with `Bot: sol (OpenAI GPT-6.1 Sol)` trailer.
- The temporary cheat in the new theorem is scaffolding to replace, never a permitted dependency.
- Keep all Alan state/task artifacts out of the eventual PR.

## Available Resources

- `lowering/defs/contextScript.sml`: actual mutually recursive typed copier, source/destination offsets, loops and bytestring copies.
- `lowering/defs/typedCopyDomainScript.sml`: existing total rank and acyclic metadata domain.
- `lowering/defs/typedCopyMetadataScript.sml`, `typedCopyProducerScript.sml`, `typedCopyAgreementScript.sml`: real producer and domain facts.
- `lowering/defs/compileEnvScript.sml`: compiler state, freshness, struct metadata and static layout sizes.
- `semantics/type/vyperTypeSystemScript.sml`: `arg_type_fits` and `type_widens_to`.
- `semantics/prop/vyperTypeArgFitsScript.sml`: widening preserves value typing.
- `semantics/vyperValueScript.sml`: evaluated type layouts and capacities.
- `lowering/defs/valueEncodingScript.sml`, `lowering/valueEncodingPropsScript.sml`, `lowering/valueEncodingProofsScript.sml`: in-memory value representation, sparse-array defaults and write frames.
- `lowering/valueCopyScript.sml`, `lowering/valueCopyBytesScript.sml`, `lowering/valueCopySourceScript.sml`: existing copy, bytestring and source-layout proofs.
- `lowering/fragExecScript.sml`: fragment composition and finite-loop rule; no PHI-free endpoint premise is needed by the existing loop rule.
- `lowering/exprLoweringPropsScript.sml`: typed-family compiler monotonicity and `ci_mono_typed_memory_family`.
- `lowering/exprSimAggregateLayoutScript.sml`: pure struct size correspondence proof under the same metadata clauses.
- `lowering/stmtSimDeclMemScript.sml`, `lowering/stmtSimAssignMemScript.sml`: real staging allocations and current memory statement consumers.
- `lowering/tupleAssignMemoryScript.sml`, `lowering/tupleLocalStoreRunScript.sml`: tuple staging and unread-suffix consumers.
- `docs/HOL4_PROOF_CONTROL_LESSONS.md`: local proof control conventions.

## Notes

Pinned Python producer inspected at `9362e36b145c4b63ceb6a893018ea970e78bf6a6`, `vyper/codegen_venom/context.py` and `stmt.py`. The source-to-destination relation is the existing checker widening relation, including nested arrays and tuples, and nominal structs. No new semantic relation is requested.
