# TASK: Prove the pointer simulation of top-level names (toplevel_expr_sim_ptr)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem toplevel_expr_sim_ptr:
  !d PG ctx func cenv cx env ty ann nsid es.
    expr_sim_pre cenv cx env (TopLevelName ann nsid) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/exprSimPtrTopLevelScript.sml`, currently admitted. All
existing definitions and all other theorem statements are frozen. New
proof-only helper lemmas, in `lowering/exprSimPtrTopLevelScript.sml` or new
leaf theories next to it in `lowering/` (named `exprSimPtrTopLevel*`), are
weakly frozen.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `exprSimPtrTopLevelTheory` builds normally (proof steps on, default step
   limit) with no CHEAT and no parser warnings.
3. Edit only `lowering/exprSimPtrTopLevelScript.sml` and new
   `lowering/exprSimPtrTopLevel*Script.sml` leaf theories. No edits to any
   other existing file.

## Build

```sh
holbuild -j4 build exprSimPtrTopLevelTheory
```

## Background

This is the pointer-safety twin (S3) of S1's top-level-name simulation.
`expr_sim_ptr` and `expr_vv_sim_ptr` (`lowering/bodyPtrDefsScript.sml`)
are S1's `expr_sim`/`expr_vv_sim` (`lowering/exprSimDefsScript.sml`,
`lowering/exprSimHypsDefsScript.sml`) with the counted path replaced by
`gas_path_ptr` (`lowering/fragGasPathPtrScript.sml`): every step is
`ptr_inst_ok` (pointer discipline at lo = 0:
`venom/compiler/ptrDisciplineScript.sml`, `lowering/ptrSafeRunScript.sml`)
and threads a ghost (provenance map G, taint tn). The post adds
`ghost_inv`, `ptr_val_ok`/`ptr_vv_ok` and `ghost_kept` to S1's post. Both
judgments assume `~cenv.ce_is_ctor`: only runtime code is in scope
(constructor immutable reads go through ILOAD, which the pointer
discipline doesn't cover, and are excluded on purpose).

A TopLevelName reads a storage or transient variable (a pointer to its
slot as a value_vv; word values load with SLOAD/TLOAD, aggregates copy
slot by slot into a fresh ALLOCA buffer), an immutable or constant at
runtime (from the code's data section: word loads, or a code copy into a
fresh buffer), or a missing module (no admissible source run). Storage
and transient reads touch no memory pointer; copies write into a fresh
G site whose bytes the copy makes untainted, so the robust
`val_in_memory` in `ptr_mem_ok` holds. `ptr_mem_ok`'s site bound is
`w2n w + val_store_size tv v <= b + sz` (`exprSimProps$val_store_size`,
the word-padded footprint); type-sized buffers meet it.

For a storage or transient `LocatedValue` at slot `w` with type `ty`,
`ptr_vv_ok` also asks that every tainted `(k,b)` in `tn.t_stor`/`tn.t_trans`
with `w2n w <= w2n k < w2n w + type_slot_size ty`, `b < 32` be
`dead_bytes (current storage) (w2n w) ty (w2n k) b`. For a declared
variable this follows from the region being a live read
(`storage_read_live`, shown in S1's `exprSimTopLevelStorage` /
`accountsRelProps`) together with `ghost_inv`'s `stor_taint_ok`.

S1's proofs (the simulation half; reuse them): `exprSimTopLevel`,
`exprSimTopLevelStorage`, `exprSimTopLevelImmutable`,
`exprSimTopLevelMissing`, `exprSimTopLevelUndecodable`,
`exprSimTopLevelProps`, `exprSimStorageCopy`, and the memory-safety twin
`bodyToplevelMemory`, `bodyToplevelWordMemory`,
`bodyToplevelAggregateMemory`, `bodyImmutableCopyMemory`,
`bodyImmutableUnwrapMemory`, `bodyStorageCopyMemory`. Some ancestors are
admitted in this checkout (an overlay admits theories not yet rebuilt at
this base, e.g. `exprSimLeaves`, `exprSimStorageCopy`,
`storageCopyGasPath`); using their statements is expected and fine.

Already proved pointer helpers you can use:
`lowering/exprSimPtrPropsScript.sml` (`expr_vv_sim_ptr_stack`: the vv half
from the expr half for stack-valued forms; `expr_stack_outcome_ptr`;
`ghost_inv_fresh_frame`: ghost_inv across steps that touch only fresh
variables; `gas_path_ptr_one_step`; `emit_mload_ptr_path`), and the worked
leaf proofs `lowering/exprSimPtrNameScript.sml` and
`lowering/exprSimPtrFlagMemberScript.sml`.

Both judgments' posts also carry `ptr_buf_ok cenv e op G t`
(`lowering/bodyPtrDefsScript.sml`): when the value is not a word (a
non-word StackValue, or a LocatedValue at LocMemory), its pointer's G site
covers `type_memory_bytes cenv (lowered_value_type cenv e)` bytes from
the pointer, whenever that size is non-zero.
For a TopLevelName, `lowered_value_type` is the annotation, so a copy's fresh buffer must be at least `type_memory_bytes cenv ann` long (`expr_body_pre_copy_ok` relates it to `type_memory_size`).

## Domain Constraints

- No definition changes, added assumptions, admissions, timeout overrides,
  or search tactics wrapped in `TRY`/`ORELSE`.
- Inherited admissions in ancestors are expected; add none of your own.
- Build at most `-j4`.

## Available Resources

- Target: `lowering/exprSimPtrTopLevelScript.sml`
- Judgments and ghost posts: `lowering/bodyPtrDefsScript.sml`
- Counted ptr paths: `lowering/fragGasPathPtrScript.sml`,
  `lowering/fragGasSeqPtrScript.sml` (`gas_path_ptr_step`,
  `run_inst_seq_gas_path_ptr`), `lowering/gasSummaryComposePtrScript.sml`
- Pointer discipline: `venom/compiler/ptrDisciplineScript.sml`,
  `lowering/ptrSafeRunScript.sml`
- Pointer toolkit (copies into fresh buffers, clean bytes):
  `lowering/typedCopy*PtrScript.sml`, `lowering/wordCopyRobustPtrScript.sml`,
  `lowering/batchCopyRobustPtrScript.sml`,
  `lowering/representationCleanPtrScript.sml`, `lowering/fragExecPtrScript.sml`,
  `lowering/decoderGhostFramePtrScript.sml`
- S1 proofs: `lowering/exprSimTopLevel*Script.sml`,
  `lowering/exprSimStorageCopyScript.sml`
- Memory twin: `lowering/bodyToplevel*MemoryScript.sml`,
  `lowering/bodyImmutable*MemoryScript.sml`,
  `lowering/bodyStorageCopyMemoryScript.sml`

## Notes

Split by kind of top-level variable (storage/transient word, storage
aggregate copy, runtime immutable/constant word, immutable aggregate copy,
missing module) into helper lemmas, as S1 and the memory twin do.
