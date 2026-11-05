# TASK: Prove the pointer simulation of non-word literals (literal_buffer_sim_ptr)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem literal_buffer_sim_ptr:
  !d PG ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
    expr_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/exprSimPtrLiteralScript.sml`, currently admitted. All
existing definitions and all other theorem statements are frozen. New
proof-only helper lemmas, in `lowering/exprSimPtrLiteralScript.sml` or new
leaf theories next to it in `lowering/` (named `exprSimPtrLiteral*`), are
weakly frozen.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `exprSimPtrLiteralTheory` builds normally (proof steps on, default step
   limit) with no CHEAT and no parser warnings.
3. Edit only `lowering/exprSimPtrLiteralScript.sml` and new
   `lowering/exprSimPtrLiteral*Script.sml` leaf theories. No edits to any
   other existing file.

## Build

```sh
holbuild -j4 build exprSimPtrLiteralTheory
```

## Background

This is the pointer-safety twin (S3) of S1's literal simulation.
`expr_sim_ptr` and `expr_vv_sim_ptr` (`lowering/bodyPtrDefsScript.sml`)
are S1's `expr_sim`/`expr_vv_sim` (`lowering/exprSimDefsScript.sml`,
`lowering/exprSimHypsDefsScript.sml`) with the counted path replaced by
`gas_path_ptr` (`lowering/fragGasPathPtrScript.sml`): every step is
`ptr_inst_ok` (pointer discipline at lo = 0:
`venom/compiler/ptrDisciplineScript.sml`, `lowering/ptrSafeRunScript.sml`)
and threads a ghost (provenance map G, taint tn). The post adds
`ghost_inv`, `ptr_val_ok`/`ptr_vv_ok` and `ghost_kept` to S1's post.

The lowering (`compile_literal_vv`, `compile_bytelike_literal` in
`lowering/defs`/`exprLowering`): word literals (bool/int/decimal, and
bytesN/address literals, which are words) are a stack value with no code
(the expr_sim side is an empty counted path). Dynamic bytes and string
literals ALLOCA a fresh buffer (a new G site) sized
`32 + 32 * word_size (LENGTH bs)` and MSTORE the length and the padded
chunks into it, then hand out the buffer pointer as a memory value. The
ALLOCA'd site starts tainted (`mem_taint`); the stores write every byte
of the value's padded footprint with untainted data, so the value's bytes
end untainted and the robust `val_in_memory` in `ptr_mem_ok` holds.
`ptr_mem_ok`'s site bound is `w2n w + val_store_size tv v <= b + sz`
(`exprSimProps$val_store_size`, the word-padded footprint), which the
buffer size meets exactly.

S1's proofs (the simulation half; reuse them): `exprSimLiteralWord`,
`exprSimLiteralBytes`, `exprSimLiteralBuffer` (`literal_bytelike_gas_path`,
`literal_bytelike_counted_shape`, `literal_memory_vv_post`,
`compile_literal_other_vv_sim`), and the memory-safety twin
`bodyLiteralMemory`, `bodyLiteralForceMemory`. Some ancestors are admitted
in this checkout (an overlay admits theories not yet rebuilt at this
base); using them is expected and fine.

Already proved pointer helpers you can use:
`lowering/exprSimPtrPropsScript.sml` (`expr_vv_sim_ptr_stack`: the vv half
from the expr half for stack-valued forms; `ghost_inv_fresh_frame`;
`gas_path_ptr_one_step`, `emit_mload_ptr_path`), and the worked leaf
proofs `lowering/exprSimPtrFlagMemberScript.sml` (a word literal-like
case, empty path) and `lowering/exprSimPtrNameScript.sml`.

## Domain Constraints

- No definition changes, added assumptions, admissions, timeout overrides,
  or search tactics wrapped in `TRY`/`ORELSE`.
- Inherited admissions in ancestors are expected; add none of your own.
- Build at most `-j4`.

## Available Resources

- Target: `lowering/exprSimPtrLiteralScript.sml`
- Judgments and ghost posts: `lowering/bodyPtrDefsScript.sml`
- Counted ptr paths: `lowering/fragGasPathPtrScript.sml`,
  `lowering/fragGasSeqPtrScript.sml` (`gas_path_ptr_step`,
  `run_inst_seq_gas_path_ptr`), `lowering/gasSummaryComposePtrScript.sml`
- Pointer discipline: `venom/compiler/ptrDisciplineScript.sml`,
  `lowering/ptrSafeRunScript.sml`
- Pointer toolkit: `lowering/typedCopyPtrScript.sml`,
  `lowering/representationCleanPtrScript.sml`, `lowering/fragExecPtrScript.sml`,
  `lowering/typedCopyAmbientLib.sml`, `lowering/decoderGhostFramePtrScript.sml`
- S1 literal proofs: `lowering/exprSimLiteral*Script.sml`
- Memory twin: `lowering/bodyLiteral*MemoryScript.sml`

## Notes

The word case is already proved in the same script (`literal_word_sim_ptr`,
used by `literal_expr_sim_ptr`); this task is only the non-word (buffer)
case. There the vv result is a LocatedValue memory pointer, and the expr
half follows from it with no extra code. `literal_expr_sim_ptr` below it
must keep building.
