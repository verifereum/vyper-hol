# TASK: pointer-safe mapping subscript (seam of the subscript lane)

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
Location: lowering/bodyPtrSubscriptSeamMapScript.sml

## Theorem Statement (FROZEN)

`subscript_map_ptr` in `lowering/bodyPtrSubscriptSeamMapScript.sml`:

```sml
Theorem subscript_map_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es kt vt.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    place_type cenv e1 = MapPT kt vt /\
    expr_map_sim_ptr d ctx PG func cenv cx ty e1 es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann e1 e2) es
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrSubscriptSeamMapTheory` passes, with `subscript_map_ptr` proved with no `cheat` in its proof, in `lowering/bodyPtrSubscriptSeamMapScript.sml`, or in any theory you add (CHEAT warnings inherited from admitted ancestor theorems are expected; see Domain Constraints).
2. No duplicate lemmas: search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrSubscriptSeamMapTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation: `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per expression and statement form. `body_expr_ptr_ok cx e` says: for every frame meeting `body_inv` and `expr_body_pre`, both `expr_sim_ptr` (the lowered value, `lower_value`) and `expr_vv_sim_ptr` (the value-or-place, `compile_expr`) hold (and, for an array literal, its elements are `body_exprs_ptr_ok`). Each is S1's `expr_sim`/`expr_vv_sim` (`lowering/exprSimDefsScript.sml`) with a counted path on which every edge passes `ptr_safe_step`, with the ghost provenance `G` and taint `tn` threaded along, and with the post extended by `ghost_inv`, `ptr_val_ok`/`ptr_vv_ok`, `ptr_buf_ok` (a memory value's pointer covers the whole buffer of its lowered type, `type_memory_bytes cenv (lowered_value_type cenv e)`) and `ghost_kept`. The posts describe a value at `post_value_type cenv e`, the type its lowered memory is laid out at: an expression's own type, but for an internal call whose site widens the callee's return type. So the simulation half replays S1's proof of the same case; the new work is the ghost and the per-edge pointer check.

These judgments are the runtime instances (`cx_dead cx`, `lo = 0`, `~cenv.ce_is_ctor`) of the `(D, lo)` judgments `expr_sim_ptr_at`/`expr_vv_sim_ptr_at` in `lowering/bodyPtrDefsScript.sml`; the theorems `expr_vv_sim_ptr_def`, `expr_sim_ptr_def`, `ghost_inv_def`, `ghost_kept_def`, `stor_taint_ok_def` there state them as plain definitions. Work at the runtime instances; the `(D, lo)` port of this case comes later.

The subscript case `subscript_expr_ptr_ok` (`lowering/bodyPtrSubscriptScript.sml`) is proved as S1's `body_subscript_case` and `compile_subscript_case` are: a base whose lowered value is laid out at another type than its own (a widening internal call) is an admitted residual, and the rest go by the base's `place_type`: a mapping, a tuple, an array whose index frames its base in memory, one whose base is a runtime immutable, and every other array (admitted, as S1 admits it: the base's place can go stale when the index writes storage, pops or changes a local). This task is one of those cases: a subscript of a mapping whose value is not a mapping, given the base's mapping judgment `expr_map_sim_ptr` (`lowering/bodyPtrSubscriptMapDefsScript.sml`, a new definition: the pointer twin of S1's `expr_map_sim` in `lowering/exprSimMapDefsScript.sml`, with S1's admissibility predicate `expr_map_res_ok`; the composer gets it from an admitted residual). The key is lowered after the base, a bytestring key is hashed (`compile_keccak256_key`), and `compile_mapping_subscript` stores the slot and the key word in a fresh 64-byte buffer and takes its `SHA3`. The result is a storage or transient place.

## Domain Constraints

- Statements frozen: the target and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrSubscriptSeamMapScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file (but see "Lane helper theories" below): no edits to bodyPtrDefs, bodyPtrPreds, bodyPtrExprCases, bodyPtrSubscriptMapDefs, exprPtrUnwrap, fragGasPathPtr, the toolkit theories, ptrSafeRun, bodySim, exprSim*, stmtSim*, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- Theorems of ancestor theories that are admitted in this tree (proved with `cheat`, such as S1's admitted cases) are inherited admissions: you may use them, and the CHEAT warnings they bring are expected. Your own files and the target's proof must contain no `cheat`. Don't use this split's sibling seams or its residuals (`bodyPtrSubscriptSeam*`, `bodyPtrSubscript*Residual`): they are admitted for this split, not inherited.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas. Use holbuild only (no Holmake, no `holbuild run`/`repl`), at most `-j4`.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix, and prefix them with `bodyPtrSubscriptSeamMap` so they don't clash with sibling tasks' theories (the other seams of this split run beside you).
- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Target | `lowering/bodyPtrSubscriptSeamMapScript.sml` | The frozen seam (hints in the comment above it) |
| Parent | `lowering/bodyPtrSubscriptScript.sml` | The lane's frozen theorem, proved from this seam, its sibling seams and three admitted residuals |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_expr_ptr_ok`, `body_exprs_ptr_ok`, `body_base_target_ptr_ok` |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `expr_sim_ptr`, `expr_vv_sim_ptr` (and their `_at` forms), `ghost_inv`, `ghost_kept`, `ptr_val_ok`, `ptr_mem_ok`, `ptr_vv_ok`, `ptr_buf_ok`, `stor_taint_ok`, `cx_dead` |
| Posts | `lowering/loweringPostsScript.sml` | `vv_post`, `vv_holds`, `vv_at`, `vv_own`, `vv_storage_live`, `expr_post`, `post_value_type` |
| Value/place glue | `lowering/exprPtrUnwrapScript.sml` | `expr_sim_ptr_of_vv`, `expr_vv_sim_ptr_stack`, `expr_stack_outcome_ptr` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then`, `gas_path_ptr_erase` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr`, `_bind_normal`, `_bind_exception`, `_finally`, `gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, aborts |
| Path to run | `lowering/gasPathPtrExecScript.sml` | `gas_path_ptr_exec`, `jump_entry_ghost` |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok`, `access_ok`, `taint_ok`, `out_prov`, `ghost_step`, `entry_prov`, `entry_taint_vars` |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/typedCopy*PtrScript.sml`, `lowering/wordCopyRobustPtrScript.sml`, `lowering/batchCopyRobustPtrScript.sml`, `lowering/robustCopyTransportPtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/ghostPcTransportPtrScript.sml`, `lowering/liveArrayTransportPtrScript.sml`, `lowering/ptrCoverageScript.sml`, `lowering/allocationPtrScript.sml`, `lowering/structChildPtrScript.sml` | Per-instruction pointer facts (MLOAD/MSTORE/MCOPY/ALLOCA access_ok and taint_ok, copies, ghost transport), stated over the fixed-run `frag_exec_ptr`: use them for the per-instruction facts and rebuild the counted paths with the combinators above |
| Statement-level ptr proofs (examples of the port) | `lowering/stmtFragPtrScript.sml`, `lowering/stmtAssertPtrScript.sml`, `lowering/stmtAbortPtrScript.sml` | How an `expr_sim_ptr` is consumed and a counted ptr path is built (JNZ edge, aborts, `ghost_inv_jump_to`, `not_fresh_at_mono`) |
| S1 proof of this case | `compile_subscript_map_case` over `compile_mapping_subscript_outcome` and `mapping_leaf_vv_holds` in `lowering/exprSimSubscriptMapScript.sml`, with `lowering/exprSimMapDefsScript.sml` | The non-pointer simulation of the same case, in this tree |
| Memory twin | `lowering/*Memory*Script.sml`, `lowering/*Mem*Script.sml` | A sibling safety proof (`gas_path_mem`) of the same expression shapes; the ptr port follows the same pattern with the ghost added |
| Lowering | `lowering/defs/exprLoweringScript.sml` (and `rg 'compile_expr_def\|unwrap_value_def\|lower_value_def\|compile_subscript_def'`) | `compile_expr`, `compile_subscript`, `lower_value`, `unwrap_value` |
| Earlier run's theories (reference only) | `alan-ref/s3ptr-sub-lane/*.sml.txt`, `alan-ref/s3ptr-sub-lane/subscript-consumer-gap.md`, `alan-ref/README.txt` | The rest of the theories an earlier alan run on the whole subscript case wrote, on the base before the `(D, lo)` port, and its audit of the index/base interface. Not built and not in git: they may not build against this tree's definitions. Read them for proof ideas; rebuild any lemma you take in a new theory of your own |

## Notes

- The result can be a `LocatedValue` in storage or transient storage: `ptr_vv_ok` then owes the taint bound over the place's own type's dead bytes. A live place gets it from `storage_read_live` and `stor_taint_ok` (in `ghost_inv`). When the subscript has no effect, `vv_post` also owes `vv_storage_live` of the result place.

## Lane helper theories

These `lowering/bodyPtrSubscript*Script.sml` theories were written by an earlier alan run on the whole subscript case and are proved here (built on this branch): `TupleDispatch`, `TupleSuffix`, `TupleLayout`, `TupleSource`, `BoundsRun`, `SignedBounds`, `RejectedSelector`, `CountedAdd`, `ScratchStore`, `ScratchTransfer`, and the theories they import (`Address`, `Boundary`, `Bounds`, `BoundsOutcome`, `Coverage`, `CurrentMemory`, `CurrentRootCase`, `CurrentRootEndpoint`, `DynamicAddress`, `DynamicSelector`, `History*`, `IndexExecution`, `IndexRefresh`, `LengthRead`, `LocalAlias`, `MarkedCompose`, `MarkedEndpoint`, `MemoryRebuild`, `NamedIndex`, `NamedRoot`, `NamedTuplePostBoundary`, `Numeric`, `OwnerPop`, `PathRebuild`, `PendingInit`, `ReadOnly`, `SignedEdge`, `SignedSelector`, `WordProvenance`, and the probes `CapturedInitProbe`, `HistoryLayoutProbe`, `MutableProbe`, `PopAppendProbe`). You may use them, and add new theorems to them; don't change or delete their existing theorems, which other seams of this split use. The probes checked candidate counterexamples and found none: use them for their checked lemmas only. `exprPtrUnwrap`'s `expr_sim_ptr_of_vv` turns an `expr_vv_sim_ptr` into an `expr_sim_ptr`; `bodyPtrSubscriptTupleDispatch` has the tuple dispatch (`tuple_subscript_pre`, `tuple_subscript_compile`, `tuple_subscript_source`). The rest of that run's theories are reference copies under `alan-ref/s3ptr-sub-lane/` (see Available Resources).
