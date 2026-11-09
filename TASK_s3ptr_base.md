# TASK: pointer-safe assignment to a base target case

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyPtrAssignCasesScript.sml

## Theorem Statement (FROZEN)

`body_assign_case_ptr` in `lowering/bodyPtrAssignCasesScript.sml`:

```sml
Theorem body_assign_case_ptr:
  !cx t e.
    (!s'' pv t'.
       eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ptr_ok cx t) /\
    body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (Assign (BaseTarget t) e)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrAssignCasesTheory` passes, with `body_assign_case_ptr` proved with no `cheat` in its proof or in any theory you add (CHEAT warnings inherited from the locally admitted ancestors and from `bodyPtrAssignResidual`'s RESIDUAL lemmas are expected; see Domain Constraints). Other theorems of the target file that are still `cheat` are not yours: leave them.
2. No duplicate lemmas: search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrAssignCasesTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation. `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per statement form. Each case is the twin of S1's case of the same name, with `stmt_frag_ptr` in place of S1's `stmt_frag`. `stmt_frag_ptr` concludes `gas_outcome_ptr` over a counted path `gas_path_ptr` on which every edge passes `ptr_safe_step`, with the ghost provenance `G` and taint `tn` threaded along. Its post is S1's post plus `ghost_inv` at the end and the ghost frame on variables older than `sa`. The judgments assume `~cenv.ce_is_ctor` (runtime code only), so constructor-only shapes (immutable stores) are vacuous here.

There is no lemma lifting S1's `stmt_frag` to `stmt_frag_ptr`: the simulation half is rebuilt on the pointer path, replaying S1's proof shape and reusing S1's lower-level facts (evaluation lemmas, code layout, `stmt_state_rel` preservation of a store), and the ghost half is added. The pointer twins of the S1 statement fragments for this case don't exist yet; building them, as reusable lemmas in leaf theories, is part of this task.

Facts about the ghost:
- Stores go through `compile_ptr_store` (lowering/defs). A memory store needs its target pointer covered: `ptr_covers` from `ghost_inv`'s locals clause for a local, or the target's `ptr_vv_ok`/`ptr_mem_ok`.
- A storage or transient store must keep `stor_taint_ok`: taint may sit in storage only in dead bytes, and an SSTORE/TSTORE of an untainted word keeps it.
- After a store, `ghost_inv`'s locals clause needs every live local's value in memory "whatever its tainted bytes hold" (`mem_agree_outside`); an MSTORE of an untainted word clears those bytes' taint, and a copy moves taint byte for byte from a source whose `ptr_mem_ok` already says the same of its own bytes.
- Locals are held through pointer variables (`PtrVar (Var p) sz`), so writing a local writes memory, not an older variable.

S1's proof is `body_assign_case` in `alan-ref/s1/bodySimStmtCasesScript.sml.txt`. It splits by target:
- a word-typed local: `body_assign_local_word` (`compile_assign_local_stmt_frag`, stmtSimAssign);
- a memory local whose RHS is lowered at its own type or a fitting bytestring, or an empty value: `body_assign_local_memory` (stmtSimAssignMem);
- a memory local assigned an internal call whose return type widens otherwise: RESIDUAL, `body_assign_widened_aggregate_call_ptr`;
- a supported scalar top-level (storage/transient word): `body_assign_toplevel_word` (stmtSimAssignStorage);
- a storage/transient aggregate (not a dynamic array): `body_assign_toplevel_copy` (stmtSimAssignStorageCopy);
- a word field of a local struct: `body_assign_attr_local` (stmtSimAssignAttr);
- a word field of a storage/transient struct: `body_assign_attr_storage` (stmtSimAssignAttrStorage);
- anything else (subscripts, nested and aggregate fields, storage dynamic arrays): RESIDUAL, `body_assign_other_ptr`.
The two RESIDUAL lemmas are in `lowering/bodyPtrAssignResidualScript.sml`, admitted; they are not yours to prove.

## Domain Constraints

- Statements frozen: the target, and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrAssignCasesScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Other cases of the target file are proved in parallel by other runs: leave them as they are. Do not edit any other existing theory: no edits to bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, the toolkit theories, ptrSafeRun, bodySim, exprSim*, stmtSim*, stmtFragPtr, stmtAbortPtr, stmtAssertPtr, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- About 140 theories of this tree have their proofs admitted locally (cheated in the working tree, hidden from git). Those inherited admissions are expected: CHEAT warnings that come from them are fine. Your own files and the target's proof must contain no `cheat`. The S1 lemmas in `lowering/` you use may be among the admitted ones; use them anyway.
- The S1 copies under `alan-ref/s1/` come from S1's own branch, which ported S1 to the counted form after this tree was cut. Their lemma names and statements can differ from `lowering/` here; a lemma that exists only in `alan-ref/` isn't loadable: re-derive what you need in your own leaf theory (under a `_ptr` or otherwise distinct name).
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix. Prefix your leaf theories with `assignBasePtr` so they don't collide with the parallel runs on the other cases.
- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Piece theory | `lowering/bodyPtrAssignCasesScript.sml` | The frozen target |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_stmt_ptr_ok`, `body_expr_ptr_ok`, `body_base_target_ptr_ok`, `body_tuple_target_ptr_ok` |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `stmt_frag_ptr`, `expr_sim_ptr`, `expr_vv_sim_ptr`, `frame_ret_ok_ptr`, `ghost_inv`, `ghost_kept`, `ptr_covers`, `ptr_val_ok`, `ptr_vv_ok`, `ptr_mem_ok` (bound `val_store_size`), `ptr_buf_ok` (a memory value's site covers its lowered type's whole buffer), `stor_taint_ok`, `cx_dead`, `stmt_exit_ptr` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr*`, `gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, aborts |
| Statement helpers already proved | `lowering/stmtFragPtrScript.sml`, `lowering/stmtAbortPtrScript.sml`, `lowering/stmtAssertPtrScript.sml`, `lowering/bodyPtrCtrlCasesScript.sml`, `lowering/bodyPtrExitCasesScript.sml` | `stmt_frag_cons_env_ptr`, `compile_expr_stmt_frag_ok_ptr` (an expression statement over `expr_vv_sim_ptr`: the closest model for running the RHS and continuing), `ghost_inv_jump_to`, `not_fresh_at_mono`, `ghost_inv_gas_obs`, `cenv_top_ext_*`; the abort edge |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok`, `access_ok`, `taint_ok`, `out_prov`, `out_taint`, `ghost_step` |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/typedCopy*PtrScript.sml`, `lowering/wordCopyRobustPtrScript.sml`, `lowering/batchCopyRobustPtrScript.sml`, `lowering/robustCopyTransportPtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/typedCopyLoop*PtrScript.sml`, `lowering/allocationPtrScript.sml`, `lowering/localPtrsPropsScript.sml`, `lowering/ptrCoverageScript.sml`, `lowering/structChildPtrScript.sml` | Per-instruction pointer facts (copies, stores, word-copy loops, ALLOCA buffers, ghost transport), stated over the fixed-run `frag_exec_ptr`: use them for the per-instruction facts and rebuild the counted path with the combinators above |
| S1 proofs (unadmitted, ported to counted form) | `alan-ref/s1/*.sml.txt` | S1's proof of the case (`bodySimStmtCasesScript.sml.txt`, `bodySimDeclCasesScript.sml.txt`) and the statement fragments it dispatches to (`stmtSimAssign*`, `stmtSimAugAssign*`, `stmtSimDecl*`, `tuple*`, `targetPlaceSim`). Read these, not the copies under `lowering/`, which are admitted locally |
| Memory twin (another checked counted path, same shapes) | `lowering/bodyDeclMemoryScript.sml`, `lowering/bodyCopyMemoryScript.sml`, `lowering/bodyToplevel*MemoryScript.sml`, `lowering/bodyStorageCopyMemoryScript.sml`, `lowering/tupleAssignMemoryScript.sml`, `lowering/memoryLocalRhsPropsScript.sml`, `lowering/bodyEnvMemoryScript.sml` | How the S1 assignment shapes were ported onto `gas_path_mem`; the ptr port follows the same pattern with the ghost added |
| Lowering | `lowering/defs/stmtLoweringScript.sml`, `lowering/defs/exprLoweringScript.sml`, `lowering/defs/contextScript.sml` | `compile_stmt`, `stmt_env`, `compile_ptr_store`, `compile_assign_*`, `compile_alloc_buffer`, `compile_word_copy_loop` |

## Notes

- A non-word RHS in memory is read whole by `compile_assign_value`: the memory-to-memory staging copies, and a bytestring copy to storage/transient reads, `type_memory_bytes cenv (lowered_value_type cenv e)` bytes from the RHS pointer. `ptr_buf_ok` in `expr_sim_ptr`'s / `expr_vv_sim_ptr`'s post covers exactly that read (`ptr_mem_ok`'s `val_store_size` bound alone doesn't).
- A storage aggregate copy (`body_assign_toplevel_copy`) reads the RHS from memory and SSTOREs words: the stored words must be untainted, or land only in dead bytes, to keep `stor_taint_ok`; the RHS's `ptr_mem_ok` says its value is in memory whatever its tainted bytes hold.
- The RESIDUAL lemmas of `lowering/bodyPtrAssignResidualScript.sml` are frozen and admitted: dispatch to them exactly where S1 dispatches to the S1 lemma of the same name (minus `_ptr`), and don't prove or restate them.
