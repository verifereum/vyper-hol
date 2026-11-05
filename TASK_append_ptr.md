# TASK: pointer-safe dynarray append

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyPtrLogCasesScript.sml

## Theorem Statement (FROZEN)

`body_append_case_ptr` in `lowering/bodyPtrLogCasesScript.sml`:

```sml
Theorem body_append_case_ptr:
  !cx t e.
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_ptr_ok cx e) /\
    body_base_target_ptr_ok cx t ==>
    body_stmt_ptr_ok cx (Append t e)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrLogCasesTheory` passes, with `body_append_case_ptr` proved with no `cheat` in its proof or in any theory you add. CHEAT warnings inherited from the locally admitted ancestors are expected (see Domain Constraints). `body_log_case_ptr` in the same file is not yours: leave its `cheat` as it is.
2. No duplicate lemmas. Search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrLogCasesTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation. `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per statement form. Each case is the twin of S1's case of the same name, with `stmt_frag_ptr` in place of S1's `stmt_frag` and `expr_sim_ptr` in place of `expr_sim`. `stmt_frag_ptr` concludes `gas_outcome_ptr` over the counted path `gas_path_ptr`, on which every edge passes `ptr_safe_step` (so every instruction passes `ptr_inst_ok` with lo = 0), with the ghost provenance `G` and taint `tn` threaded along. Its post is S1's post plus `ghost_inv` and the ghost frame. So the simulation half replays S1's proof (reuse S1's lemmas); the new work is the ghost and the per-instruction check.

S1's proof is `body_append_case` and `body_append_storage_other` in `alan-ref/s1/bodySimStmtCasesScript.sml.txt`. `supported_append_target` (`lowering/supported/supportedStmtsScript.sml`) admits only `TopLevelNameTarget` of a storage or transient DynArray whose element is a full word type (`supported_storage_dynamic_array`), so every other target is vacuous. The storage case is `body_append_storage_fragment` (`alan-ref/s1/bodyAppendStorageAdapterScript.sml.txt`) over `compile_append_storage_word_stmt_frag` (`alan-ref/s1/stmtSimAppendStorageComposeScript.sml.txt`), `stmtSimAppendStorage`, `bodyAppendStorageFacts` and `appendStorageRel`. The lowering is `compile_stmt`'s Append case in `lowering/defs/stmtLoweringScript.sml` (~line 1081) and `compile_dynarray_append` in `lowering/defs/exprLoweringScript.sml` (~line 1099): evaluate the element, SLOAD/TLOAD the length, `LT` against the capacity, ASSERT, compute the element slot (ADD, MUL, ADD), SSTORE/TSTORE the element, ADD 1, SSTORE/TSTORE the new length.

The pointer twins of that chain don't exist yet; building them, as reusable lemmas in leaf theories, is part of this task.

## Domain Constraints

- Statements frozen: the target, and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrLogCasesScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file: no edits to bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, the toolkit theories, ptrSafeRun, ptrDiscipline, bodySim, exprSim*, stmtSim*, stmtFragPtr, stmtAbortPtr, stmtAssertPtr, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- About 140 theories of this tree have their proofs admitted locally (cheated in the working tree, hidden from git). Those inherited admissions are expected: CHEAT warnings that come from them are fine. Your own files and the target's proof must contain no `cheat`. The S1 lemmas you use may be among the admitted ones (all of `stmtSimAppendStorage*`, `bodyAppendStorage*` and `appendStorageRel` are, locally); use them anyway, and read their unadmitted copies in `alan-ref/s1/` to see how they are proved.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix.
- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Piece theory | `lowering/bodyPtrLogCasesScript.sml` | The frozen target |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_stmt_ptr_ok`, `body_expr_ptr_ok`, `body_base_target_ptr_ok` |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `stmt_frag_ptr`, `expr_sim_ptr`, `ghost_inv`, `ghost_kept`, `ptr_val_ok`, `stor_taint_ok`, `cx_dead`, `stmt_exit_ptr` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr*`, `gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, `gas_path_ptr_abort`, `run_inst_seq_abort_gas_path_ptr` |
| Path to run | `lowering/gasPathPtrExecScript.sml` | `gas_path_ptr_exec` |
| Proved statement helpers | `lowering/stmtFragPtrScript.sml`, `lowering/stmtAbortPtrScript.sml`, `lowering/stmtAssertPtrScript.sml`, `lowering/bodyPtrExitCasesScript.sml`, `lowering/bodyPtrCtrlCasesScript.sml` | Cons/env helpers, `ghost_inv_jump_to`, `not_fresh_at_mono`, aborts (the capacity ASSERT fails into an abort), worked examples of proved `stmt_frag_ptr` cases |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok`, `access_ok`, `taint_ok`, `out_taint`, `step_taint`, `store_taint`, `key_update` |
| Dead storage | `lowering/defs/compileEnvScript.sml` (`dead_bytes`, `storage_dead`) | Slots of a dynarray at or past its length are dead; the length word never is |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/ghostPcTransportPtrScript.sml` | Per-instruction pointer facts and ghost transport, over the fixed-run `frag_exec_ptr` |
| Assign-case twins | `lowering/bodyPtrAssignCasesScript.sml` | The storage-assign cases keep `stor_taint_ok` the same way (may still be admitted) |
| S1 proofs (unadmitted copies) | `alan-ref/s1/*.sml.txt` | `bodySimStmtCases`, `bodyAppendStorageAdapter`, `bodyAppendStorageFacts`, `appendStorageRel`, `stmtSimAppendStorage`, `stmtSimAppendStorageCompose`. Read these, not the copies under `lowering/`, which are admitted locally |

## Notes

- The element is a full word, so no memory is read or written by the append itself: only the element's evaluation (covered by `expr_sim_ptr`) touches memory.
- SSTORE/TSTORE replace the key's taint with the stored value's (`store_taint`, `key_update`). The element operand is untainted (`ptr_val_ok` of a word type), and so is the slot address, built from the untainted loaded length (the length word is never dead, so `stor_taint_ok` leaves it untainted) and literals. So after the element store, slot `len` is untainted, and slots past the new length stay dead: `stor_taint_ok` holds after the length bump.
- The capacity ASSERT failing is an abort; no store has happened yet.
