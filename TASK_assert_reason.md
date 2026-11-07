# TASK: pointer-safe assert with a reason

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyPtrExitCasesScript.sml

## Theorem Statement (FROZEN)

`body_assert_reason_case_ptr` in `lowering/bodyPtrExitCasesScript.sml`:

```sml
Theorem body_assert_reason_case_ptr:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ptr_ok cx se) /\
    body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (Assert e (AssertReason se))
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrExitCasesTheory` passes, with `body_assert_reason_case_ptr` proved with no `cheat` in its proof or in any theory you add. CHEAT warnings inherited from the locally admitted ancestors are expected (see Domain Constraints). `body_raise_reason_case_ptr` in the same file is not yours (a separate run proves it): leave it as it is.
2. No duplicate lemmas. Search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`. The raise-with-reason case, proved by a separate run, uses the same revert encoder; its helpers will be merged with yours afterwards, so name yours for what they state.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrExitCasesTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation. `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per statement form. Each case is the twin of S1's case of the same name, with `stmt_frag_ptr` in place of S1's `stmt_frag`. `stmt_frag_ptr` is a counted path `gas_path_ptr` on which every edge passes `ptr_safe_step`, with the ghost provenance `G` and taint `tn` threaded along. So the simulation half replays S1's proof; the new work is the ghost and the per-instruction check `ptr_inst_ok`.

S1's proof is `body_assert_reason_case` in `alan-ref/s1/bodySimStmtCasesScript.sml.txt`. The condition is a JNZ as in the bare assert; the failing branch runs the same revert-with-reason encoder as `raise` with a reason. S1 splits the reason four ways:
- a string literal: `compile_assert_reason_lit_frag`, stmtSimReason
- a word or memory value: `compile_assert_reason_frag`, stmtSimReasonExpr
- a storage or transient pointer: `compile_assert_storage_reason_frag`, stmtSimReasonStorage(Path)
- a pointer into code (an immutable): `body_assert_reason_other`, stmtSimReasonCode
(`assert_reason_vv_sim` in bodySimStmtCases gives the reason's simulation after the condition fails.)

Their pointer twins don't exist yet. Building them, as reusable lemmas in leaf theories, is part of this task. The bare and unreachable raise and assert are already done in this piece: `lowering/stmtAbortPtrScript.sml` (REVERT 0 0 / INVALID pass `ptr_inst_ok`; the abort edge) and `lowering/stmtAssertPtrScript.sml` (the JNZ edge, the assert fragment).

## Domain Constraints

- Statements frozen: the target, and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrExitCasesScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file: no edits to bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, the toolkit theories, ptrSafeRun, bodySim, exprSim*, stmtSim*, stmtAbortPtr, stmtAssertPtr, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- About 140 theories of this tree have their proofs admitted locally (cheated in the working tree, hidden from git). Those inherited admissions are expected: CHEAT warnings that come from them are fine. Your own files and the target's proof must contain no `cheat`. The S1 lemmas you use may be among the admitted ones; use them anyway. Some stmtSimReason* theories have `raise Fail` tag gates that can fail under admitted ancestors; read the unadmitted copies in `alan-ref/s1/` instead of depending on those gates.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix.
- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Piece theory | `lowering/bodyPtrExitCasesScript.sml` | The frozen target, and the proved sibling cases (bare/unreachable raise and assert, returns) |
| This piece's ptr helpers | `lowering/stmtAbortPtrScript.sml`, `lowering/stmtAssertPtrScript.sml` | `ptr_inst_ok_abort_zero`, `emit_abort_zero_path_ptr`, `compile_raise_frag_ptr`, `assert_jnz_zero_path_ptr`, `compile_assert_frag_ptr` |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_stmt_ptr_ok`, `body_expr_ptr_ok` |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `stmt_frag_ptr`, `expr_sim_ptr`, `expr_vv_sim_ptr`, `frame_ret_ok_ptr`, `ghost_inv`, `ghost_kept`, `ptr_val_ok`, `ptr_vv_ok`, `ptr_mem_ok` (bound `val_store_size`), `stor_taint_ok`, `stmt_exit_ptr` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr*`, `gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, aborts |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok`, `access_ok`, `taint_ok`, `out_prov`, `out_taint`, `about_to_revert` |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/typedCopy*PtrScript.sml` (esp. `typedCopyBytesRobustPtr`), `lowering/wordCopyRobustPtrScript.sml`, `lowering/batchCopyRobustPtrScript.sml`, `lowering/robustCopyTransportPtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/typedCopyLoop*PtrScript.sml`, `lowering/allocationPtrScript.sml` | Per-instruction pointer facts (copies, stores, word-copy loops, ALLOCA buffers, ghost transport), stated over the fixed-run `frag_exec_ptr` |
| Revert encoder | `lowering/defs/stmtLoweringScript.sml` (~lines 140-190) | The assert/raise-with-reason lowering: ALLOCA buffers, `unwrap_value`, MLOAD length, MCOPY, MSTORE, REVERT |
| Unwrap / buffers | `lowering/defs/exprLoweringScript.sml` (`unwrap_value`), `lowering/defs/contextScript.sml` (`compile_alloc_buffer`, `compile_word_copy_loop`) | How a located reason becomes a memory buffer |
| S1 proofs (unadmitted copies) | `alan-ref/s1/*.sml.txt` | S1's proofs of the case and the four reason fragments (stmtSimReason, stmtSimReasonExpr, stmtSimReasonStorage(Path), stmtSimReasonCode, stmtSimRaise, bodySimStmtCases). Read these, not the copies under `lowering/`, which are admitted locally |
| Memory twin | `lowering/stmtRaiseMemoryScript.sml` | The bare raise ported to another checked path (no reason twin exists) |
| Assert in S1 | `alan-ref/s1/stmtSimAssertScript.sml.txt`, `alan-ref/s1/stmtSimAssertPropsScript.sml.txt` | S1's assert fragments, `assert_success_post`, `eval_assert_bind` |
| Value sizes | `lowering/exprSimPropsScript.sml` | `val_store_size`, `val_store_size_le`; `val_footprint_le_store_size` in bodyPtrDefs |

## Notes

- REVERT is an Abort, not a Halt: `ptr_inst_ok`'s halt clause (`ret_taint`) is vacuous for it, and `taint_ok`'s memory-read clause is lifted by `about_to_revert`.
- The encoder's buffers are all ALLOCAs, so `out_prov` gives each a G site, and ADD-derived addresses keep it.
- The encoder's first MCOPY copies `32 + ceil32(len)` bytes from the reason; `ptr_mem_ok`'s bound `val_store_size` equals that for strings.
- The reason's length word feeds ADD, so it must be untainted. For a memory reason that follows from `ghost_inv`'s `val_in_memory`. For a storage or transient reason, `ptr_vv_ok` of the located value says every `(k,b)` of `t_stor`/`t_trans` within its slots is `dead_bytes` of its type at that offset, which makes the head slot untainted.

## Your own helper theories (added 2026-11-06)

The theory files listed in `OWNED_FILES.txt` (at the project root) were written by earlier runs on this task. They are yours: you may edit, restate, split or delete any theorem in them, and repair their proofs, notwithstanding any "do not edit existing theories" rule above. That rule applies only to theories not in that list. Some of them predate the tip merge (word values now carry no provenance: `ptr_val_ok` at a word type includes `op_prov G op = NONE`) and need proof repairs.
