# TASK: pointer-safe log statement

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyPtrLogCasesScript.sml

## Theorem Statement (FROZEN)

`body_log_case_ptr` in `lowering/bodyPtrLogCasesScript.sml`:

```sml
Theorem body_log_case_ptr:
  !cx id es. body_exprs_ptr_ok cx es ==> body_stmt_ptr_ok cx (Log id es)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrLogCasesTheory` passes, with `body_log_case_ptr` proved with no `cheat` in its proof or in any theory you add. CHEAT warnings inherited from the locally admitted ancestors are expected (see Domain Constraints). `body_append_case_ptr` in the same file is not yours: leave its `cheat` as it is.
2. No duplicate lemmas. Search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrLogCasesTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation. `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per statement form. Each case is the twin of S1's case of the same name, with `stmt_frag_ptr` in place of S1's `stmt_frag` and `expr_sim_ptr` in place of `expr_sim`. `stmt_frag_ptr` concludes `gas_outcome_ptr` over the counted path `gas_path_ptr`, on which every edge passes `ptr_safe_step` (so every instruction passes `ptr_inst_ok` with lo = 0), with the ghost provenance `G` and taint `tn` threaded along. Its post is S1's post plus `ghost_inv` and the ghost frame. So the simulation half replays S1's proof (reuse S1's lemmas); the new work is the ghost and the per-instruction check.

S1's proof is `body_log_case` in `alan-ref/s1/bodySimLogScript.sml.txt`. It reduces to `compile_log_stmt_frag` (`alan-ref/s1/stmtSimLogScript.sml.txt`), which is `compile_log_ready_stmt_frag` (`stmtSimLogCompose`) over the `stmtSimLog*` chain: evaluate the arguments in order (`compile_log_eval_all`), split them (`split_log_ops`), hash bytestring topics (`compile_encode_log_topic`: ADD, MLOAD, SHA3), store the data into a fresh ALLOCA buffer (`compile_log_store_data`), ABI-encode it into a second fresh ALLOCA buffer (`compile_abi_encode_to_buf`), and emit LOG. The lowering is `compile_stmt`'s Log case in `lowering/defs/stmtLoweringScript.sml` (~line 950). Supported events have word or bytestring fields only (`supported_log`, `supported_scalar_type`).

The pointer twins of that chain don't exist yet; building them, as reusable lemmas in leaf theories, is part of this task.

## Domain Constraints

- Statements frozen: the target, and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrLogCasesScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file: no edits to bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, the toolkit theories, ptrSafeRun, ptrDiscipline, bodySim, exprSim*, stmtSim*, stmtFragPtr, stmtAbortPtr, stmtAssertPtr, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- About 140 theories of this tree have their proofs admitted locally (cheated in the working tree, hidden from git). Those inherited admissions are expected: CHEAT warnings that come from them are fine. Your own files and the target's proof must contain no `cheat`. The S1 lemmas you use may be among the admitted ones (all of `stmtSimLog*` and `bodySimLog` are, locally); use them anyway, and read their unadmitted copies in `alan-ref/s1/` to see how they are proved.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix.
- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Piece theory | `lowering/bodyPtrLogCasesScript.sml` | The frozen target |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_stmt_ptr_ok`, `body_exprs_ptr_ok`, `body_expr_ptr_ok` |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `stmt_frag_ptr`, `expr_sim_ptr` (its post includes `ptr_buf_ok`: a memory value's site covers `type_memory_bytes cenv (lowered_value_type cenv e)`), `ghost_inv`, `ghost_kept`, `ptr_val_ok`, `ptr_mem_ok` (bound `val_store_size`), `stor_taint_ok`, `stmt_exit_ptr` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr*`, `gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, aborts |
| Path to run | `lowering/gasPathPtrExecScript.sml` | `gas_path_ptr_exec` |
| Proved statement helpers | `lowering/stmtFragPtrScript.sml`, `lowering/stmtAbortPtrScript.sml`, `lowering/stmtAssertPtrScript.sml`, `lowering/bodyPtrExitCasesScript.sml`, `lowering/bodyPtrCtrlCasesScript.sml` | Cons/env helpers, `ghost_inv_jump_to`, `not_fresh_at_mono`, aborts, worked examples of proved `stmt_frag_ptr` cases |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok`, `access_ok`, `taint_ok`, `out_prov`, `out_taint`, `step_taint`, `mem_taint` (fresh ALLOCA sites start tainted; a write sets its bytes' taint) |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/typedCopy*PtrScript.sml` (esp. `typedCopyBytesRobustPtr`), `lowering/wordCopyRobustPtrScript.sml`, `lowering/batchCopyRobustPtrScript.sml`, `lowering/robustCopyTransportPtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/allocationPtrScript.sml`, `lowering/ghostPcTransportPtrScript.sml` | Per-instruction pointer facts (copies, stores, ALLOCA buffers, ghost transport), stated over the fixed-run `frag_exec_ptr`; rebuild counted paths with the combinators above |
| Lowering | `lowering/defs/stmtLoweringScript.sml` (Log case, `compile_log_*`, `split_log_ops`), `lowering/defs/contextScript.sml` (`compile_encode_log_topic`, `compile_alloc_buffer`, `compile_store_bytestring`), `lowering/defs/abiEncoderScript.sml`, `lowering/abiEncoderBytesCodeScript.sml` | What the code does |
| Allocation bounds | `lowering/defs/allocLimitsScript.sml` (`log_alloc_ok`) | Buffer sizes fit below 2 ** 64 |
| S1 proofs (unadmitted copies) | `alan-ref/s1/*.sml.txt` | `bodySimLog`, `stmtSimLog*` (the whole log chain). Read these, not the copies under `lowering/`, which are admitted locally |

## Notes

- `taint_ok`: tainted memory may be read only by MLOAD/ILOAD/MCOPY/RETURN, and a tainted operand only feeds ASSIGN, a shift, or a store's value. So LOG's read range `[abi_buf, abi_buf + encoded_len)` and SHA3's range must be untainted, and LOG's topics and sizes untainted.
- `ptr_mem_ok` says the value is in memory for every memory agreeing outside `tn.t_mem`, so a bytestring's length word and data bytes are untainted; its padding up to `val_store_size` may be tainted.
- `compile_log_store_data` copies a bytestring arg's whole words into the data buffer, padding taint included; the encoder only MCOPYs `32 + len` bytes out of it (MCOPY may read tainted bytes). The encoder's bytestring case zero-stores the last word before the MCOPY (`abiEncoderBytesCodeScript`), so every byte of the encoded range is written untainted.
- The two buffers are fresh ALLOCAs (`out_prov` gives each a G site; ADD keeps the provenance), so writes into them leave `ghost_kept` and the live locals alone.
- With no data, LOG reads 0 bytes (`Lit 0w; Lit 0w`).
