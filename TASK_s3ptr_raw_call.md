# TASK: pointer-safe raw_call expression case

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyPtrCallCasesScript.sml

## Theorem Statement (FROZEN)

`body_raw_call_case_ptr` in `lowering/bodyPtrCallCasesScript.sml`:

```sml
Theorem body_raw_call_case_ptr:
  !cx ty flags es v18.
    body_exprs_ptr_ok cx es ==>
    body_expr_ptr_ok cx (Call ty (RawCallTarget flags) es v18)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrCallCasesTheory` passes, with `body_raw_call_case_ptr` proved with no `cheat` in its proof or in any theory you add (CHEAT warnings inherited from the locally admitted ancestors are expected; see Domain Constraints). Other theorems of the target file that are still `cheat` are not yours: leave them.
2. No duplicate lemmas: search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrCallCasesTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation: `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per expression and statement form. Each case is the twin of S1's case of the same name, with `expr_sim_ptr` / `expr_vv_sim_ptr` (a counted path `gas_path_ptr` on which every edge passes `ptr_safe_step`, with the ghost provenance `G` and taint `tn` threaded along) in place of S1's `expr_sim` / `expr_vv_sim`. Their posts are S1's posts plus `ghost_inv`, `ptr_val_ok` / `ptr_vv_ok`, `ghost_kept`, and `ptr_buf_ok` for memory values (the value's site covers `type_memory_bytes` of its lowered type, not just its footprint). So the simulation half replays S1's proof; the new work is the ghost and the per-edge check.

`raw_call(to, data, [value=], [gas=], [max_outsize=], [is_static_call=], [revert_on_failure=])` lowers (`compile_call ... (RawCallTarget rcf)` in `lowering/defs/exprLoweringScript.sml`) to: the address with `lower_value`; the data (a dynamic `Bytes` value in memory, `well_typed_expr` requires `BytesT (Dynamic n)`) with `lower_value`, then `MLOAD` of its length and `ADD data 32`; the `value=`/`gas=` keyword operands in source order (`compile_ext_call_kwargs`); `GAS` without `gas=`; the output buffer (`compile_raw_call_outbuf`, an ALLOCA); and the call (`compile_raw_call_finish`, in `lowering/defs/builtinSystemScript.sml`). Delegate raw_calls hold vacuously: `expr_body_pre` excludes them (`~expr_has_evm_run`, `expr_evm_run_root`). In oracle mode a regular/static raw_call takes the same outcome as the lowered CALL/STATICCALL (`extCallOracleStep`'s `exec_ext_call_oracle_step`).

S1's proof: S1's own proof of this case is on S1's branch, written but not yet built there: `alan-ref/s1/exprSimRawCallScript.sml.txt` (`compile_raw_call_case`, about 3700 lines), with `alan-ref/s1/exprSimCallRawCallScript.sml.txt`, `alan-ref/s1/bodySimCallRawCallScript.sml.txt` (`raw_call_body_expr_ok`) and `alan-ref/s1/exprSimAccountsScript.sml.txt`. None of it is in this tree: the simulation half (the S1 post inside `expr_sim_ptr`/`expr_vv_sim_ptr`) has to be proved here too. Port what you need into your own leaf theories under new names; lemma statements on S1's branch may rely on S1-branch changes, so check each against this tree's definitions. The send case of this file is being proved in parallel (`TASK_s3ptr_send.md`): it needs the same operand-list composition and a pointer-checked CALL step.

Pointer facts a statement check found (not built): the data value's site covers `[data, data + 32 + 32 * ceil(len/32))` by `ptr_mem_ok`'s `val_store_size` bound, so the length MLOAD and the CALL's input read are in it; the output buffer is an ALLOCA and `ADD out_val 32` keeps its site (`first_prov`); the CALL's return region and RETURNDATACOPY leave the written bytes untainted (`step_writes`, `mem_taint`); the failure path (RETURNDATACOPY then REVERT) is a revert-forwarding pair, exempt from `access_ok`; after an adopted outcome `adopt_reset` clears `t_stor`/`t_trans`, otherwise storage is unchanged.

## Domain Constraints

- Statements frozen: the target and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrCallCasesScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file: no edits to bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, the toolkit theories, ptrSafeRun, ptrDiscipline, bodySim, exprSim*, stmtSim*, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- About 140 theories of this tree have their proofs admitted locally (cheated in the working tree, hidden from git). Those inherited admissions are expected: CHEAT warnings that come from them are fine. Your own files and the target's proof must contain no `cheat`. The S1 lemmas you use may be among the admitted ones; use them anyway.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix.
- The send case of this file needs the same operand-list composition (`body_exprs_ptr_ok` of word operands lowered left to right with `lower_value`) and a pointer-checked CALL step. State those helpers generally (any list of word operands; any CALL whose memory regions lie in sites) so the sibling cases can reuse them.
- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Piece theory | `lowering/bodyPtrCallCasesScript.sml` | The frozen target; the other cases are worked on elsewhere, leave them |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_*_ptr_ok`, the induction's predicates |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `expr_sim_ptr`, `expr_vv_sim_ptr`, `ghost_inv`, `ghost_kept`, `ptr_val_ok`, `ptr_vv_ok`, `ptr_buf_ok`, `cx_dead`, `stor_taint_ok` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then`, `gas_path_ptr_erase` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr*`, `gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, `gas_path_ptr_abort` |
| Path to run | `lowering/gasPathPtrExecScript.sml` | `gas_path_ptr_exec` |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok` (its request clause for CALL), `access_ok`, `taint_ok`, `step_taint`, `ghost_step` |
| Proved ptr cases to imitate | `lowering/stmtAbortPtrScript.sml`, `lowering/stmtAssertPtrScript.sml`, `lowering/stmtFragPtrScript.sml`, `lowering/bodyPtrExitCasesScript.sml`, `lowering/bodyPtrCtrlCasesScript.sml` | `ptr_inst_ok_abort_zero`, `emit_abort_zero_path_ptr`, `assert_jnz_zero_path_ptr`, `compile_assert_frag_ptr` (an ASSERT edge), `ghost_inv_jump_to`, `not_fresh_at_mono`, cons/env helpers |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/ghostPcTransportPtrScript.sml`, `lowering/returnMetadataPtrScript.sml` | Per-instruction pointer facts and ghost transport, stated over the fixed-run `frag_exec_ptr` |
| S1 raw_call proof | `alan-ref/s1/exprSimRawCallScript.sml.txt`, `alan-ref/s1/exprSimCallRawCallScript.sml.txt`, `alan-ref/s1/bodySimCallRawCallScript.sml.txt`, `alan-ref/s1/exprSimAccountsScript.sml.txt` | S1 branch copies, unbuilt there |
| S1 send proof (a smaller CALL case) | `alan-ref/s1/exprSimSendScript.sml.txt` | S1 branch copy |
| Unadmitted source at this tree's commit | `alan-ref/base/extCallOracleStepScript.sml.txt`, `alan-ref/base/exprSimSendScript.sml.txt` | The locally admitted copies' proofs |
| Oracle CALL step | `lowering/extCallOracleStepScript.sml` | `exec_ext_call_oracle_step`, `venom_call_request_source` |
| Lowering | `lowering/defs/exprLoweringScript.sml`, `lowering/defs/builtinSystemScript.sml` | `compile_call` (RawCallTarget), `compile_ext_call_kwargs`, `compile_raw_call_outbuf`, `compile_raw_call_finish` |

## Notes

- The CALL changes storage and transient storage (the oracle outcome's accounts). `ghost_inv`'s `stor_taint_ok` is stated over the current storage's dead bytes; see `step_taint`'s `adopted`/`adopt_reset`.
- With `max_outsize > 0` the result is a `LocatedValue` in memory (a fresh tuple buffer, or the out buffer), so `ptr_vv_ok` needs `ptr_mem_ok` of it: only the bytes the value occupies must be untainted; the padding past the returned data may keep the fresh ALLOCA's taint.
- The data operand's bytes must stay intact and untainted while the keyword operands are evaluated: the operands' `ghost_kept` and S1's memory frame.
- `ptr_buf_ok` of the memory result: its pointer's site (in `G`) must cover `type_memory_bytes cenv (lowered_value_type cenv e)` from the pointer on, the whole buffer of the lowered `Bytes[max_outsize]` (or tuple) type, not only the returned bytes.

## Your own helper theories (added 2026-11-06)

The theory files listed in `OWNED_FILES.txt` (at the project root) were written by earlier runs on this task. They are yours: you may edit, restate, split or delete any theorem in them, and repair their proofs, notwithstanding any "do not edit existing theories" rule above. That rule applies only to theories not in that list. Some of them predate the tip merge (word values now carry no provenance: `ptr_val_ok` at a word type includes `op_prov G op = NONE`) and need proof repairs.
