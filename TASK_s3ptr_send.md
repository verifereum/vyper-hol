# TASK: pointer-safe send expression case

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyPtrCallCasesScript.sml

## Theorem Statement (FROZEN)

`body_send_case_ptr` in `lowering/bodyPtrCallCasesScript.sml`:

```sml
Theorem body_send_case_ptr:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Call v12 (Send has_gas) es v13)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrCallCasesTheory` passes, with `body_send_case_ptr` proved with no `cheat` in its proof or in any theory you add (CHEAT warnings inherited from the locally admitted ancestors are expected; see Domain Constraints). Other theorems of the target file that are still `cheat` are not yours: leave them.
2. No duplicate lemmas: search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrCallCasesTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation: `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per expression and statement form. Each case is the twin of S1's case of the same name, with `expr_sim_ptr` / `expr_vv_sim_ptr` (a counted path `gas_path_ptr` on which every edge passes `ptr_safe_step`, with the ghost provenance `G` and taint `tn` threaded along) in place of S1's `expr_sim` / `expr_vv_sim`. Their posts are S1's posts plus `ghost_inv`, `ptr_val_ok` / `ptr_vv_ok`, `ghost_kept`, and `ptr_buf_ok` for memory values (the value's site covers `type_memory_bytes` of its lowered type, not just its footprint). So the simulation half replays S1's proof; the new work is the ghost and the per-edge check.

`send(to, value[, gas=g])` lowers its word operands left to right with `lower_value`, then `CALL [gas; to; value; 0; 0; 0; 0]` (gas `Lit 0w` without `gas=`) and an `ASSERT` of the success word; its value is `StackValue NoneT (Lit 0w)` (`compile_call ... (Send has_gas)` in `lowering/defs/exprLoweringScript.sml`). In oracle mode the CALL takes the same outcome as the source's `eval_send` (`extCallOracleStep`'s `send_call_oracle_step`). The CALL reads and writes no memory (both regions have size 0).

S1's proof: `alan-ref/s1/exprSimSendScript.sml.txt` (`send_expr_sim`, `send_tail_frag`, `compile_send_case`) and `body_send_case` in `alan-ref/s1/bodySimExprCasesScript.sml.txt`. These are from S1's branch, where the S1 lemmas are being ported to the counted form; some lemma statements there may differ from this tree's. The copies of the same theories under `lowering/` are admitted locally (see Domain Constraints); their unadmitted source at this tree's commit is in `alan-ref/base/` (`exprSimSendScript.sml.txt`, `extCallOracleStepScript.sml.txt`). Lemma names and statements you can call are those under `lowering/`.

## Domain Constraints

- Statements frozen: the target and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrCallCasesScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file: no edits to bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, the toolkit theories, ptrSafeRun, ptrDiscipline, bodySim, exprSim*, stmtSim*, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- About 140 theories of this tree have their proofs admitted locally (cheated in the working tree, hidden from git). Those inherited admissions are expected: CHEAT warnings that come from them are fine. Your own files and the target's proof must contain no `cheat`. The S1 lemmas you use may be among the admitted ones; use them anyway.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix.
- Other cases of this file (extcall, raw_call) need the same operand-list composition (`body_exprs_ptr_ok` of word operands lowered left to right with `lower_value`) and a pointer-checked CALL step. State those helpers generally (any list of word operands; any CALL whose memory regions lie in sites) so the sibling cases can reuse them.
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
| S1 send proof | `alan-ref/s1/exprSimSendScript.sml.txt`, `alan-ref/s1/bodySimExprCasesScript.sml.txt` | S1 branch copies (counted form) |
| S1 at this tree's commit | `alan-ref/base/exprSimSendScript.sml.txt`, `alan-ref/base/extCallOracleStepScript.sml.txt` | Unadmitted source of the locally admitted copies |
| Oracle CALL step | `lowering/extCallOracleStepScript.sml` | `send_call_oracle_step`, `exec_ext_call_oracle_step` |
| Lowering | `lowering/defs/exprLoweringScript.sml` | `compile_call` (Send), `lower_value` |

## Notes

- The CALL changes storage and transient storage (the oracle outcome's accounts). `ghost_inv`'s `stor_taint_ok` is stated over the current storage's dead bytes, so check how `step_taint` treats the CALL before relying on it surviving.
- `NoneT` is not a word type; `ptr_mem_ok` of `NoneV` holds because its footprint is 0.
- The result is `StackValue NoneT (Lit 0w)`; check whether `ptr_buf_ok` is vacuous for it (`type_memory_bytes` of its lowered type).
