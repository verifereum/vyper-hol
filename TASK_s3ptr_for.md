# TASK: pointer-safe For statement case

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyPtrCtrlCasesScript.sml

## Theorem Statement (FROZEN)

`body_for_case_ptr` in `lowering/bodyPtrCtrlCasesScript.sml`:

```sml
Theorem body_for_case_ptr:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ptr_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ptr_ok cx it) ==>
    body_stmt_ptr_ok cx (For id typ it n body)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrCtrlCasesTheory` passes, with `body_for_case_ptr` proved with no `cheat` in its proof or in any theory you add (CHEAT warnings inherited from the locally admitted ancestors are expected; see Domain Constraints). Other theorems of the target file that are still `cheat` are not yours: leave them.
2. No duplicate lemmas: search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrCtrlCasesTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation: `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per statement form. Each case is the twin of S1's case of the same name, with `stmt_frag_ptr` (a counted path `gas_path_ptr` on which every edge passes `ptr_safe_step`, with the ghost provenance `G` and taint `tn` threaded along) in place of S1's `stmt_frag`. The post of `stmt_frag_ptr` is S1's `stmt_post` (minus the alloca conjunct) plus `ghost_inv` at the end and the ghost frame on variables older than `sa`. So the simulation half replays S1's proof; the new work is the ghost and the per-edge check.

S1's proof: `body_for_case` in `alan-ref/s1/bodySimDeclCasesScript.sml.txt` (split into a literal range, a dynamic range and an array iterator: `body_for_range_lit`, `body_for_range`, `body_for_array`, `body_for_other`), over the loop machinery in `alan-ref/s1/stmtSimFor*Script.sml.txt` and `alan-ref/s1/stmtSimForcedScript.sml.txt` (the loop's iteration, rounds and frame lemmas). There is no memory twin of the For case yet. The pointer twins of that machinery don't exist: building the ones the cases need, as reusable lemmas in leaf theories, is part of this task.

## Domain Constraints

- Statements frozen: the target and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrCtrlCasesScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file: no edits to bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, the toolkit theories, ptrSafeRun, bodySim, exprSim*, stmtSim*, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- About 140 theories of this tree have their proofs admitted locally (cheated in the working tree, hidden from git). Those inherited admissions are expected: CHEAT warnings that come from them are fine. Your own files and the target's proof must contain no `cheat`. The S1 lemmas you use may be among the admitted ones; use them anyway.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix.

- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Piece theory | `lowering/bodyPtrCtrlCasesScript.sml` | The frozen target; the other cases of the piece are worked on elsewhere, leave them as they are |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_*_ptr_ok`, the induction's predicates |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `stmt_frag_ptr`, `expr_sim_ptr`, `expr_vv_sim_ptr`, `frame_ret_ok_ptr`, `ghost_inv`, `ghost_kept`, `ptr_val_ok`, `stmt_exit_ptr` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then`, `gas_path_ptr_erase` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr`, `_bind_normal`, `_bind_exception`, `_finally`, `gas_outcome_ptr_bind`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, aborts |
| Path to run | `lowering/gasPathPtrExecScript.sml` | `gas_path_ptr_exec`; see its local `jump_entry_ghost` for the ghost at a PHI-free block entry |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok`, `access_ok`, `taint_ok`, `ghost_step`, `entry_prov`, `entry_taint_vars` |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/typedCopy*PtrScript.sml`, `lowering/wordCopyRobustPtrScript.sml`, `lowering/robustCopyTransportPtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/ghostPcTransportPtrScript.sml`, `lowering/typedCopyLoop*PtrScript.sml` | Per-instruction pointer facts (access_ok/taint_ok of copies, stores, loop headers and back-edges, ghost transport), stated over the fixed-run `frag_exec_ptr` |
| S1 proofs (unadmitted copies) | `alan-ref/s1/*.sml.txt` | The S1 (non-pointer) proofs of the same case and their lemmas. Read these, not the copies under `lowering/`, which are admitted locally (see Domain Constraints) |
| Ptr helpers already written for this piece | `alan-ref/piece/*.sml.txt` | Sibling work on the same piece: `emit_jump_zero_path_ptr` (a JMP edge keeping the ghost), `ghost_inv_jump_to`, `stmt_frag_cons_env_ptr`, `compile_expr_stmt_frag_ok_ptr`. Not in this tree: copy what you need into your own leaf theory under a different name, or re-derive it |
| Memory twin (a sibling safety proof of the same shapes) | `lowering/stmtIfMemoryScript.sml`, `lowering/bodyIfMemoryScript.sml`, `lowering/stmtSimSeqMemScript.sml`, `lowering/stmtMemoryScript.sml`, `lowering/stmtSimJumpMemScript.sml`, `lowering/stmtSimIfPropsScript.sml` (the `*_mem` lemmas) | How the S1 shapes were ported to another counted, checked path (`gas_path_mem`); the ptr port follows the same pattern with the ghost added |
| Lowering | `lowering/defs/stmtLoweringScript.sml` | `compile_stmt`, `stmt_env`, `stmts_env` |

## Notes

- The lowered loop (`compile_stmt` For in `lowering/defs/stmtLoweringScript.sml`) uses ASSIGN counters and no PHIs, so block entries keep the ghost.
- The loop variable's slot is allocated once before the loop; each iteration's element store re-establishes `ghost_inv` for it.
- A dynamic array's length word, read by MLOAD for the bound, is untainted because `ghost_inv`'s `val_in_memory` holds for every memory agreeing outside `tn.t_mem`, and that fixes the length bytes. `ghost_kept` excludes dynamic-array length words from its taint frame, so get that fact from `ghost_inv`, not `ghost_kept`.
- `typedCopyLoop*PtrScript.sml` (loop header test, back-edge, address arithmetic) are pointer facts for a copy loop of the same counter-and-JNZ shape.

## Your own helper theories (added 2026-11-06)

The theory files listed in `OWNED_FILES.txt` (at the project root) were written by earlier runs on this task. They are yours: you may edit, restate, split or delete any theorem in them, and repair their proofs, notwithstanding any "do not edit existing theories" rule above. That rule applies only to theories not in that list. Some of them predate the tip merge (word values now carry no provenance: `ptr_val_ok` at a word type includes `op_prov G op = NONE`) and need proof repairs.
