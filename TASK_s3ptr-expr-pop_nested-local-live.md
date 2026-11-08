# TASK: pointer-safe pop on a live nested local target

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
Location: lowering/bodyPtrPopSeamNestedLocalLiveScript.sml

## Theorem Statement (FROZEN)

`pop_nested_local_live_vv_ptr` in `lowering/bodyPtrPopSeamNestedLocalLiveScript.sml`:

```sml
Theorem pop_nested_local_live_vv_ptr:
  !tops ctx cenv cx env ann bt id ty es d PG func.
    body_inv tops ctx cenv cx /\
    body_base_target_ptr_ok cx bt /\
    (!x. bt <> NameTarget x) /\
    target_root bt = NameTarget id /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    (!s path t entry err.
       eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
       lookup_scopes id t.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INR err ==>
       read_popped entry.type path entry.popped = NONE) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrPopSeamNestedLocalLiveTheory` passes, with `pop_nested_local_live_vv_ptr` proved with no `cheat` in its proof, in `lowering/bodyPtrPopSeamNestedLocalLiveScript.sml`, or in any theory you add (CHEAT warnings inherited from the locally admitted ancestors are expected; see Domain Constraints).
2. No duplicate lemmas: search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrPopSeamNestedLocalLiveTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation: `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per expression and statement form. `bodyPtrExprCases` proves its compound-expression cases from one leaf theory per case (builtins: one per family); this task is one of those leaves. `body_expr_ptr_ok cx e` says: for every frame meeting `body_inv` and `expr_body_pre`, both `expr_sim_ptr` (the lowered value, `lower_value`) and `expr_vv_sim_ptr` (the value-or-place, `compile_expr`) hold. Each is S1's `expr_sim`/`expr_vv_sim` (`lowering/exprSimDefsScript.sml`) with a counted path `gas_path_ptr` on which every edge passes `ptr_safe_step`, with the ghost provenance `G` and taint `tn` threaded along, and with the post extended by `ghost_inv`, `ptr_val_ok`/`ptr_vv_ok`, `ptr_buf_ok` (a memory value's pointer covers the whole buffer of its lowered type, `type_memory_bytes cenv (lowered_value_type cenv e)`) and `ghost_kept`. So the simulation half replays S1's proof of the same case; the new work is the ghost and the per-edge pointer check.

S1 proves its case from the operands' judgments through a shared case lemma (`exprSimHyps`' `expr_sim_case`/`expr_vv_case`/`exprs_case`, instantiated by `bodySimExprCases`' `body_expr_ok_case`). The pointer twins of that machinery mostly don't exist yet: building the ones this case needs, as reusable lemmas in leaf theories, is part of this task. `lowering/exprPtrUnwrapScript.sml` has `expr_sim_ptr_of_vv` (an `expr_vv_sim_ptr` gives the `expr_sim_ptr`; proved by a sibling task, use it as is) and `expr_vv_sim_ptr_stack` (proved: an `expr_sim_ptr` gives the `expr_vv_sim_ptr` when `compile_expr` leaves a stack value).

S1's proof: `body_pop_case`, `body_pop_nested_case` (`bodySimExprCases`) over `compile_pop_name_case`, `pop_nested_sim`, `body_pop_nested_target_frag` (`exprSimPlaces`, `exprSimPop`, `exprSimPopNested`, `exprSimPopStorage` in `alan-ref/s1-places-pop/`). Memory twin stubs: `alan-ref/mem/bodyMemPopNameScript.sml.txt`, `bodyMemPopNestedScript.sml.txt`.

This task is one seam of `pop_expr_ptr_ok`: pop on a nested target rooted at a local (`x[i].pop()`, `x.a[i].pop()`, ...) whose place stays live, as S1's `pop_nested_local_live_case` (`alan-ref/s1-places-pop/exprSimPopNestedLocalScript.sml.txt`) has it; the target's index judgments come from `body_base_target_ptr_ok` (`body_expr_ptr_ok` of each index, when the inner target evaluates) instead of S1's `pop_target_frag`. `bodyPtrPopCompose` proves the parent from this seam, the bare-local seam (`bodyPtrPopSeamLocalRoot`), a held residual for the popped-history case (`bodyPtrPopResidualNestedLocalPopped`), and proved lemmas for top-level names and nested module-rooted targets.

## Domain Constraints

- Statements frozen: the target and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrPopSeamNestedLocalLiveScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file: no edits to bodyPtrDefs, bodyPtrPreds, bodyPtrExprCases, exprPtrUnwrap, fragGasPathPtr, the toolkit theories, ptrSafeRun, bodySim, exprSim*, stmtSim*, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- About 140 theories of this tree have their proofs admitted locally (cheated in the working tree, hidden from git). Those inherited admissions are expected: CHEAT warnings that come from them are fine. The exported theorems of those admitted ancestor theories, and of this seam's sibling seam and residual theories, are inherited admissions you may use. Your own files and the target's proof must contain no `cheat`. The S1 lemmas you use may be among the admitted ones; use them anyway.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix, and prefix them with `bodyPtrPopNestedLive` so they don't clash with sibling tasks' theories.
- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Target | `lowering/bodyPtrPopSeamNestedLocalLiveScript.sml` | The frozen target |
| Parent theorem | `lowering/bodyPtrPopScript.sml`, `lowering/bodyPtrPopComposeScript.sml` | `pop_expr_ptr_ok`, proved from this seam, its sibling seam and one held residual |
| Earlier runs' helpers | `lowering/bodyPtrPop*Script.sml` (committed on this branch) | Proved pieces of the Pop case: counted memory header load, length guard, header store, interior pointer, nested target compilation and index cuts |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_expr_ptr_ok`, `body_exprs_ptr_ok`, `body_base_target_ptr_ok` |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `expr_sim_ptr`, `expr_vv_sim_ptr`, `ghost_inv`, `ghost_kept`, `ptr_val_ok`, `ptr_mem_ok`, `ptr_vv_ok`, `ptr_buf_ok`, `stor_taint_ok`, `cx_dead` |
| Value/place glue | `lowering/exprPtrUnwrapScript.sml` | `expr_sim_ptr_of_vv`, `expr_vv_sim_ptr_stack`, `expr_stack_outcome_ptr` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then`, `gas_path_ptr_erase` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr`, `_bind_normal`, `_bind_exception`, `_finally`, `gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, aborts |
| Path to run | `lowering/gasPathPtrExecScript.sml` | `gas_path_ptr_exec`, `jump_entry_ghost` |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok`, `access_ok`, `taint_ok`, `ghost_step`, `entry_prov`, `entry_taint_vars` |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/typedCopy*PtrScript.sml`, `lowering/wordCopyRobustPtrScript.sml`, `lowering/batchCopyRobustPtrScript.sml`, `lowering/robustCopyTransportPtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/ghostPcTransportPtrScript.sml`, `lowering/liveArrayTransportPtrScript.sml`, `lowering/ptrCoverageScript.sml`, `lowering/allocationPtrScript.sml`, `lowering/structChildPtrScript.sml` | Per-instruction pointer facts (MLOAD/MSTORE/MCOPY/ALLOCA access_ok and taint_ok, copies, ghost transport), stated over the fixed-run `frag_exec_ptr`: use them for the per-instruction facts and rebuild the counted paths with the combinators above |
| Statement-level ptr proofs (examples of the port) | `lowering/stmtFragPtrScript.sml`, `lowering/stmtAssertPtrScript.sml`, `lowering/stmtAbortPtrScript.sml` | How an `expr_sim_ptr` is consumed and a counted ptr path is built (JNZ edge, aborts, `ghost_inv_jump_to`, `not_fresh_at_mono`) |
| Unadmitted base proofs | `alan-ref/base/*.sml.txt` | The original proofs of the ~140 theories admitted in this tree (S1's exprSim*, bodySim*, stmtSim*, ...). Read these, not the copies under `lowering/` |
| S1 branches (newer S1 proofs) | `alan-ref/s1-ops-widened-expr/`, `alan-ref/s1-builtins-aggregates/`, `alan-ref/s1-places-pop/` | Files changed on the S1 branches that are closing S1's remaining admissions (IfExp/operators/widened calls; builtins/aggregates/abi; places/pop). Where a file is here, it supersedes the base copy |
| Memory twin | `lowering/*Memory*Script.sml`, `lowering/*Mem*Script.sml`, `alan-ref/mem/*.sml.txt` | A sibling safety proof (`gas_path_mem`) of the same expression shapes; `alan-ref/mem` holds its branch's newer files. The ptr port follows the same pattern with the ghost added |
| Lowering | `lowering/defs/exprLoweringScript.sml` (and `rg 'compile_expr_def\|unwrap_value_def\|lower_value_def'`) | `compile_expr`, `lower_value`, `unwrap_value` |

## Helper theories from earlier runs

The `lowering/bodyPtrPop*Script.sml` theories committed on this branch were written by earlier runs on the parent Pop task, and are proved. Use them, and you may add theorems to them, notwithstanding the "do not edit existing theories" rule above; don't change or delete their existing theorems (the parent's proof and a sibling seam run use them), and don't touch `lowering/bodyPtrPopScript.sml`, `lowering/bodyPtrPopComposeScript.sml`, the sibling seam, or the residual theory `lowering/bodyPtrPopResidualNestedLocalPoppedScript.sml`.
