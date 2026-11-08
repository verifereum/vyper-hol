# TASK: pointer-safe target place from the base place

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
Location: lowering/bodyPtrPopSeamTargetFragScript.sml

## Theorem Statement (FROZEN)

`pop_target_frag_ptr_of_sim` in `lowering/bodyPtrPopSeamTargetFragScript.sml`:

```sml
Theorem pop_target_frag_ptr_of_sim:
  !d ctx PG func cenv cx env bt es.
    target_sim_ptr d ctx PG func cenv cx env bt es ==>
    pop_target_frag_ptr d ctx PG func cenv cx env bt es
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrPopSeamTargetFragTheory` passes, with `pop_target_frag_ptr_of_sim` proved with no `cheat` in its proof, in `lowering/bodyPtrPopSeamTargetFragScript.sml`, or in any theory you add (CHEAT warnings inherited from ancestor theories are expected; see Domain Constraints).
2. No duplicate lemmas: search before adding one; each helper exists once, in its most general form, in a new leaf theory under `lowering/`.

**If the theorem is false as stated:** give a concrete counterexample, state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
holbuild -j4 build bodyPtrPopSeamTargetFragTheory
```

## Background

The S3 pointer-safety proof of the Vyper-to-Venom lowering is a pointer twin of the S1 body simulation: `bodySimPtrMain`'s `body_sim_ptr_mutual` runs the body induction over the predicates of `bodyPtrPreds`, one case lemma per expression and statement form. `bodyPtrExprCases` proves its compound-expression cases from one leaf theory per case; `pop_expr_ptr_ok` (`lowering/bodyPtrPopScript.sml`) is the Pop case. `body_expr_ptr_ok cx e` says: for every frame meeting `body_inv` and `expr_body_pre`, both `expr_sim_ptr` (the lowered value, `lower_value`) and `expr_vv_sim_ptr` (the value-or-place, `compile_expr`) hold (plus a clause for array literals' elements). Each is S1's `expr_sim`/`expr_vv_sim` (`lowering/exprSimDefsScript.sml`) with a counted path `gas_path_ptr` on which every edge passes `ptr_safe_step`, with the ghost provenance `G` and taint `tn` threaded along, and with the post extended by `ghost_inv`, `ptr_val_ok`/`ptr_vv_ok`, `ptr_buf_ok` and `ghost_kept`. The runtime judgments assume `~cenv.ce_is_ctor`. So the simulation half replays S1's proof of the same case; the new work is the ghost and the per-edge pointer check. On this base, `vv_post` has `post_value_type`, `vv_own` and `vv_storage_live`; `ptr_vv_ok`'s `LocatedValue` clause asks `op_prov G p.ptr_operand = NONE` for `LocCode`; for a pop, `post_value_type cenv (Pop ann bt) = ann` and `expr_has_effect (Pop ann bt)`.

`bodyPtrPopCompose` proves `pop_expr_ptr_ok` by the target's root: a top-level name (`bodyPtrPopRootCase`'s `body_pop_root_ptr_ok`, proved); a bare local (seam `bodyPtrPopSeamLocalRoot`); an immutable or constant root (proved: it does not type at runtime); a storage or transient root with pure indices (seam `bodyPtrPopSeamStoragePure`) or not (held residual `bodyPtrPopResidualStorageEffectful`); a local root whose indices leave the base's path live (`local_target_live`: seam `bodyPtrPopSeamNestedLocalLive`) or not (held residual `bodyPtrPopResidualNestedLocalPopped`). The nested cases take the target's fragment judgment `pop_target_frag_ptr`, which the seams `bodyPtrPopSeamTargetSim` (`target_sim_ptr` by induction on the target) and `bodyPtrPopSeamTargetFrag` (`target_sim_ptr` to `pop_target_frag_ptr`) give. `lowering/bodyPtrPopTargetDefsScript.sml` defines `target_ptr_ok`, `target_sim_ptr`, `pop_target_frag_ptr` and `local_target_live`, the pointer twins of S1's `targetPlaceSimDefs.target_sim` and `exprSimPopNestedBase.pop_target_frag`.

This task is one seam of `pop_expr_ptr_ok`: the pointer twin of S1's `pop_target_frag_of_sim` (`exprSimPopNestedBase`), which is `targetPlaceSimCases`' `target_place_sim`: `eval_target_place cx bt` is `bind (eval_base_place cx bt) get_place`, `get_place` runs no Venom code, and `gas_admissible`'s `target_place_res_ok` rules out a non-place result.

## Domain Constraints

- Statements frozen: the target and every theorem outside the files you add. Edit only the target's `Proof ... QED` in `lowering/bodyPtrPopSeamTargetFragScript.sml` (and its `Ancestors` line), and add new leaf theories next to it in `lowering/`. Do not edit any existing theory other than the target file: no edits to bodyPtrDefs, bodyPtrPreds, bodyPtrPopTargetDefs, bodyPtrExprCases, exprPtrUnwrap, fragGasPathPtr, the toolkit theories, ptrSafeRun, bodySim, exprSim*, stmtSim*, targetPlace*, semantics or defs. If the proof needs a change to one of them, or a statement is false, stop and report the exact change and a counterexample.
- This tree has no locally admitted theories: everything is committed. Some ancestor theories still hold admitted (`cheat`) theorems: S1's open cases (for instance `targetSubscriptCase`'s `target_subscript_case`, `exprSimPopNestedStorageEffectful`'s `pop_nested_storage_effectful_dead_case`, `exprSimPopNestedLocalPopped`'s `pop_nested_local_popped_case`), this task's sibling seams (`bodyPtrPopSeam*`) and held residuals (`bodyPtrPopResidual*`), and the other open S3 cases. CHEAT warnings inherited from those are expected. Their exported theorems are inherited admissions you may use (the sibling seams' included). Your own files and the target's proof must contain no `cheat`.
- No `supported_*` or `occurs*` unpacking (opcode-absence arguments from `supported_program`, `supported_effect_expr`, `occurs5` and the like): the case must be proved by running the code, not by showing the program can't contain it.
- holbuild's 2.5 s per-step tactic timeout stays: never raise it. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. No `let` in statements. 50 lines per proof at most: split into helper lemmas. Unfolding `step_inst_base_def` is slow: use `step_inst_base_opcode_eqs` with `mk_inst_def`.
- New definitions are discouraged; if you add one, say why in a comment.
- Name new theories without a `Lib` suffix, and prefix them with `bodyPtrPopTargetFrag` so they don't clash with sibling tasks' theories.
- Before pushing a helper into a big proof, build it alone.

## Available Resources

All paths are relative to this directory (the vyper-hol project root).

| Resource | Location | Description |
|----------|----------|-------------|
| Target | `lowering/bodyPtrPopSeamTargetFragScript.sml` | The frozen target |
| Parent theorem | `lowering/bodyPtrPopScript.sml`, `lowering/bodyPtrPopComposeScript.sml` | `pop_expr_ptr_ok`, proved from this seam, its sibling seams and two held residuals |
| Target judgments | `lowering/bodyPtrPopTargetDefsScript.sml` | `target_ptr_ok`, `target_sim_ptr`, `pop_target_frag_ptr`, `local_target_live` |
| Proved Pop helpers | `lowering/bodyPtrPop*Script.sml` (the non-seam, non-residual ones) | Root storage pop (`bodyPtrPopRootCase`, `bodyPtrPopRootOutcome`, `bodyPtrPopRoot*`, `bodyPtrPop*Transfer`, `bodyPtrPopZeroAbort`, `bodyPtrPopReturned`), memory pop suffix pieces (`bodyPtrPopMemoryHeader`, `bodyPtrPopLengthGuard`, `bodyPtrPopMemoryStore`, `bodyPtrPopLengthStore`, `bodyPtrPopInteriorPointer`, `bodyPtrPopLiveElement`), target cuts (`bodyPtrPopTargetFactor`) |
| Predicates | `lowering/bodyPtrPredsScript.sml` | `body_expr_ptr_ok`, `body_exprs_ptr_ok`, `body_base_target_ptr_ok` |
| Judgments | `lowering/bodyPtrDefsScript.sml` | `expr_sim_ptr`, `expr_vv_sim_ptr`, `ghost_inv`, `ghost_kept`, `ptr_covers`, `ptr_val_ok`, `ptr_mem_ok`, `ptr_vv_ok`, `ptr_buf_ok`, `stor_taint_ok`, `cx_dead` |
| Value/place glue | `lowering/exprPtrUnwrapScript.sml` | `expr_sim_ptr_of_vv`, `expr_vv_sim_ptr_stack` |
| Counted ptr paths | `lowering/fragGasPathPtrScript.sml` | `gas_path_ptr_edge`, `gas_path_ptr`, `gas_summary_ptr_at`, `gas_outcome_ptr`, `gas_path_ptr_then`, `gas_path_ptr_erase` |
| Composition | `lowering/gasSummaryComposePtrScript.sml` | `gas_marked_exec_ptr`, `_bind_normal`, `_bind_exception`, `_finally`, `gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`, `_erase` |
| Straight-line runs | `lowering/fragGasSeqPtrScript.sml` | `run_inst_seq_gas_path_ptr`, `inst_seq_ptr`, `gas_path_ptr_step`, aborts |
| Ghost and check | `venom/compiler/ptrSafeRunScript.sml`, `venom/compiler/ptrDisciplineScript.sml` | `ptr_safe_step`, `ptr_inst_ok`, `access_ok`, `taint_ok`, `ghost_step`, `out_prov`, `out_taint` |
| Pointer toolkit | `lowering/fragExecPtrScript.sml`, `lowering/typedCopy*PtrScript.sml`, `lowering/representationCleanPtrScript.sml`, `lowering/ghostPcTransportPtrScript.sml`, `lowering/liveArrayTransportPtrScript.sml`, `lowering/ptrCoverageScript.sml`, `lowering/allocationPtrScript.sml`, `lowering/structChildPtrScript.sml`, `lowering/appendStorage*PtrScript.sml`, `lowering/stmtAppendStorage*PtrScript.sml` | Per-instruction pointer facts (MLOAD/MSTORE/SLOAD/SSTORE access_ok and taint_ok, copies, ghost transport) |
| Statement-level ptr proofs (examples) | `lowering/stmtFragPtrScript.sml`, `lowering/stmtAssertPtrScript.sml`, `lowering/stmtAbortPtrScript.sml` | How an `expr_sim_ptr` is consumed and a counted ptr path is built |
| S1 (simulation) | `lowering/exprSimPop*Script.sml`, `lowering/targetPlaceSim*Script.sml`, `lowering/targetSubscriptCaseScript.sml`, `lowering/targetPlaceLiveScript.sml`, `lowering/bodyPopNestedTargetFragScript.sml`, `lowering/popTargetPreScript.sml` | S1's proof of the same shapes |
| Memory twin | `lowering/bodyMemPop*Script.sml` | A sibling safety proof (`gas_path_mem`) of the same pop shapes |
| Lowering | `lowering/defs/exprLoweringScript.sml` (`compile_expr`, `compile_get_target_ptr`, `compile_dynarray_pop`) | The code |

## Helper theories from earlier runs

The proved `lowering/bodyPtrPop*Script.sml` theories (all but `bodyPtrPop`, `bodyPtrPopCompose`, `bodyPtrPopTargetDefs`, the `bodyPtrPopSeam*` seams and the `bodyPtrPopResidual*` residuals) were written by earlier runs on the parent Pop task. Use them, and you may add theorems to them, notwithstanding the "do not edit existing theories" rule above; don't change or delete their existing theorems (the parent's proof and sibling seam runs use them), and don't touch `lowering/bodyPtrPopScript.sml`, `lowering/bodyPtrPopComposeScript.sml`, `lowering/bodyPtrPopTargetDefsScript.sml`, the sibling seams or the residual theories.
