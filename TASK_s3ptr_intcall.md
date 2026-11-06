# TASK: pointer safety of the internal-call case of the body induction

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (target script lowering/bodyPtrIntCallEqScript.sml)

## Theorem Statement (FROZEN)

In lowering/bodyPtrIntCallEqScript.sml: `body_intcall_eq_ptr`, exactly as
it stands in that file. Its hypotheses are the three induction hypotheses
of the internal-call case `Call v16 (IntCall (src_id_opt,fn)) es v17` of
`evaluate_ind` for the predicates of lowering/bodyPtrPredsScript.sml:
`body_stmts_ptr_ok cxf body'` (the callee's body, at the context
`push_function` makes), `body_exprs_ptr_ok cxd needed_dflts` (the
defaults, at the callee's stack) and `body_results_ptr_ok cx es` (the
arguments). Its conclusion is `body_expr_ptr_ok`'s for that call
(`expr_sim_ptr` and `expr_vv_sim_ptr`), at a call whose annotation is the
callee's declared return type:
`lowered_value_type cenv e = expr_type e`. (The widened calls are held
separately, in bodyPtrIntCallWidened, and bodyPtrIntCallCase combines the
two; neither is your concern.)

The predicates (`body_expr_ptr_ok`, `body_stmts_ptr_ok`, ...) are in
lowering/bodyPtrPredsScript.sml. The judgments `expr_sim_ptr`,
`expr_vv_sim_ptr`, `stmt_frag_ptr`, `frame_ret_ok_ptr`, `stmt_exit_ptr`,
`ghost_inv`, `ghost_kept`, `ptr_val_ok`, `ptr_mem_ok`, `ptr_vv_ok`, `ptr_buf_ok`,
`cx_dead`, `frag_exec_ptr` are in lowering/bodyPtrDefsScript.sml; the
counted paths `gas_path_ptr_edge`, `gas_path_ptr`, `gas_outcome_ptr` in
lowering/fragGasPathPtrScript.sml; the per-step check `ptr_safe_step`,
`ghost_step` (an INVOKE checks the callee's whole run with
`PG := MAP (op_prov G) ops`, `G := FEMPTY`, `tn with t_var := FEMPTY`) in
venom/compiler/ptrSafeRunScript.sml, with `access_ok`, `taint_ok` in
venom/compiler/ptrDisciplineScript.sml.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyPtrIntCallEqTheory` passes, with no `cheat` in
   lowering/bodyPtrIntCallEqScript.sml or in any theory you add.
2. Helpers go in new leaf theories in lowering/ that bodyPtrIntCallEq
   imports (add them to its `Ancestors`), named `bodyPtrIntCall*`. Do not
   edit any other existing file: not bodyPtrDefs, bodyPtrPreds,
   fragGasPathPtr, fragGasSeqPtr, gasSummaryComposePtr, gasPathPtrExec,
   stmtFragPtr, bodyPtrIntCallCase, bodyPtrIntCallWidened, the ptr toolkit theories (fragExecPtr, typedCopy*Ptr,
   wordCopyRobustPtr, robustCopyTransportPtr, representationCleanPtr,
   returnMetadataPtr, ghostPcTransportPtr, entryHaltPtr, ...), ptrSafeRun,
   ptrDiscipline, the S1 theories (bodySim*, exprSim*, stmtSim*, intCall*,
   gasIntCall*), semantics/ or lowering/defs/. If you need one changed (a
   definition, a premise, a shared lemma), stop and report the exact change
   and why.
3. No duplicate lemmas: search before adding one; reuse what exists.
4. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with
   `>~`, `>-`, `>|`. No step near the 2.5 s tactic timeout (never raise it).

**If the theorem is false as stated:** give a concrete counterexample and
the tightest fix. Do NOT weaken the statement.

## Build

```
holbuild -j4 build bodyPtrIntCallEqTheory
```
(from the project root, the directory containing holproject.toml)

Many ancestor theories in this worktree have their proofs replaced by
`cheat` locally (a build overlay; git doesn't show them as modified). The
CHEAT warnings from those ancestors are expected and not your concern, and
their theorems are usable as stated. Only the target theory and your new
theories must be cheat-free. Never commit changes to those overlaid files.

## Background

S3 of the Vyper compiler correctness proof shows the lowered code is
pointer-safe: every memory access stays inside the allocation its pointer
came from (provenance G), and data from not-yet-written bytes (taint tn)
reaches only dead bytes. It is a twin of S1 (the simulation): each ptr
judgment's post is S1's post (`expr_post`, `vv_post`, `stmt_state_rel`, ...)
plus the ghost conjuncts (`ghost_inv`, `ghost_kept`, `ptr_val_ok` /
`ptr_vv_ok`), over a counted path that also runs `ptr_safe_step` on each
edge. lowering/bodySimPtrMainScript.sml runs the body induction; this is
its internal-call case.

The lowering of the call: `compile_call ... (IntCall func_id)`,
lowering/defs/exprLoweringScript.sml:2627. It compiles the arguments
(`compile_multi_vvs`), allocates a return buffer when the callee returns
through memory (`returns_count > 0` or `return_buf_size > 0`), stages the
arguments (`compile_stage_intcall_args`: memory arguments copied into fresh
buffers unless passed via stack), emits the `INVOKE` (the buffer pointer
first when `returns_count = 0`), and for stack multi-returns stores the
results into the buffer (`store_multi_results`). The source side is
`evaluate`'s `IntCall` clause in semantics/vyperInterpreterScript.sml
(`push_function`, `lookup_callable_function`, defaults evaluated at
`cxd` with scopes `[FEMPTY]`, the body under `cxf`, then the return).

The ptr judgments assume `~cenv.ce_is_ctor`, and `body_inv` (in
lowering/bodySimScript.sml) has `cenv.ce_is_ctor <=> cx.in_deploy`, so
only the runtime unit matters (`lookup_callable_function F` is
`lookup_function NONE fn Internal`).

The callee's body runs as its own Venom function: the IH
`body_stmts_ptr_ok cxf body'` is used at the callee's func, its compile
env, its return buffer `d` (`SOME (buffer, capacity)` for memory returns),
and `PG = MAP (op_prov G) ops` (the caller's operands' provenance, as
ptr_safe_step's INVOKE rule gives the callee). `frame_ret_ok_ptr` for the
callee's returns, with a `RetQ` that carries the ghost back, is what makes
the caller's post after the `INVOKE`.

S1's version of this case (`bodySimCallCases$body_intcall_case`) is
admitted at this base, so S1's whole body result
(`bodySimMain$body_sim_mutual`, giving `body_expr_ok`, hence `expr_sim` and
`expr_vv_sim` for the call) is a usable theorem. The S1 proof of the case
is in progress elsewhere; its partial work (S1-level helper theories
`bodyIntCall*`, not part of this project's build) is a read-only reference
under /home/claude/tasks/s3ptr-intcall/s1c-intcall/lowering/ (its target there is
`bodySimCallIntcall$intcall_body_expr_ok`). Do not import or copy those
theories into the build: read them for the shape only.

## Domain Constraints

- The ptr judgments conclude counted paths (`gas_outcome_ptr` over
  `gas_path_ptr`). The ptr toolkit lemmas are stated over the fixed-run
  `frag_exec_ptr`; use them for per-instruction pointer facts (copies,
  stores, ghost transport) and build the counted paths with the
  combinators of fragGasSeqPtr (`run_inst_seq_gas_path_ptr`,
  `gas_path_ptr_step`, aborts) and gasSummaryComposePtr
  (`gas_outcome_ptr_bind`, `_bind_normal`, `_prefix`, `_conseq`,
  `_erase`, `gas_marked_exec_ptr_*`); `gas_path_ptr_then` sequences paths
  and gasPathPtrExec's `gas_path_ptr_exec` turns a path into a run with
  `ptr_safe_run`/`ghost_run` (what the INVOKE edge needs of the callee).
- The INVOKE edge: ptrSafeRun has `ghost_step_invoke`,
  `ptr_safe_step_invoke` and the `ptr_point_call`/`ptr_point_ret`
  reasoning for the callee's run; intCallStep has `step_inst_invoke_intret`,
  `frag_exec_invoke_intret`, `compile_call_intcall_shape`; intCallFrame
  has `callee_writes_above*` and `invoke_return_*` (the callee writes only
  above the caller's live regions); intCallReturn has
  `invoke_intret_state_rel`, `eval_expr_intcall_return`; intCallResult
  has `store_multi_results_frag`; intCallArgs has `stage_mem_arg_frag`;
  intCallCallee has the callee's entry (`compile_internal_prologue_entry`);
  intCallReturnMem has `compile_internal_return_memory_frag`;
  gasIntCallArgs/gasIntCallBody have the gas-exempt cases.
- Proved ptr pieces to reuse: stmtFragPtr (`stmt_frag_cons_env_ptr`,
  `ghost_inv_jump_to`, `not_fresh_at_mono`, `ghost_inv_gas_obs`,
  `cenv_top_ext_*`), stmtAbortPtr, stmtAssertPtr, exprSimPtr.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target | lowering/bodyPtrIntCallEqScript.sml | the theorem |
| Case and intuition | lowering/bodyPtrIntCallCaseScript.sml | the case it serves; intuition comment |
| Predicates | lowering/bodyPtrPredsScript.sml | body_*_ptr_ok |
| Judgments | lowering/bodyPtrDefsScript.sml | expr_sim_ptr, stmt_frag_ptr, frame_ret_ok_ptr, ghost_inv, ... |
| Counted ptr paths | lowering/fragGasPathPtrScript.sml, lowering/fragGasSeqPtrScript.sml, lowering/gasSummaryComposePtrScript.sml, lowering/gasPathPtrExecScript.sml | path combinators |
| Venom ptr check | venom/compiler/ptrSafeRunScript.sml, venom/compiler/ptrDisciplineScript.sml | ptr_safe_step, ghost_step, INVOKE rules |
| ptr toolkit | lowering/*Ptr*Script.sml | per-instruction pointer facts over frag_exec_ptr |
| Other ptr cases | lowering/bodyPtr*CasesScript.sml, lowering/stmtFragPtrScript.sml, lowering/stmtAbortPtrScript.sml, lowering/stmtAssertPtrScript.sml, lowering/exprSimPtrScript.sml | worked ptr proofs |
| S1 call lemmas | lowering/intCall*Script.sml, lowering/gasIntCall*Script.sml | proved S1 facts about the call lowering |
| S1 case and induction | lowering/bodySimCallCasesScript.sml, lowering/bodySimMainScript.sml, lowering/bodySimScript.sml | S1's statement and body_sim_mutual |
| S1 judgments | lowering/exprSimDefsScript.sml, lowering/stmtSimDefsScript.sml, lowering/exprSimHypsDefsScript.sml, lowering/loweringPostsScript.sml | expr_sim, stmt_frag, expr_post, vv_post |
| Lowering | lowering/defs/exprLoweringScript.sml, lowering/defs/stmtLoweringScript.sml | compile_call, internal function packaging |
| Source semantics | semantics/vyperInterpreterScript.sml | evaluate's IntCall clause |
| S1 partial proof (reference only) | /home/claude/tasks/s3ptr-intcall/s1c-intcall/lowering/bodyIntCall*Script.sml, /home/claude/tasks/s3ptr-intcall/s1c-intcall/lowering/bodySimCallIntcallScript.sml | shape of the S1 proof in progress |

## Notes

- Intermediate lemmas you add are yours to state; the target is frozen.
- Intuition is in the comment above body_intcall_case_ptr in
  lowering/bodyPtrIntCallCaseScript.sml.
- `intCallCallee$internal_prologue_run` is now exported (its `[local]` was
  dropped, statement unchanged), so the prologue leaf can `drule` it.
- Decision 12 is merged: for a word type, `ptr_val_ok` now also requires
  `op_prov G op = NONE` (helpers `ptr_val_ok_word`, `out_prov_*_none` in
  bodyPtrDefs). A word IntCall return is an MLOAD, so it has no provenance;
  adapt any leaf that concludes or consumes a word `ptr_val_ok`.

## Your own helper theories (added 2026-11-06)

The theory files listed in `OWNED_FILES.txt` (at the project root) were written by earlier runs on this task. They are yours: you may edit, restate, split or delete any theorem in them, and repair their proofs, notwithstanding any "do not edit existing theories" rule above. That rule applies only to theories not in that list. Some of them predate the tip merge (word values now carry no provenance: `ptr_val_ok` at a word type includes `op_prov G op = NONE`) and need proof repairs.
