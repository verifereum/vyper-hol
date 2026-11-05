# TASK: pop_nested_storage_pure_sim (Pop on a nested storage dynarray with pure indices, counted gas judgment)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimPopNestedBaseScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem pop_nested_storage_pure_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
```

Definitions: `pop_target_frag_def` (top of lowering/exprSimPopNestedBaseScript.sml); `expr_vv_sim_def`, `expr_vv_res_ok_def`, `expr_exit_def` (lowering/exprSimDefsScript.sml); `gas_outcome_def` (lowering/gasOutcomeScript.sml); `gas_summary_at_def` (lowering/gasSummaryScript.sml); `gas_admissible_def` (lowering/gasContextScript.sml); `vv_post_def`, `target_post_def` (lowering/loweringPostsScript.sml); `expr_body_pre_def` (lowering/exprSimHypsDefsScript.sml); `target_indices_def` (lowering/targetPlaceLiveScript.sml); `pure_expr_def` (semantics/prop/vyperPureExprScript.sml).

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild(targets=['exprSimPopNestedBaseTheory','exprSimPopNestedTheory'])` passes.
2. No `cheat` anywhere in lowering/exprSimPopNestedBaseScript.sml or in any helper theory you add.
3. No duplicate lemmas: search `lowering/` and `semantics/` before adding a helper; reuse what exists.

Weakly frozen: the other theorems in exprSimPopNestedBaseScript.sml are helpers used only inside this file. You may restate or replace any of them (e.g. `nested_pop_storage_suffix_sim`, still in the old `frag_exec` form, and `nested_pop_suffix_vv_post`), or add new ones. Keep `pop_target_frag_def`, `nested_pop_suffix_def` and `pop_target_frag_of_sim` as they are.

Expected and fine: inherited admissions. About 30 shared ancestor theories have their proofs admitted locally in this worktree (their repair is other work: e.g. exprSimPop's `pop_step_*`, exprSimHash's `hash_run_path`). A theorem that depends on them shows as CHEAT in the build log; that's expected. Only `cheat` written in the files you edit counts against criterion 2.

**If the theorem is false as stated:** produce a concrete counterexample and state the tightest sufficient fix. Do NOT weaken the statement.

## Build

```
holbuild -j4 build exprSimPopNestedBaseTheory exprSimPopNestedTheory
```

## Background

vyper-hol proves the Vyper-to-Venom lowering correct by simulation. `expr_vv_sim ... e es` says the code `compile_expr` emits for `e` simulates the source's `eval_expr cx e` in the gas-counted form: `gas_outcome` over a `gas_admissible` source run, where the target's GAS readings pick the source's gas observations. This theorem is `x.pop()` where `x` is a dynamic array nested inside a storage (or transient) variable and every index on the way is pure. The code is the target pointer (`compile_get_target_ptr`, simulated by the `pop_target_frag` hypothesis) followed by a 9-instruction suffix (`nested_pop_suffix_def`: load the header, assert it nonzero, store length-1, compute the last element's slot). The theorem was proved before the gas join in `frag_exec` form; that proof is in this file (and `alan-ref/base-cut/exprSimPopNestedScript.sml.txt`). Since then `expr_vv_sim` and `pop_target_frag` moved to `gas_outcome`, and SSTORE/TSTORE abort in a static frame (`cc_static`). Every helper above the theorem now builds (some show inherited CHEAT); the theorem's own proof and `nested_pop_storage_suffix_sim`'s use of `frag_exec` are what needs porting. The comment above the theorem gives the argument.

## Domain Constraints

- Don't change any definition or any statement other than the weakly frozen helpers above and your own new ones: nothing in `semantics/`, `frontend/`, `lowering/defs/`, `venom/`, the judgments (`exprSim*Defs`, `exprSimHyps*`, `bodySim*`, `*Main`, `targetPlaceSim*`, `loweringPosts`, `gas*`), or `targetPlaceLive`.
- Put new helpers in lowering/exprSimPopNestedBaseScript.sml or a new leaf theory `lowering/exprSimPopNested<Something>Script.sml` that exprSimPopNestedBase imports; never edit low shared ancestors.
- holbuild's default 2.5 s step timeout stays; no `tactic_timeout` override. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No new `cheat`, axiom or oracle.
- Commit only the `.sml` files you create or edit (and this task's own files if your workflow requires). Never commit anything under `alan-ref/`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target file | lowering/exprSimPopNestedBaseScript.sml | statement, helpers, argument comment |
| Consumer | lowering/exprSimPopNestedScript.sml | uses the theorem; must still build |
| Counted target case (model of a ported composition) | lowering/targetPlaceSimCasesBaseScript.sml (`target_attr_case`, `target_attr_add_path`, `extend_place_attr_gas_obs`), lowering/targetPlaceSimCasesScript.sml (`target_place_sim`) | gas_outcome over a bind with a gas-free continuation and a 0-GAS path |
| Gas composition | lowering/gasSummaryComposeScript.sml (`gas_marked_exec_bind_normal`, `gas_marked_exec_bind_exception`), lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/fragGasModeScript.sml | |
| Exemption lifting | grep `gas_exempt_cert_error_result` in lowering/ | exempt branch through a bind |
| Straight-line runs as counted paths | lowering/exprSimHashScript.sml (`hash_run_path`, `hash_abort_path`), lowering/fragGasSeqAbortScript.sml (`run_inst_seq_abort_zero_path`), lowering/fragGasFreshScript.sml, lowering/emitHelperPropsScript.sml (`emit_op_zero_path`) | |
| gas_obs invariance | lowering/exprSimWordArgsScript.sml (`stmt_state_rel_gas_obs`), lowering/exprSimHypsDefsScript.sml (`expr_sim_inv_gas_obs`), lowering/exprSimSourceScript.sml (`expr_body_pre_gas_obs`), lowering/stmtSimAssignStorageScript.sml (`write_storage_slot_gas_obs`, `assign_storage_store_path`), lowering/stmtSimDeclComposeScript.sml (`gas_marked_exec_end_gas_obs`) | |
| Non-nested storage pop (same suffix, top-level slot) | lowering/exprSimPopStorageScript.sml | still the pre-gas-join proof; facts reusable, composition not |
| Pure target state, liveness | lowering/targetPlaceLiveScript.sml | nested_pop_eval_target_pure_state, nested_pop_eval_target_live |
| Static frame | lowering/defs/compileEnvScript.sml (`state_rel_def`: `~cx.txn.is_static`, call ctx) | `stmt_state_rel` gives `~s.vs_call_ctx.cc_static` |
| Source semantics | semantics/vyperInterpreterScript.sml (eval_expr Pop ~l.1586), semantics/vyperStateScript.sml (pop_place_def ~l.1261) | |
| Compiler | lowering/defs/exprLoweringScript.sml (compile_get_target_ptr, compile_dynarray_pop) | |
| Pre-split original file | alan-ref/base-cut/exprSimPopNestedScript.sml.txt | frag_exec-era proof |
| Porting gotchas | -- |  Known: `gas_marked_exec_bind_normal` and the exempt bind rules hand the continuation `mid with gas_obs := []`; apply `gas_marked_exec_bind_normal` forward (`drule_all`) or via `irule` with explicit `qexistsl_tac`; `expr_exit` is polymorphic in the INL type, use `stmtSimProps.expr_exit_INR_type` | |
| Repo conventions | AGENTS.md | read first |

## Notes

- `alan-ref/` is reference material only: not built, not committed.
