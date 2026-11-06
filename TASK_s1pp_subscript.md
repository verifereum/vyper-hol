# TASK: target_subscript_case (write-side target judgment for an array element or a mapping value)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/targetSubscriptCaseScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem target_subscript_case:
  !nocalls ctx func cenv cx bt e.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
```

Definitions: `target_case_def`, `target_pre_def`, `target_root_def`, `toplevel_target_env` (lowering/targetPlaceSimScript.sml); `target_sim_def` (lowering/targetPlaceSimDefsScript.sml); `target_post_def`, `place_readable_def` (lowering/loweringPostsScript.sml); `target_indices_def` (lowering/targetPlaceLiveScript.sml); `pure_expr_def` (semantics/prop/vyperPureExprScript.sml); `supported_target_exists` (lowering/supported/supportedExprTraverseScript.sml); `expr_sim_case_def`, `expr_vv_case_def` (lowering/exprSimHypsDefsScript.sml).

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild(targets=['targetSubscriptSplitTheory','targetSubscriptCaseTheory'])` passes (plus any leaf theory you add).
2. `target_subscript_case` is proved, and the only `cheat`s it rests on in the files you edit are the two admitted residuals below.
3. No duplicate lemmas: search `lowering/` and `semantics/` before adding a helper; reuse what exists.

**Admitted residuals: given premises, not yours.** In lowering/targetSubscriptSplitScript.sml, `target_subscript_storage_effectful_case` (a storage/top-level root with an impure index) and `target_subscript_local_pop_case` (a local root with a Pop in an index) are admitted on purpose. Use them as given; do not prove, restate, move or delete them, and keep their `cheat` proofs exactly as they are.

**Everything else is yours.** `target_subscript_main_case` (the remaining case, now a helper rather than the goal), the dispatcher proof of `target_subscript_case`, and every helper in the targetSubscript* leaf theories may be restated, re-split or reorganised, as long as `target_subscript_case` keeps its statement and rests only on the two residuals (plus inherited admissions).

Expected and fine: inherited admissions. About 30 shared ancestor theories have their proofs admitted locally in this worktree (their repair is other work), and several lemmas you may use are admitted in the committed tree (e.g. `target_attr_case`, `target_place_sim`, exprSimPopNestedBase's helpers). A theorem that depends on them shows as CHEAT in the build log; that's expected. Only `cheat` written in the files you edit counts against criterion 2.

**If the theorem is false as stated:** produce a concrete HOL4 counterexample and state the tightest sufficient fix. Do NOT weaken the statement.

## Build

```
holbuild -j4 build targetSubscriptSplitTheory targetSubscriptCaseTheory
```

## Background

vyper-hol proves the Vyper-to-Venom lowering correct by simulation. `target_case ... bt` says the code `compile_get_target_ptr` emits for an assignment target `bt` simulates the source's `eval_base_place cx bt`, in the gas-counted form (`gas_outcome` over a `gas_admissible` source run): on success the machine ends with an operand pointing at the source's place (`target_post`), and on a source error it exits as `expr_exit` allows. This theorem is the step for `SubscriptTarget bt e` (an element of an array, or a mapping's value): the base's fragment, then the index's (`lower_value`), then either `compile_array_subscript` (bounds check against the length the loader reads, then the element's pointer) or `compile_mapping_subscript` (SHA3 of slot and key, with `compile_keccak256_key` for a bytes/string key). The field step `target_attr_case` is the closest model; its pre-gas-join proof is in `/home/claude/tasks/s1pp/alan-ref-subscript/base-cut/targetPlaceSimCasesScript.sml.txt`. The comment above `target_subscript_main_case` in lowering/targetSubscriptSplitScript.sml gives the argument. The cases where an index can shrink an array the place is already in (a storage root with an effectful index; a local root with a pop) are the two admitted residuals and are out of scope.

## Domain Constraints

- Don't change any definition, or any statement other than the helpers that are yours (above): nothing in `semantics/`, `frontend/`, `lowering/defs/`, `venom/`, the judgments (`exprSim*Defs`, `exprSimHyps*`, `bodySim*`, `*Main`, `targetPlaceSim*`, `loweringPosts`), or `targetPlaceLive`.
- Put new helpers in lowering/targetSubscriptSplitScript.sml or in a new leaf theory `lowering/targetSubscript<Something>Script.sml` that targetSubscriptSplit imports; never edit low shared ancestors.
- holbuild's default 2.5 s step timeout stays; no `tactic_timeout` override. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No new `cheat`, axiom or oracle.
- Commit only the `.sml` files you create or edit (and this task's own files if your workflow requires).

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Split file | lowering/targetSubscriptSplitScript.sml | target_subscript_main_case (yours) with its argument comment; the two admitted residuals |
| Goal and dispatcher | lowering/targetSubscriptCaseScript.sml | target_subscript_case, currently proved from main_case and the two residuals |
| Shared target facts | lowering/targetPlaceSimCasesBaseScript.sml | eval_base_place_sim_inv, place_ptr_rel_vars_frame, target_post_add, target_pre_sub, base_assignment_target_induct, field-step helpers |
| Target judgment | lowering/targetPlaceSimScript.sml, lowering/targetPlaceSimDefsScript.sml | target_case/target_pre/target_sim; toplevel_target_env; name/toplevel cases |
| Storage liveness (pure targets) | lowering/targetPlaceLiveScript.sml | nested_pop_eval_base_pure_state, nested_pop_eval_base_live, nested_pop_result_live_def, nested_pop_live_*_element |
| Storage relation | lowering/defs/compileEnvScript.sml | storage_dead, storage_read_live, storage_agree, accounts_agree |
| Storage relation lemmas | lowering/accountsRelPropsScript.sml | declared_storage_region_read_live, storage_read_live_head, ... |
| Header load agreement | lowering/exprSimPopNestedBaseScript.sml | nested_pop_live_array_agree, nested_pop_array_header_load (admitted; usable) |
| Read-side array subscript | lowering/exprSimSubscript*Script.sml, lowering/exprSimPlacesScript.sml | the expression-side (value) version of the same compile steps |
| Mapping hash | lowering/exprSimSubscriptMapScript.sml and grep `compile_mapping_subscript` in lowering/ | compile_mapping_subscript execution |
| Gas judgment adapters | lowering/gasOutcomeScript.sml, lowering/gasNormalPrefixScript.sml, lowering/stmtSimPropsScript.sml | gas_outcome sequencing and prefixes |
| Source semantics | semantics/vyperInterpreterScript.sml (eval_base_place ~l.1745), semantics/vyperStateScript.sml (extend_place, extend_storage_place, resolve_array_element, read_memory_path) | |
| Compiler | lowering/defs/exprLoweringScript.sml (compile_get_target_ptr, compile_array_subscript, compile_mapping_subscript, compile_keccak256_key) | |
| Old helpers (pre gas join, frag_exec form; port, don't copy blindly) | /home/claude/tasks/s1pp/alan-ref-subscript/seq-616-write/targetSubscriptSimScript.sml.txt | target_post_index_frame, target_index_frag, target_memory_array_suffix, target_mapping_* etc. |
| Old split and old field proof | /home/claude/tasks/s1pp/alan-ref-subscript/seq-616-write/targetPlaceSimCasesScript.sml.txt, /home/claude/tasks/s1pp/alan-ref-subscript/base-cut/targetPlaceSimCasesScript.sml.txt | |
| Old run's learnings | /home/claude/tasks/s1pp/alan-ref-subscript/seq-616-write/LEARNINGS_seq616_write.md | tactics that worked/failed on this family |
| Repo conventions | AGENTS.md | read first |

## Notes

- `/home/claude/tasks/s1pp/alan-ref-subscript/` (outside the checkout) is reference material only.
- An earlier prover run spent long on a storage case where an index of the *base* is effectful; that case is now excluded by the purity premise over every index (`target_indices`), so don't revisit it.
