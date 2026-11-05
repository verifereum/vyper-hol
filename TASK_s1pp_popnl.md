# TASK: pop on an array inside a memory local

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimPopNestedLocalScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

In `lowering/exprSimPopNestedLocalScript.sml`, currently `cheat`:

```sml
Theorem pop_nested_local_sim:
  !ctx func cenv cx env ann bt ty es id.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
```

`pop_target_frag` is defined in `lowering/exprSimPopNestedBaseScript.sml`; `expr_vv_sim` in `lowering/exprSimDefsScript.sml`; `expr_body_pre` in `lowering/exprSimHypsDefsScript.sml`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

You may use the deliberately admitted leaf `pop_local_popped_in_memory` in `lowering/exprSimPopNestedLocalPoppedScript.sml` (its comment says why it is admitted). Leave it, its statement and its `cheat` unchanged; it is the only admitted lemma of this piece.

## Completion Criteria

1. `holbuild -j4 build exprSimPopNestedLocalTheory exprSimPopNestedTheory` passes with no CHEAT warning for `pop_nested_local_sim` other than through `pop_local_popped_in_memory` and the theories of the local overlay (below).
2. No duplicate or near-duplicate lemmas: search `lowering/` and `semantics/` before proving a helper; each helper exists once, in its most general form. Put this piece's machinery in new leaf theories (e.g. `lowering/exprSimPopNestedLocalPropsScript.sml`) that `exprSimPopNestedLocal` imports; don't edit low-level shared ancestors, except to add a lemma next to its definition where it belongs.
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout override. No new `cheat`, axiom, or changed statement anywhere. Don't change any definition in `semantics/`, `frontend/`, `lowering/defs/`, `venom/`, or any judgment (`exprSim*Defs`, `exprSimHyps*`, `loweringPosts`, `bodySim*`, `*Main`).
4. Commit messages end with these two lines:
   `Bot: opus (Claude Opus 5.5)`
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
   Commit only `.sml` sources you changed or added. Never commit the 30 files the working tree has modified as a local admission overlay (listed in `alan-ref/overlaid.txt`), nor `alan-ref/`, `.alan/`, PLAN_, LOG_, STATE_, LEARNINGS_, DOSSIER_ or evidence files.

**If the theorem is false as stated:** produce a HOL4 counterexample, state the tightest sufficient fix, and do NOT silently weaken the statement.

## Build

```
holbuild -j4 build exprSimPopNestedLocalTheory exprSimPopNestedTheory
```

## Background

vyper-hol proves the Vyper-to-Venom lowering correct by an expression simulation: for each expression form, the code `compile_expr` emits, run from a state related to the source state, ends related to the source result (`expr_vv_sim`, in the counted `gas_outcome` form), or exits as `expr_exit` allows when the source raises.

This case is `bt.pop()` where the target `bt` is rooted at a memory local: the local itself (`x.pop()`), a field or element of it (`x.a.pop()`, `x[i].pop()`, deeper). Indices may have effects, including pops.

Source: `eval_expr cx (Pop _ bt)` (semantics/vyperInterpreterScript.sml) is `eval_target_place cx bt` then `pop_place cx` (semantics/vyperStateScript.sml). For `MemoryPlace id path`, `pop_place` reads the array through `read_memory_path` (the live value, else the popped history `read_popped`), shortens it in the value (`assign_subscripts`) or in the history (`replace_popped`), records the popped element (`record_pop`) and returns the place of the popped element, `path ++ [ValueSubscript (len-1)]`, which is then read back through the history.

Lowering: the `Pop` case of `compile_expr` (lowering/defs/exprLoweringScript.sml) takes the target's pointer, location and type from `compile_get_target_ptr`, then `compile_dynarray_pop` at that pointer (memory: MLOAD length, assert nonzero, MSTORE length-1, element pointer), returning `LocatedValue ann (mk_ptr elem_ptr LocMemory)`. `pop_target_frag` is the target's counted fragment: it ends in `target_post` (lowering/loweringPostsScript.sml) with the place and the pointer related by `place_ptr_rel` (the local's base plus `mem_path_offset`).

The pop's MSTORE writes a dynamic array's length word inside the local's region; `locals_kept` exempts exactly those words (`dynarray_len_at`; see `local_path_at_dynarray_len_at` in lowering/exprSimAttributeFieldsScript.sml).

The root case `bt = NameTarget id` is also `exprSimPop.compile_pop_name_sim` (old proof shape, admitted in the overlay); it shows the memory run (`dynarray_pop_mem_shape`, `dynarray_pop_mem_run`, `dynarray_pop_mem_run_empty`) and the post (`pop_vv_post`, `pop_local_ptrs_rel`, `pop_elem_in_memory`, `pop_locals_kept`) for path `[]`. The overlay replaced its proofs with `cheat`; read the committed proofs with `git show HEAD:lowering/exprSimPopScript.sml`.

## Domain Constraints

- Follow `AGENTS.md` at the project root (proof conventions for this repo).
- Default step timeout (2.5 s). A step near it is a proof performance bug: split it or cut the rewrite set.
- The working tree carries an uncommitted local overlay that admits the proofs of 30 shared theories not yet repaired on this branch (listed in `alan-ref/overlaid.txt`). Use their statements freely; don't edit, fix or commit them. Their committed proofs are readable with `git show HEAD:<file>`.
- `exprSimPopNestedBase` has other admitted helpers (storage pop) that belong to other pieces; don't depend on them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target | `lowering/exprSimPopNestedLocalScript.sml` | The theorem and its comment |
| Admitted leaf | `lowering/exprSimPopNestedLocalPoppedScript.sml` | `pop_local_popped_in_memory`: a path dead in the value but read through the history sits in memory |
| Target fragment | `lowering/exprSimPopNestedBaseScript.sml` | `pop_target_frag_def` |
| Consumer | `lowering/exprSimPopNestedScript.sml` | `pop_nested_sim` dispatches to this theorem |
| Judgments | `lowering/exprSimDefsScript.sml`, `lowering/exprSimHypsDefsScript.sml`, `lowering/gasOutcomeScript.sml` | `expr_vv_sim`, `expr_exit`, `expr_body_pre`, `expr_sim_inv`, `popped_keys_indexed`, `gas_outcome` |
| Posts | `lowering/loweringPostsScript.sml` | `target_post`, `place_ptr_rel`, `place_readable`, `vv_post`, `vv_holds`, `vv_at`, `locals_kept`, `dynarray_len_at`, `mem_path_offset`, `local_path_at` |
| State relation | `lowering/exprLoweringPropsScript.sml`, `lowering/defs/compileEnvScript.sml`, `lowering/localPtrsPropsScript.sml` | `stmt_state_rel`, `state_rel`, `local_ptrs_rel`, `local_region`, `local_ptrs_rel_write_local`, `local_ptrs_rel_mstore` |
| Memory encoding | `lowering/defs/valueEncodingScript.sml` | `val_in_memory`, `val_wf`, `elems_in_memory` |
| Path offsets | `lowering/exprSimPropsScript.sml`, `lowering/exprSimAttributeFieldsScript.sml` | `mem_path_offset_snoc`, `mem_path_offset_sound`, `mem_path_offset_dynarray_apart`, `local_path_at_dynarray_len_at`, `mem_path_offset_type` |
| Root-case pop | `lowering/exprSimPopScript.sml` (proofs via `git show HEAD:`) | The memory pop run and its post at path `[]` |
| Counted composition (templates) | `lowering/exprSimUnopComposeScript.sml`, `lowering/exprSimUnopComposePropsScript.sml`, `lowering/gasSummaryComposeScript.sml`, `lowering/stmtSimAssignComposeScript.sml`, `lowering/exprSimHashScript.sml` (`hash_run_path`, `hash_abort_path`) | Prefix `gas_outcome` then a straight-line run: `gas_marked_exec_bind_normal`, `gas_marked_exec_bind_exception`, the exempt-cert bind rules |
| Target cases in the counted form | `lowering/targetPlaceSimCasesBaseScript.sml`, `lowering/targetPlaceSimCasesScript.sml`, `lowering/stmtSimAssignAttrScript.sml` | Memory place pointers and writes at a field path |
| Popped history facts | `lowering/stmtPoppedKeysScript.sml`, `lowering/exprSimHypsScript.sml` | `popped_keys_indexed` preservation (`eval_target_place_popped_keys_indexed`) |
| Source facts | `semantics/prop/` (e.g. `vyperStatePreservationScript.sml`, `vyperPlaceFramesScript.sml`) | Evaluation invariants (scopes domain, assignability) |
| Overlay list | `alan-ref/overlaid.txt` | The 30 locally admitted theories |
| HOL4 sources | `.holbuild/src/` is off limits; use theory names via `DB.find` in scratch probes | |

## Notes

- The case split between a live place (`evaluate_subscripts entry.type entry.value path = INL _`) and a place read through the history is the prover's to arrange; only the history case's memory fact is admitted.
