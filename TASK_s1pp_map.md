# TASK: mapping subscript simulation (counted judgments)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimSubscriptMapScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

Both are in `lowering/exprSimSubscriptMapScript.sml`, currently `cheat`:

```sml
Theorem compile_subscript_map_map_case:
  !nocalls ctx func cenv cx ann obj idx.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) ==>
    expr_map_case nocalls ctx func cenv cx (Subscript ann obj idx)

Theorem compile_subscript_map_case:
  !nocalls ctx func cenv cx ann obj idx kt vt.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    place_type cenv obj = MapPT kt vt ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
```

Definitions the statements use: `expr_map_res_ok`, `expr_map_sim`, `expr_map_pre`, `expr_map_case` (lowering/exprSimMapDefsScript.sml); `expr_vv_case`, `expr_sim_case`, `expr_body_pre`, `expr_sim_inv` (lowering/exprSimHypsDefsScript.sml); `expr_sim`, `expr_vv_sim`, `expr_exit`, `expr_vv_res_ok`, `expr_res_ok` (lowering/exprSimDefsScript.sml); `vv_post`, `vv_holds`, `vv_at`, `expr_post`, `storage_holds`, `slot_loc`, `locals_kept` (lowering/loweringPostsScript.sml); `gas_outcome` (lowering/gasOutcomeScript.sml); `gas_admissible` (lowering/gasContextScript.sml); `storage_mapping_region` (semantics/prop/vyperStoragePlaceProvenanceScript.sml).

**Do not modify these statements, or the definitions above.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build exprSimSubscriptMapTheory` passes with no CHEAT warning for the two theorems above. `compile_toplevel_map_case` in the same file is out of scope (another run proves it) and stays `cheat`; `expr_map_case_below` is proved from it and is fine as is.
2. No duplicate or near-duplicate lemmas: search lowering/ and semantics/ before proving a helper; each helper exists once, in its most general form.
3. New helper theorems go in `exprSimSubscriptMapScript.sml` itself or in a new leaf theory `lowering/exprSimMapKeyScript.sml` that exprSimSubscriptMap imports. Don't edit any other existing theory (exprSimHash, exprSimHyps, exprSimLeaves etc. are shared and frozen for this run).
4. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout override. No new `cheat`, axiom, or changed statement anywhere.
5. Commit only the `.sml` files you added or changed under criterion 3, by explicit path (`git add lowering/exprSimSubscriptMapScript.sml lowering/exprSimMapKeyScript.sml`), never `git add -A`/`-u`/`.`: the worktree has many other modified files (a local overlay that admits unrepaired ancestors) that must never be committed. No `.alan/`, PLAN_, LOG_, DOSSIER_, STATE_, LEARNINGS_ or `alan-ref/` files. Commit messages end with these two lines:
   `Bot: opus (Claude Opus 5.5)`
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`

**If a theorem is false as stated:** produce a HOL4 counterexample, state the tightest sufficient fix, and do NOT silently weaken the statement.

## Build

```
holbuild -j4 build exprSimSubscriptMapTheory
```

## Background

vyper-hol proves the Vyper-to-Venom lowering correct by an expression simulation: for each expression form, the code `compile_expr` emits, run from a state related to the source state, ends related to the source result, or exits as `expr_exit` allows when the source raises. The judgments are counted: `expr_sim`/`expr_vv_sim` conclude `gas_outcome`, a gas-summarised execution (or an exempt certificate) of the source computation alongside the Venom run, with a post `Q res ee t` on success and `expr_exit` on abort.

A mapping (`HashMap[K, V]`) evaluates to a `HashMapRef tr slot kt vt` that no value relation describes and that `well_typed_expr` doesn't type (`type_place_expr` does), so `expr_vv_case` says nothing of a mapping-typed expression. `expr_map_sim` is the mapping-specific judgment: the fragment ends with the pointer's operand holding the mapping's slot, at location `slot_loc tr`, the slot that of a declared mapping, with `vv_post`'s frame. `compile_subscript_map_map_case` is a mapping-valued subscript `m[a]` (its result is again a mapping); `compile_subscript_map_case` is a subscript of a mapping whose values are not mappings, whose result is a storage place (`expr_vv_sim`'s post via `vv_holds`/`storage_holds`).

The lowering: `compile_subscript` on a `MapPT` base calls `compile_mapping_subscript`, which stores the slot and the key's word in a fresh 64-byte buffer and SHA3s it; a bytes or string key is first hashed by `compile_keccak256_key`. The source: Subscript evaluates the base, then the index, reads it, and `extend_place` on a `HashMapRef` gives `hashmap_slot slot (encode_hashmap_key kt kv)`.

These exact two statements were proved before, on an older base whose judgments were uncounted (`frag_exec` instead of `gas_outcome`). That work is in `alan-ref/seq616/` (plain-text copies, `.sml.txt`): `exprSimMapScript.sml.txt` (the mapping machinery: key encoding, the two-word SHA3 run, the shared `compile_mapping_subscript_frag`, the consumers), `exprSimHashScript.sml.txt` (helpers it added: `emit_ADD_frame`, `emit_MLOAD_frame`, `emit_length_prefixed_hash_run`, `hash_alloc_two_words_frame`, a cap-general `hash_alloc_mstore_frame`), `exprSimHypsScript.sml.txt` (`expr_map_pre_eval_result`, `expr_map_pre_subscript_base`, `expr_body_pre_map_subscript_base`, `expr_map_pre_res_ok`, `expr_subscript_pre_index`), `exprSimPlacesScript.sml.txt` (the old proofs of these two theorems), and `task-diff.patch.txt` (the whole old diff). Its proof structure and lemmas are a guide; its statements over `frag_exec` don't apply directly here.

## Domain Constraints

- HOL4 via holbuild only. Default 2.5 s step timeout: a step that runs over is split or given a smaller rewrite set.
- Don't change executable definitions (lowering/defs, semantics/) or any judgment definition.
- Prefer `irule`/`drule_all` to `metis_tac`; no metis over a large search space.
- Name variables with `rename1`, never generated names.
- Some ancestor theories have their proofs admitted locally (the overlay); their statements are what counts. Use them freely; don't try to repair them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Statements | lowering/exprSimSubscriptMapScript.sml | the cheats and the comments above them; `expr_map_case_below` shows how they're consumed |
| Map judgment | lowering/exprSimMapDefsScript.sml | expr_map_res_ok, expr_map_sim, expr_map_pre, expr_map_case, expr_map_case_other |
| Consumer | lowering/exprSimPlacesScript.sml | compile_subscript_case, compile_subscript_sim |
| Counted judgments | lowering/exprSimDefsScript.sml, lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/gasExemptCertScript.sml | expr_sim, expr_vv_sim, gas_outcome and their composition (bind/ignore_bind) |
| Counted composition examples | lowering/exprSimAttributeScript.sml, lowering/exprSimTupleScript.sml, lowering/exprSimSubscriptArrayScript.sml, lowering/stmtSimAssignComposeScript.sml | base then step over gas_outcome, with frames |
| Shared case lemmas | lowering/exprSimHypsScript.sml | expr_body_pre_eval_result and friends (well-typed expressions only; a mapping base needs expr_map_pre analogs) |
| Storage leaf sim | lowering/exprSimLeavesScript.sml | compile_toplevel_storage_vv_sim, toplevel_storage_slots_in_range: the same pattern for a storage variable |
| SHA3 / buffer frames | lowering/exprSimHashScript.sml | hash_alloc_mstore_frame, emit_SHA3_bytes_frame, compile_keccak256_bytes_run, wb_frame_allocating_tail, vv_post_frame_intro |
| Word-args frames | lowering/exprSimWordArgsScript.sml | wb_frame, expr_post_frame, wb_frame_trans, wb_frame_readonly_tail |
| Lowering | lowering/defs/exprLoweringScript.sml | compile_expr, compile_subscript, compile_mapping_subscript, compile_keccak256_key |
| Compile env | lowering/defs/compileEnvScript.sml | storage_vars_rel, transient_vars_rel, state_rel |
| Source semantics | semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml | eval_expr Subscript, extend_place, hashmap_slot, encode_hashmap_key |
| Mapping regions | semantics/prop/vyperStoragePlaceProvenanceScript.sml | storage_mapping_region and its step/leaf lemmas |
| Place typing | lowering/placeTypingPropsScript.sml | place_type_checked_place_on_defined, place_type_well_typed_on_defined |
| Type soundness | semantics/prop/vyperTypeEvalSoundnessScript.sml | eval_scc_type_sound_mutual (type_place_expr conjuncts) |
| Old proofs | alan-ref/seq616/ | see Background |

## Notes

- Repo conventions: AGENTS.md at the project root.
- In `compile_subscript_map_case`, a mapping-valued `vt` is impossible: `expr_body_pre` requires `well_typed_expr` of the subscript, which forces the base to be place-typed with `subscript_vtype ... = SOME (Type ann)`.
- The base's pointer operand must survive the key's code: `expr_map_sim`'s post doesn't say so directly, but the operand is a literal or the SHA3 result variable from earlier code (the old `compile_mapping_operand_not_label`).
