# TASK: subscript target simulation (write side, no pop)

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering/targetPlaceSimCasesScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

In `lowering/targetPlaceSimCasesScript.sml`, currently `cheat`:

```sml
Theorem target_subscript_nopop_case:
  !nocalls ctx func cenv cx bt e.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) /\
    ~target_has_pop (SubscriptTarget bt e) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
```

Definitions the statement uses: `target_case`, `target_post`, `place_ptr_rel`, `place_readable` (lowering/targetPlaceSimScript.sml and its ancestors); `expr_vv_case`, `expr_sim_case`, `target_has_pop` (lowering/exprSimHypsScript.sml); `vv_holds`, `expr_post`, `locals_kept` (lowering/exprSimScript.sml).

**Do not modify this statement, or the definitions above.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build targetPlaceSimCasesTheory` passes with no CHEAT warning for `target_subscript_nopop_case` (`target_subscript_pop_case` is out of scope and stays).
2. No duplicate or near-duplicate lemmas: search lowering/ and semantics/ before proving a helper; each helper exists once, in its most general form, in the theory where it belongs. A new theory (e.g. `lowering/targetSubscriptSimScript.sml`, imported by targetPlaceSimCases) is fine for the case's machinery; a lemma purely about source evaluation (e.g. that a pop-free expression leaves the caller's scopes unchanged) goes in a lowering theory too, not in semantics/.
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout override. No new `cheat`, axiom, or changed statement anywhere.
4. Commit messages end with these two lines:
   `Bot: opus (Claude Opus 5.5)`
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
   Commit only `.sml` sources you changed or added (no `.alan/`, PLAN_, LOG_, DOSSIER_ or evidence files).

**If the theorem is false as stated:** produce a HOL4 counterexample, state the tightest sufficient fix, and do NOT silently weaken the statement.

## Build

```
holbuild -j2 build targetPlaceSimCasesTheory
```

## Background

vyper-hol proves the Vyper-to-Venom lowering correct by simulation. `target_case` is the judgment for an assignment target's place: the code computing the target's pointer (a memory pointer into a local, or a storage/transient slot) ends with `target_post`, relating the pointer to the source's place (`place_ptr_rel`) and saying the place is readable (`place_readable`). This case is `bt[e]` for a base target that is an array or a mapping. `target_attr_case` in the same file is the proved field case: follow its pattern.

Source: `eval_base_place` / `eval_target_place` of `SubscriptTarget` (semantics/vyperInterpreterScript.sml) evaluates the base's place, then the index, then extends the place (`extend_place`, semantics/vyperStateScript.sml): for a mapping, `hashmap_slot slot (encode_hashmap_key kt kv)`; for an array, the bounds check and the element's path or slot (`resolve_array_element` for storage).

Lowering: the base's fragment, the index's (`lower_value`), then by the base's place type `compile_mapping_subscript` (SHA3 over the slot and key words in a fresh 64-byte buffer; `compile_keccak256_key` first for a bytes or string key; a bytesN key is its left-aligned word, as `encode_hashmap_key` now says) or `compile_array_subscript` (the bounds check, an ASSERT that aborts, against the length the loader reads, then the element's pointer).

The base's `place_ptr_rel` survives the index's fragment (`place_ptr_rel_vars_frame`; `expr_post` keeps lookups only as `SOME` values, so it may need a `SOME` variant). Without a pop in the target, evaluating the index leaves the caller's scopes as they were (an internal call restores them via `pop_function`; the only expression that writes a local is `Pop`), so `place_readable` survives; this needs a new lemma by mutual induction over evaluation (model: `eval_mutual_scope_pop_effect` in semantics/prop/vyperPlaceResultTypingScript.sml). A call in the index that shrinks a storage array is fine: both sides read the length after the index.

## Domain Constraints

- HOL4 via holbuild only. Default 2.5 s step timeout: a step that runs over is split or given a smaller rewrite set (the box is heavily loaded; keep steps well under the limit).
- Don't change executable definitions (lowering/defs, semantics/) or any judgment definition.
- Prefer `irule`/`drule_all` to `metis_tac`; no metis over a large search space.
- Name variables with `rename1`, never generated names. Don't use `base` as a variable name (it is a constant).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Statement | lowering/targetPlaceSimCasesScript.sml | the cheat, its comment, target_attr_case, place_ptr_rel_vars_frame (~294) |
| Target judgment | lowering/targetPlaceSimScript.sml | target_case, target_post, place_ptr_rel, place_readable |
| Notes | ~/notes/repos/vyper-hol/target-place-frame.md | how the target judgment's frame works |
| Case judgments | lowering/exprSimHypsScript.sml | expr_vv_case, expr_sim_case, expr_body_pre_eval_result (~810) |
| Frames | lowering/exprSimOpsScript.sml, semantics/prop/vyperEvalExprPreservesScopesDomScript.sml | locals_kept_trans (~315), eval_base_place_preserves_scopes_dom |
| Bounds check | lowering/exprSimArrayIndexScript.sml | compile_array_subscript_ok / _oob (~412/450), array_len_ok_MLOAD/SLOAD/TLOAD (~141–161) |
| SHA3 | lowering/builtinPropsScript.sml, lowering/exprSimHashScript.sml | step_SHA3 (~127), step_SHA3_bytes (~153), hash_alloc_mstore_frame |
| Storage regions | semantics/prop/vyperStoragePlaceProvenanceScript.sml | eval_base_place_region (~190), storage_mapping_region_step/leaf |
| Offsets | lowering/exprSimScript.sml, lowering/exprSimAttributeFieldsScript.sml | mem_path_offset_snoc (~588), slot_count_of_memory_size (~55) |
| Paths | semantics/prop/vyperPlaceResultTypingScript.sml, lowering/exprSimTupleScript.sml | evaluate_subscripts_append (~135), the local read_memory_path snoc lemma (~330) as a model |
| Lowering | lowering/defs/exprLoweringScript.sml | compile_mapping_subscript (~842), compile_keccak256_key (~863), compile_array_subscript |
| Hashmap keys | semantics/vyperStorageScript.sml, semantics/prop/vyperHashMapScript.sml | encode_hashmap_key, hashmap_slot lemmas |

## Notes

- Repo conventions: AGENTS.md at the project root.
- A mapping subscript on the read side (`compile_subscript_map_case` in exprSimPlacesScript.sml) is being proved in parallel in another branch; don't depend on it, but a shared SHA3-slot lemma you write may later be deduplicated with it.
