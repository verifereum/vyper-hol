# TASK: mapping subscript simulation (read side)

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/exprSimPlacesScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

All three are in `lowering/exprSimPlacesScript.sml`, currently `cheat`:

```sml
Theorem compile_toplevel_map_case:
  !nocalls ctx func cenv cx ty id.
    expr_map_case nocalls ctx func cenv cx (TopLevelName ty id)

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

Definitions the statements use: `expr_map_case`, `expr_map_sim`, `expr_map_pre`, `slot_loc`, `expr_vv_case`, `expr_sim_case`, `expr_body_pre` (lowering/exprSimHypsScript.sml); `expr_vv_sim`, `vv_post`, `vv_holds`, `vv_at`, `storage_holds`, `locals_kept` (lowering/exprSimScript.sml).

**Do not modify these statements, or the definitions above.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build exprSimPlacesTheory` passes with no CHEAT warning for the three theorems above (the other cheats in exprSimPlacesScript.sml, `compile_subscript_array_case` and the pop cases, are out of scope and stay).
2. No duplicate or near-duplicate lemmas: search the lowering/ and semantics/ theories before proving a helper; each helper exists once, in its most general form, in the theory where it belongs (a new `lowering/exprSimMapScript.sml` theory imported by exprSimPlaces is fine for the mapping machinery).
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout override. No new `cheat`, axiom, or changed statement anywhere.
4. Commit messages end with these two lines:
   `Bot: opus (Claude Opus 5.5)`
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
   Commit only `.sml` sources you changed or added (no `.alan/`, PLAN_, LOG_, DOSSIER_ or evidence files).

**If a theorem is false as stated:** produce a HOL4 counterexample, state the tightest sufficient fix, and do NOT silently weaken the statement.

## Build

```
holbuild -j4 build exprSimPlacesTheory
```

## Background

vyper-hol proves the Vyper-to-Venom lowering correct by an expression simulation: for each expression form, the code `compile_expr` emits, run from a state related to the source state, ends related to the source result (`expr_vv_sim`), or exits as `expr_exit` allows when the source raises. A mapping (`HashMap[K, V]`) evaluates to a `HashMapRef tr slot kt vt` that no value relation describes, so `expr_map_sim` is the mapping-specific judgment: the fragment ends with the pointer's operand holding the mapping's slot, at location `slot_loc tr`, with vv_post's frame. These three theorems are its cases: a mapping variable, a mapping-valued subscript `m[a]`, and a subscript of a mapping whose values are not mappings, whose result is a storage place.

The lowering: `compile_expr` on a `TopLevelName` of a mapping returns its slot as a literal pointer; `compile_subscript` on a `MapPT` base calls `compile_mapping_subscript`, which stores the slot and the key's word in a fresh 64-byte buffer and SHA3s it; a bytes or string key is first hashed by `compile_keccak256_key`. The source: `extend_place` on a `HashMapRef` gives `hashmap_slot slot (encode_hashmap_key kt kv)`. The branch merges a semantics change making a fixed-size `bytesN` key encode as its left-aligned word, as the lowering does.

## Domain Constraints

- HOL4 via holbuild only. Default 2.5 s step timeout: a step that runs over is split or given a smaller rewrite set.
- Don't change executable definitions (the lowering in lowering/defs, the semantics in semantics/) or any judgment definition.
- Prefer `irule`/`drule_all` to `metis_tac`; no metis over a large search space.
- Name variables with `rename1`, never generated names.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Statements | lowering/exprSimPlacesScript.sml | the three cheats, and the comments above them |
| Map judgment | lowering/exprSimHypsScript.sml (section "The judgment of an expression naming a mapping") | expr_map_sim, expr_map_pre, expr_map_case, slot_loc, expr_map_case_other |
| Core judgments | lowering/exprSimScript.sml | expr_vv_sim, vv_post, vv_holds, vv_at, expr_post, locals_kept, storage_holds |
| Shared case lemmas | lowering/exprSimHypsScript.sml | expr_vv_case, expr_sim_case, expr_body_pre, expr_body_pre_eval_result (well-typed expressions only; a mapping base needs an expr_map_pre analog) |
| Storage leaf sim | lowering/exprSimLeavesScript.sml | compile_toplevel_storage_vv_sim, toplevel_storage_slots_in_range: the same pattern for a storage variable |
| SHA3 buffer frame | lowering/exprSimHashScript.sml | hash_alloc_mstore_frame and the keccak simulation (no cheats) |
| Lowering | lowering/defs/exprLoweringScript.sml | compile_expr, compile_subscript, compile_mapping_subscript (line ~842), compile_keccak256_key (~863) |
| Compile env | lowering/defs/compileEnvScript.sml | storage_vars_rel, transient_vars_rel, state_rel, local_ptrs_rel |
| Source semantics | semantics/vyperStateScript.sml, semantics/vyperStorageScript.sml | eval of TopLevelName/Subscript, extend_place, hashmap_slot, encode_hashmap_key |
| Mapping regions | semantics/prop/vyperStoragePlaceProvenanceScript.sml | storage_mapping_region_step (47), storage_mapping_region_leaf (61), lookup_global_mapping_region (88) |
| Lookup results | semantics/prop/vyperPlaceResultTypingScript.sml | lookup_global_toplevel_ready |
| Place typing | lowering/placeTypingPropsScript.sml | place_type_checked_place_on_defined, place_type_well_typed_on_defined |
| Type soundness | semantics/prop/vyperTypeEvalSoundnessScript.sml | eval_scc_type_sound_mutual (type_place_expr conjuncts) |
| Storage preservation | lowering/bodyStoragePreservationScript.sml | storage well-formedness after evaluation |
| Slots in range | semantics/prop/vyperLookupStorageScript.sml | storage_field_slots_in_range |
| Hashmap facts | semantics/prop/vyperHashMapScript.sml | hashmap_slot / key lemmas |
| Similar proved cases | lowering/exprSimAttributeScript.sml, lowering/exprSimTupleScript.sml | compile_attribute_vv_sim, compile_subscript_tuple_sim: base then step, with frames |

## Notes

- Repo conventions: AGENTS.md at the project root.
- In `compile_subscript_map_case`, a mapping-valued `vt` is impossible: `expr_body_pre` requires `well_typed_expr` of the subscript, which forces the base to be place-typed with `subscript_vtype ... = SOME (Type ann)`.
