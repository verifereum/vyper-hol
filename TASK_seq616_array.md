# TASK: array subscript simulation (read side, no pop)

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering/exprSimPlacesScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

In `lowering/exprSimPlacesScript.sml`, currently `cheat`:

```sml
Theorem compile_subscript_array_nopop_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    ~expr_has_pop (Subscript ann obj idx) /\
    (!ty st l. vv_location (FST (compile_expr cenv ty obj st)) = SOME l /\
               is_slot_addressed l ==> ~expr_has_effect idx) /\
    (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode ==>
             ~cenv.ce_is_ctor) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
```

Definitions the statement uses: `expr_vv_case`, `expr_sim_case`, `expr_body_pre`, `expr_has_pop` (lowering/exprSimHypsScript.sml); `expr_vv_sim`, `vv_post`, `vv_holds`, `vv_at`, `local_place_at`, `expr_post`, `locals_kept`, `storage_holds` (lowering/exprSimScript.sml); `expr_has_effect` (lowering/supported/supportedExprTraverseScript.sml).

**Do not modify this statement, or the definitions above.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimPlacesTheory` passes with no CHEAT warning for `compile_subscript_array_nopop_case`. The other cheats in exprSimPlacesScript.sml (the mapping cases, `compile_subscript_array_pop_case`, `compile_subscript_array_storage_call_case`, `compile_subscript_array_ctor_code_case`, the pop cases) are out of scope and stay.
2. An `array_len_ok` lemma for a dynamic array in code (LocCode, outside the constructor: compile_imm_load_word's ILOAD/DLOAD), next to `array_len_ok_MLOAD`/`SLOAD`/`TLOAD` in lowering/exprSimArrayIndexScript.sml, if the proof needs it (it does for an immutable base).
3. No duplicate or near-duplicate lemmas: search lowering/ and semantics/ before proving a helper; each helper exists once, in its most general form, in the theory where it belongs. A new theory (e.g. `lowering/exprSimArraySubscriptScript.sml`, imported by exprSimPlaces) is fine for the case's machinery; a lemma purely about source evaluation (e.g. that a pop-free expression leaves the caller's scopes unchanged) goes in a lowering theory too, not in semantics/.
4. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout override. No new `cheat`, axiom, or changed statement anywhere.
5. Commit messages end with these two lines:
   `Bot: opus (Claude Opus 5.5)`
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
   Commit only `.sml` sources you changed or added (no `.alan/`, PLAN_, LOG_, DOSSIER_ or evidence files).

**If the theorem is false as stated:** produce a HOL4 counterexample, state the tightest sufficient fix, and do NOT silently weaken the statement.

## Build

```
holbuild -j2 build exprSimPlacesTheory
```

## Background

vyper-hol proves the Vyper-to-Venom lowering correct by an expression simulation: for each expression form, the code `compile_expr` emits, run from a state related to the source state, ends related to the source result (`expr_vv_sim`), or exits as `expr_exit` allows when the source raises. This case is `a[i]` for an array base (static or dynamic) in memory (a local, or a temporary), storage, transient storage or code (an immutable, at runtime).

Source: `eval_expr` of `Subscript` evaluates the base, then the index, reads the index's value, then `select_result` / `extend_place` (semantics/vyperStateScript.sml): for a place, it reads the base's place, checks the index with `evaluate_subscripts`, and extends the place's path (memory) or computes the element's slot (`resolve_array_element`, storage). For a `Value` base it selects the element.

Lowering: `compile_subscript` lowers the base, then the index (`lower_value`), then `compile_array_subscript`: the bounds check (an ASSERT, which aborts; the source raises a RuntimeError, allowed by `expr_exit`, see exprSimArrayIndex) against the length the loader reads, and the element's pointer.

The base's `vv_holds` gives, for a pointer into a local, `local_place_at`: the pointer is the local's base plus the offset of the base's path (`mem_path_offset`). It survives the index's fragment by `local_place_at_vars_frame` / `vv_holds_vars_frame`. Without a pop in the subscript, evaluating the index leaves the caller's scopes as they were (an internal call restores them via `pop_function`; the only expression that writes a local is `Pop`), so the base's path still reads the current value; this needs a new lemma by mutual induction over evaluation (model: `eval_mutual_scope_pop_effect` in semantics/prop/vyperPlaceResultTypingScript.sml). For storage the index has no call, so storage is unchanged and liveness carries over. For an immutable, the premise excludes the constructor.

## Domain Constraints

- HOL4 via holbuild only. Default 2.5 s step timeout: a step that runs over is split or given a smaller rewrite set (the box is heavily loaded; keep steps well under the limit).
- Don't change executable definitions (lowering/defs, semantics/) or any judgment definition.
- Prefer `irule`/`drule_all` to `metis_tac`; no metis over a large search space.
- Name variables with `rename1`, never generated names. Don't use `base` as a variable name (it is a constant).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Statement | lowering/exprSimPlacesScript.sml | the cheat, the comments above it and the sibling cases |
| Case judgments | lowering/exprSimHypsScript.sml | expr_vv_case, expr_sim_case, expr_body_pre, expr_body_pre_eval_result (~810), expr_body_pre_storage_preserved (~626) |
| Core judgments | lowering/exprSimScript.sml | expr_vv_sim, vv_post, vv_holds, local_place_at, mem_path_offset_snoc (~588), mem_step_offset |
| Frames | lowering/exprSimAggregateChildrenScript.sml | local_place_at_vars_frame, vv_holds_vars_frame (~123–148) |
| Bounds check | lowering/exprSimArrayIndexScript.sml | compile_array_subscript_ok / _oob (~412/450), array_len_ok_MLOAD/SLOAD/TLOAD (~141–161) |
| Immutables | lowering/proofs/immutableWordExecutionScript.sml, lowering/exprSimLenScript.sml | compile_imm_load_word_runtime_execution (~187), immutable_holds_data (~299), compile_len_vv_case (same LocCode premise) |
| Similar proved cases | lowering/exprSimTupleScript.sml, lowering/exprSimAttributeScript.sml | compile_subscript_tuple_sim, compile_attribute_vv_sim, local_place_at_tuple_elem, local_place_at_field, select_result_memory_place |
| Storage elements | semantics/prop/vyperStoragePlaceProvenanceScript.sml, lowering/accountsRelPropsScript.sml, semantics/prop/vyperStorageLayoutSafetyScript.sml | eval_base_place_region (~190), storage_read_live_field (~727), contract_storage_well_formed_region (~266) |
| Scope effects | semantics/prop/vyperPlaceResultTypingScript.sml, semantics/prop/vyperEvalExprPreservesScopesDomScript.sml | eval_mutual_scope_pop_effect (~1709), evaluate_subscripts_append (~135), scope-domain preservation |
| Lowering | lowering/defs/exprLoweringScript.sml | compile_subscript, compile_array_subscript, compile_ptr_load |
| Source semantics | semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml | eval_expr Subscript, select_result, extend_place, read_memory_path, resolve_array_element |

## Notes

- Repo conventions: AGENTS.md at the project root.
- A popped-history snapshot keyed at the element's path cannot be read here: `extend_place` checks the index against the current value, and without a pop the current value is unchanged at the end.
