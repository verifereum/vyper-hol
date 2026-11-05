# TASK: array subscript simulation, framed base

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimSubscriptArrayScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

In `lowering/exprSimSubscriptArrayScript.sml`, currently `cheat`:

```sml
Theorem compile_subscript_array_framed_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (!t r t'. eval_expr cx idx t = (INL r, t') ==>
              t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
    ((~cenv.ce_is_ctor /\
      !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
     ((?n. bd = Fixed n) /\
      (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
      !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory)) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

`compile_subscript_array_place_base_case` in the same file is deliberately admitted and out of scope (its comment says why the current judgments can't carry it); leave it and `compile_subscript_array_case` unchanged.

## Completion Criteria

1. `holbuild -j4 build exprSimSubscriptArrayTheory exprSimPlacesTheory` passes with no CHEAT warning for `compile_subscript_array_framed_base_case` (`compile_subscript_array_place_base_case` keeps its).
2. An `array_len_ok` lemma for a dynamic array in code at runtime (compile_imm_load_word's DLOAD) lives in `lowering/exprSimSubscriptArrayFramedScript.sml`, not in `exprSimArrayIndexScript.sml` (`array_len_ok_DLOAD` is there now; add nothing to exprSimArrayIndex).
3. No duplicate or near-duplicate lemmas: search `lowering/` and `semantics/` before proving a helper; each helper exists once, in its most general form. Put this case's machinery in new leaf theories (e.g. `lowering/exprSimSubscriptArrayFramedScript.sml`) that `exprSimSubscriptArray` imports (it already imports `exprSimSubscriptArrayFramed`, and the theories build through that import; add no `holproject.toml` roots); don't edit shared ancestors.
4. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout override. No new `cheat`, axiom, or changed statement anywhere. Don't change any definition in `semantics/`, `frontend/`, `lowering/defs/`, `venom/`, or any judgment (`exprSim*Defs`, `exprSimHyps*`, `loweringPosts`, `bodySim*`, `*Main`).
5. Commit messages end with these two lines:
   `Bot: opus (Claude Opus 5.5)`
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
   Commit only `.sml` sources you changed or added . Never commit the 30 files the working tree has modified as a local admission overlay (they're listed in `alan-ref/overlaid.txt`), nor `alan-ref/`, `.alan/`, PLAN_, LOG_, STATE_, LEARNINGS_, DOSSIER_ or evidence files.

**If the theorem is false as stated:** produce a HOL4 counterexample, state the tightest sufficient fix, and do NOT silently weaken the statement.

## Build

```
holbuild -j4 build exprSimSubscriptArrayTheory exprSimPlacesTheory
```

## Background

vyper-hol proves the Vyper-to-Venom lowering correct by an expression simulation: for each expression form, the code `compile_expr` emits, run from a state related to the source state, ends related to the source result (`expr_vv_sim`, in the counted `gas_outcome` form), or exits as `expr_exit` allows when the source raises. This case is `a[i]` for an array base (static or dynamic) in memory (a local, or a temporary), storage, transient storage or code (an immutable: the staged buffer in the constructor, the data section at runtime), restricted to an index that leaves the source locals and immutables unchanged, and a base that is an immutable at runtime (in the data section) or a static array with no dynamic array inside it in memory (a local or a temporary allocation), whose source result is no storage place. The comment on the admitted residual says why the other cases are out of reach of the current judgments; don't try to prove them.

Source: `eval_expr` of `Subscript` (semantics/vyperInterpreterScript.sml) evaluates the base, then the index, reads the index's value, then `select_result` / `extend_place` (semantics/vyperStateScript.sml): for a place it reads the base's place, checks the index with `evaluate_subscripts`, and extends the place's path (memory, immutable) or computes the element's slot (`extend_storage_place`, storage). For a `Value` base it selects the element.

Lowering: `compile_subscript` (lowering/defs/exprLoweringScript.sml) lowers the base, then the index (`lower_value`), then `compile_array_subscript`: the bounds check (an ASSERT, which aborts; the source raises a RuntimeError, allowed by `expr_exit`, see exprSimArrayIndex) against the length the loader (`compile_ptr_load`) reads, and the element's pointer.

`compile_subscript_array_case` (same file) dispatches to this theorem and the admitted residual; it is consumed by `compile_subscript_case` in `lowering/exprSimPlacesScript.sml`.

## Domain Constraints

- Follow `AGENTS.md` at the project root (proof conventions for this repo).
- Default step timeout (2.5 s). A step near it is a proof performance bug: split it or cut the rewrite set.
- The working tree carries an uncommitted local overlay that admits the proofs of ~30 shared theories not yet repaired on this branch (listed in `alan-ref/overlaid.txt`). Use their statements freely; don't edit, fix or commit them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target and its split | `lowering/exprSimSubscriptArrayScript.sml` | The theorem, its comment, and the admitted subcases' comments (what is deliberately out of scope) |
| Dispatcher consumer | `lowering/exprSimPlacesScript.sml` | `compile_subscript_case` and `compile_expr_array_subscript`-style unfolding of `compile_subscript` |
| Judgments | `lowering/exprSimDefsScript.sml`, `lowering/exprSimHypsDefsScript.sml` | `expr_vv_sim`, `expr_sim`, `expr_exit`, `expr_vv_case`, `expr_sim_case`, `expr_body_pre`, `expr_sim_inv` |
| Posts | `lowering/loweringPostsScript.sml` | `vv_post`, `vv_holds`, `vv_at`, `expr_post`, `locals_kept`, `wb_frame`, `storage_holds`, `immutable_holds`, `sub_layout` |
| Bounds check | `lowering/exprSimArrayIndexScript.sml` | `compile_array_subscript_ok`/`_oob`, `array_len_ok_*` |
| Proven sibling cases (templates) | `lowering/exprSimTupleScript.sml`, `lowering/exprSimAttributeScript.sml`, `lowering/exprSimAttributeFieldsScript.sml` | Tuple subscript and attribute in the counted form: base then selection, memory/storage/code |
| Code reads | `lowering/exprSimUnwrapScript.sml` (`immutable_holds_dload`, `immutable_holds_iload`), `lowering/exprSimLenScript.sml`, `lowering/exprSimCopyScript.sml` | ILOAD/DLOAD of an immutable word |
| Storage frames | `lowering/accountsRelPropsScript.sml` | `storage_range_agree`, `storage_range_agree_of_live` |
| Source facts | `semantics/prop/` (e.g. `vyperPlaceResultTypingScript.sml`, `vyperStatePreservationScript.sml`, `vyperImmutablesPreservationScript.sml`, `vyperStoragePlaceProvenanceScript.sml`) | Evaluation invariants: scope restoration across calls, immutables/storage preservation |
| Type invariants | `semantics/prop/vyperTypeInvariantsScript.sml` | `bare_global_assignable_complete` (no immutable writes at runtime) |
| Earlier attempt, OLD BASE | `alan-ref/seq616-old-base/` | An earlier prover run on the no-pop subcase over a base ~890 commits older (frame_exec judgments instead of the counted gas_outcome form; `storage_holds` asked `storage_read_live` then). Its scripts are renamed `.sml.txt`; its DOSSIER/LEARNINGS record what worked and what didn't. Reuse ideas and source-side lemmas after checking them against the current definitions; don't copy blindly. |
| HOL4 sources | `.holbuild/src/` is off limits; use theory names via `DB.find` in scratch probes | |

## Notes

- `nocalls` may be F: the index may contain internal calls.
- The case split in `compile_subscript_array_case` already builds; only `compile_subscript_array_framed_base_case` is yours.
