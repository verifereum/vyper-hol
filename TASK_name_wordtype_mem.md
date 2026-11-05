# TASK: Memory-safe lowering of address and bytesM local names

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem compile_name_wordtype_body_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es /\
    is_word_type ann /\ ~word_value_type ann ==>
    expr_sim_mem ctx func ce cx ty (Name ann id) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/bodyNameWordTypeMemoryScript.sml`. All existing
definitions and other theorem statements are frozen. New proof-only helper
lemmas are weakly frozen.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `bodyNameWordTypeMemoryTheory` builds normally (proof steps on, default
   step limit) with no CHEAT and no parser warnings.
3. Reuse existing helpers rather than duplicating them. New helpers go in
   `lowering/bodyNameWordTypeMemoryScript.sml` or a new leaf theory next to
   it; don't edit shared ancestors (anything outside `lowering/body*Memory*`).

## Build

```sh
holbuild -j4 build bodyNameWordTypeMemoryTheory
```

## Background

`is_word_type ann /\ ~word_value_type ann` leaves exactly the local names of
type `address` and `bytesM` (m <= 32). Their lowering is the same as for
other word locals: `lower_value compile_expr` gives one `MLOAD` from the
local's pointer variable (`lower_value_name_word` needs only
`is_word_type`). The source values are `AddressV` / `BytesV`, which are not
`word_value`s, so the existing word-name lemmas (`eval_name_word`,
`step_name_word`, `body_word_name_region`, `name_word_post`, all on
`word_value`) don't apply directly.

`expr_sim_mem` (`lowering/exprSimMemDefsScript.sml`) is the memory-safe,
gas-counted expression simulation: `gas_outcome` over `gas_path_mem`, with
`expr_post`, `alloca_history` and `vs_alloca_next` monotonicity.
`expr_sim_mem_values` (`lowering/exprSimMemoryValuesScript.sml`) reduces it
to a `gas_value_prefix` for expressions that always produce a value.

Proved siblings to follow:
- `lowering/bodyNameWordMemoryScript.sml`: `compile_name_word_body_sim_mem`,
  the same theorem for `word_value_type ann` (numeric, bool, flag).
- `lowering/exprSimNameScript.sml`: `compile_name_other_sim`, the
  non-memory (`expr_sim`) version covering these types, via
  `expr_sim_of_vv_sim_memory` (`lowering/exprSimMemoryForceScript.sml`) and
  `unwrap_memory_marked_read` (`lowering/exprSimMemoryReadScript.sml`).
- `lowering/bodyNameValueMemoryScript.sml`: `compile_name_body_vv_sim_mem`.

## Domain Constraints

- No executable or semantics definition changes, no added assumptions, no
  admissions, no new axioms.
- holbuild's per-step tactic timeout stays at its default; never wrap
  `metis_tac` or other search in `TRY`/`ORELSE`.
- No `let` in theorem statements.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| target | `lowering/bodyNameWordTypeMemoryScript.sml` | the frozen theorem |
| word sibling | `lowering/bodyNameWordMemoryScript.sml` | same proof for word_value types; `body_name_load_history`, `body_name_word_counted` (local) |
| region facts | `lowering/bodyNameMemoryFactsScript.sml` | `body_name_source_region`, `body_word_name_region`, `body_word_name_MLOAD_frontier` |
| MLOAD frontier | `lowering/bodyMemoryDefsScript.sml` | `body_local_ptr_MLOAD_frontier`, `local_region` |
| S1 name proofs | `lowering/exprSimNameWordScript.sml`, `lowering/exprSimNameValueScript.sml`, `lowering/exprSimNameScript.sml` | counted non-memory versions |
| memory read | `lowering/exprSimMemoryReadScript.sml`, `lowering/exprSimMemoryForceScript.sml` | generic unwrap of a memory pointer |
| word encoding | `lowering/exprSimPropsScript.sml` | `val_in_memory_word_type` (address, bytesM) |
| sizes | `lowering/defs/valueEncodingScript.sml` | `type_memory_size` (BaseTV _ = 32) |
| expr_post / expr_val_rel | `lowering/loweringPostsScript.sml` | post-condition |
| gas paths | `lowering/fragGasPathMemScript.sml`, `lowering/gasNormalPrefixScript.sml`, `lowering/gasSummaryScript.sml` | gas_path_mem, gas_value_prefix |
| source semantics | `semantics/vyperInterpreterScript.sml` | `evaluate_def` Name case |
| lowering defs | `lowering/defs/exprLoweringScript.sml`, `lowering/defs/compileEnvScript.sml` | `compile_expr`, `unwrap_value`, `is_word_type` |

## Notes

Some theories outside this task's cone are locally admitted by an
uncommitted overlay (their files show as modified in `git status`); leave
them alone and never commit them.
