# TASK: Counted memory simulation of a struct field of a local Name

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

Two theorems; the second may use the first.

```sml
(* lowering/bodyFieldValueMemoryScript.sml *)
Theorem compile_attribute_name_body_vv_sim_mem:
  !ctx func cenv cx env ty ann sid id fld es.
    expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es ==>
    expr_vv_sim_mem ctx func cenv cx ty
      (Attribute ann (Name (StructT sid) id) fld) es

(* lowering/bodyFieldForceMemoryScript.sml *)
Theorem compile_attribute_name_body_sim_mem:
  !ctx func cenv cx env ty ann sid id fld es.
    expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es ==>
    expr_sim_mem ctx func cenv cx ty (Attribute ann (Name (StructT sid) id) fld) es
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
All existing definitions and other theorem statements are frozen. New
proof-only helper lemmas are weakly frozen.

## Completion Criteria

1. Both statements proved without admissions or added assumptions.
2. `bodyFieldForceMemoryTheory` (which imports `bodyFieldValueMemoryTheory`)
   builds normally (proof steps on, default step limit) with no parser
   warnings, and neither target script contains `cheat`.
3. Reuse existing helpers rather than duplicating them. New helpers go in
   `lowering/bodyFieldMemoryPropsScript.sml`, the two target scripts, or new
   leaf theories next to them in `lowering/`; don't edit any other existing
   theory.

## Build

```sh
holbuild -j4 build bodyFieldForceMemoryTheory
```

## Background

`expr_vv_sim_mem` / `expr_sim_mem` (`lowering/exprSimMemDefsScript.sml`) are
the memory-safe, gas-counted expression simulations: a `gas_outcome` over
`gas_path_mem`, with `vv_post` / `expr_post`, `alloca_history` and
`vs_alloca_next` monotonicity. They replaced the older uncounted
`frag_exec_mem` form. Both target scripts still hold their old
`frag_exec_mem`-style proofs, which show the intended argument but no longer
fit the counted definitions; rewrite them.

The lowering of `Attribute ann (Name (StructT sid) id) fld` is the Name's
code (no instructions: a pointer to the local) followed by one `ADD` of the
base pointer and the field offset (`body_attribute_name_compile`); the
force version adds `unwrap_value`, one `MLOAD` for a word-typed field and
nothing otherwise. The source evaluates the Name and then `select_result`
(`body_attribute_name_eval`).

The old force proof used `compile_attribute_name_body_capacity_mem`, which
lives in `bodyFieldMemoryScript.sml`, a theory that imports the targets and
is out of scope; it is unreachable from them. Whatever capacity fact the
`MLOAD` needs must come from a helper in scope (give it a different name).

Proved counted siblings to follow:
- `lowering/bodyNameValueMemoryScript.sml`: `compile_name_body_vv_sim_mem`
  (the Name child, counted).
- `lowering/bodyCalldataMemoryScript.sml`: a straight-line instruction as a
  counted prefix (`run_inst_seq_gas_path_mem`, `gas_value_prefix`).
- `lowering/bodyNameWordMemoryScript.sml`: counted `MLOAD` of a word local.
- `lowering/exprSimMemoryStackScript.sml`, `lowering/exprSimMemoryValuesScript.sml`:
  how `gas_outcome` goals are opened and closed.

## Domain Constraints

- No executable or semantics definition changes, no added assumptions, no
  admissions, no new axioms.
- holbuild's per-step tactic timeout stays at its default; never wrap
  `metis_tac` or other search in `TRY`/`ORELSE`.
- No `let` in theorem statements.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| targets | `lowering/bodyFieldValueMemoryScript.sml`, `lowering/bodyFieldForceMemoryScript.sml` | frozen theorems, old proofs |
| field props | `lowering/bodyFieldMemoryPropsScript.sml` | `body_attribute_name_compile`/`_eval`/`_pre`, `attr_add_run_post`, `attr_add_history`, `attr_add_frag_mem_at` (uncounted), `body_attr_memory_vv_post`, `body_base_memory_post_read_struct`, `body_word_load_run_post`, `body_unwrap_memory_read_mem` (uncounted), `body_attribute_name_capacity` |
| counted defs | `lowering/exprSimMemDefsScript.sml`, `lowering/gasOutcomeScript.sml` | `expr_vv_sim_mem`, `expr_sim_mem`, `gas_outcome` |
| gas composition | `lowering/gasSummaryComposeScript.sml`, `lowering/gasSummaryScript.sml`, `lowering/gasNormalPrefixScript.sml`, `lowering/gasExemptCertScript.sml` | `gas_marked_exec_bind_normal`/`_exception`, `gas_summary_at`, `gas_value_prefix`, exempt certificates |
| gas paths with memory | `lowering/fragGasSeqMemScript.sml`, `lowering/fragGasPathMemScript.sml` | `straight_line_mem_edge`, `run_inst_seq_gas_path_mem`, `gas_path_mem_then` |
| memory read / force | `lowering/exprSimMemoryReadScript.sml`, `lowering/exprSimMemoryForceScript.sml`, `lowering/exprSimMemorySourceScript.sml` | `unwrap_memory_marked_read`, `expr_sim_of_vv_sim_memory`, `force_exempt_cert` |
| name facts | `lowering/bodyNameMemoryFactsScript.sml` | `body_name_source_region` |
| field layout | `lowering/exprSimFieldLayoutScript.sml`, `lowering/exprSimAttributeFieldsScript.sml`, `lowering/exprSimAttributePropsScript.sml` | `struct_fields_layout`, `select_attr_read`, `popped_keys_indexed_not_at_field`, `attribute_type_evaluates` |
| posts | `lowering/loweringPostsScript.sml` | `vv_post`, `vv_at`, `expr_post`, `expr_exit` |
| unwrap props | `lowering/exprSimUnwrapPropsScript.sml`, `lowering/exprSimUnwrapScript.sml` | `vv_post_read_result`, `vv_post_failed_read`, `expr_post_of_vv_post_memory` |
| source semantics | `semantics/vyperInterpreterScript.sml` | `evaluate_def` (Attribute, Name), `select_result` |
| lowering defs | `lowering/defs/exprLoweringScript.sml` | `compile_expr`, `compile_attribute`, `unwrap_value`, `lower_value` |

## Notes

Some theories outside this task's cone are locally admitted by an
uncommitted overlay (hidden from git); their admissions show up as CHEAT
tags on theorems that depend on them (e.g. `mem_field_offset_layout`,
`vv_post_failed_read`). That is expected; leave those files alone and never
commit them. Only `cheat`s in the target scripts and your new helpers count.
