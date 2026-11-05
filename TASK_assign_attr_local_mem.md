# TASK: Prove the memory case of x.f = e on a word field of a local struct

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem body_assign_attr_local_mem:
  !cx id fld e sid fty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/bodyMemAssignAttrLocalScript.sml` with `cheat` as its
proof. All existing definitions and other theorem statements are frozen.
New proof-only helper lemmas are weakly frozen; put them in
`lowering/bodyMemAssignAttrLocalScript.sml` or a new leaf theory next to
it, never in shared ancestors.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `bodyMemAssignAttrLocalTheory` builds normally (proof steps on,
   default step limit) with no CHEAT from its own file and no parser
   warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build bodyMemAssignAttrLocalTheory
```

## Background

The statement is one subcase of the S3 (memory-safety) body induction's
plain-assignment case, dispatched in lowering/bodyMemAssignScript.sml.
The target judgment is `stmt_frag_mem` (lowering/stmtSimDefsScript.sml):
under `gas_admissible` of the statement's source action, a counted
`gas_outcome` (lowering/gasOutcomeScript.sml) on a memory-checked path
(`memory = T`): either a `gas_summary_at` with the full post/exit, or an
exemption certificate `gas_exempt_cert` (lowering/gasExemptCertScript.sml)
for the statement's own action. e's memory simulations `expr_sim_mem` /
`expr_vv_sim_mem` (lowering/exprSimMemDefsScript.sml) come from the IH
`body_expr_mem_ok cx e` (lowering/bodyMemoryPredsScript.sml) given
`expr_body_pre`.

The lowering compiles e to a value (`compile_expr`), ADDs f's byte offset
(`struct_field_offset`) to x's pointer p into dst, unwraps e's value
(`unwrap_value`; an MLOAD when e's value is located in memory) and stores
it with one MSTORE at dst. The memory obligation is the MSTORE: dst + 32
stays inside x's region, which lies below the allocation frontier
(`local_ptrs_rel` in `stmt_state_rel`); `body_field_region_frontier` /
`body_field_address_no_wrap` and `attr_add_frag_mem` /
`attr_add_prefix_mem_ok` (lowering/bodyFieldMemoryPropsScript.sml) give
the field bound and the ADD; `emit_mstore_mem_ok`
(lowering/allocaFootprintScript.sml) the store.

Worked memory twins:
- lowering/bodyMemAssignLocalWordScript.sml: `body_assign_local_word_mem`,
  the plain `x = e` word store into a local's region
  (`assign_local_word_frag_mem`, `assign_local_word_store_path_mem`).
  Follow its structure.
- lowering/bodyMemAssignTopWordScript.sml: the counted outcome
  composition (`forced_then_outcome` over e's simulation).
- lowering/bodyMemAugAssignAttrLocalScript.sml (if proved in the tree):
  `x.f op= e`, the same field ADD and MSTORE.

S1 (non-memory) twin: `body_assign_attr_local` (lowering/bodySimStmtCasesScript.sml
on commit ab7b4209c, branch bot/opus/seq-692-s1-stmts-decls: `git show
ab7b4209c:lowering/bodySimStmtCasesScript.sml`) via
`compile_assign_attr_local_case` (`git show
ab7b4209c:lowering/stmtSimAssignAttrScript.sml`; its header explains the
split). The stmtSimAssignAttr file in this tree is an older version, built
locally with its proofs admitted by an overlay; its source-side and
code-side lemma statements (`eval_assign_attr_local`,
`assign_attr_local_code_parts`, `stmt_state_rel_write_field`,
`attribute_type_struct_field`, ...) are fine to use. Where the S1
commit's counted source-side helpers (`assign_attr_local_admissible_*`,
`assign_attr_local_continuation_*`, `assign_attr_local_exempt`, ...) are
missing here, copy the ones you need into the target file as `[local]`
`*_mem_src` theorems, generalising `gas_marked_path F` /
`gas_marked_exec F` to a `memory` variable. Don't edit the stmtSim* files.

## Domain Constraints

- No executable definition changes, added assumptions, admissions,
  timeout overrides, or search tactics wrapped in `TRY`/`ORELSE`.
- Keep every full post, frame and storage agreement; use counted GAS paths
  and all source gas tails; don't discard exemption certificates.
- Don't edit files outside `lowering/bodyMem*`/`lowering/body*Memory*` and
  new leaf theories; don't edit the stmtSim* theories.
- At most `-j4`.

## Available Resources

- Target: `lowering/bodyMemAssignAttrLocalScript.sml`; dispatch `lowering/bodyMemAssignScript.sml`
- Judgments: `lowering/stmtSimDefsScript.sml`, `lowering/exprSimMemDefsScript.sml`,
  `lowering/bodyMemoryPredsScript.sml`, `lowering/bodyMemoryDefsScript.sml`
- Counted outcomes: `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`,
  `lowering/gasSummaryComposeScript.sml`, `lowering/gasExemptCertScript.sml`,
  `lowering/stmtSimForcedScript.sml`
- Worked memory twins: `lowering/bodyMemAssignLocalWordScript.sml`,
  `lowering/bodyMemAssignTopWordScript.sml`
- Field address, ADD, field reads on a memory path: `lowering/bodyFieldMemoryPropsScript.sml`,
  `lowering/bodyFieldMemoryScript.sml`, `lowering/bodyAttributeMemoryScript.sml`
- Value unwrap on a memory path: `lowering/exprSimMemUnwrapScript.sml`,
  `lowering/bodyRhsRoomMemoryScript.sml` (`expr_sim_mem_room`)
- Store footprint: `lowering/allocaFootprintScript.sml` (`emit_mstore_mem_ok`)
- S1 twins: `lowering/bodySimStmtCasesScript.sml`, `lowering/stmtSimAssignAttrScript.sml`
  (and their versions at commit ab7b4209c, above)
- Source semantics: `semantics/vyperInterpreterScript.sml` (`eval_stmt` Assign)
