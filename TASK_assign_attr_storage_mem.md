# TASK: Prove the memory case of self.x.f = e on a word field of a storage or transient struct

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem body_assign_attr_storage_mem:
  !cx nsid fld e fty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld /\
    type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
      SOME (Type fty) /\
    is_word_type fty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/bodyMemAssignAttrStorageScript.sml` with `cheat` as its
proof. All existing definitions and other theorem statements are frozen.
New proof-only helper lemmas are weakly frozen; put them in
`lowering/bodyMemAssignAttrStorageScript.sml` or a new leaf theory next to
it, never in shared ancestors.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `bodyMemAssignAttrStorageTheory` builds normally (proof steps on,
   default step limit) with no CHEAT from its own file and no parser
   warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build bodyMemAssignAttrStorageTheory
```

## Background

The statement is one subcase of the S3 (memory-safety) body induction's
plain-assignment case, dispatched in lowering/bodyMemAssignScript.sml.
The target judgment is `stmt_frag_mem` (lowering/stmtSimDefsScript.sml):
under `gas_admissible` of the statement's source action, a counted
`gas_outcome` (lowering/gasOutcomeScript.sml) on a memory-checked path
(`memory = T`): either a `gas_summary_at` with the full post/exit, or an
exemption certificate `gas_exempt_cert` (lowering/gasExemptCertScript.sml)
for the statement's own action. e's memory simulation `expr_sim_mem`
(lowering/exprSimMemDefsScript.sml) comes from the IH `body_expr_mem_ok cx e`
(lowering/bodyMemoryPredsScript.sml) given `expr_body_pre`.

The lowering evaluates e, ADDs f's slot offset (`struct_field_offset_slots`)
to x's slot, unwraps the value and stores it with one SSTORE or TSTORE.
None of this touches memory, so it composes like the proved top-level word
leaf.

Worked memory twins:
- lowering/bodyMemAssignTopWordScript.sml: `body_assign_toplevel_word_mem`
  via `compile_assign_storage_typed_stmt_frag_mem`, the plain
  `self.x = e` word store (`forced_then_outcome` over e's `expr_sim_mem`,
  then `assign_storage_store_path_mem`). Follow its structure.
- lowering/bodyMemAugAssignAttrStorageScript.sml (if present in the tree):
  `self.x.f op= e`, the same field slot ADD then a store at an operand
  slot, on a memory-safe path.

S1 (non-memory) twin: `body_assign_attr_storage` (lowering/bodySimStmtCasesScript.sml
on commit ab7b4209c, branch bot/opus/seq-692-s1-stmts-decls: `git show
ab7b4209c:lowering/bodySimStmtCasesScript.sml`) via
`compile_assign_attr_storage_case` (`git show
ab7b4209c:lowering/stmtSimAssignAttrStorageScript.sml`). The
stmtSimAssignAttrStorage file in this tree is an older version, built
locally with its proofs admitted by an overlay; its source-side and
code-side lemma statements (`eval_assign_attr_toplevel`,
`assign_attr_storage_code_parts`, `struct_field_slot_alookup`, ...) are
fine to use. Where the S1 commit's counted source-side helpers
(`eval_assign_attr_toplevel_action`, `assign_attr_storage_source_counted`,
...) are missing here, copy the ones you need into the target file as
`[local]` `*_mem_src` theorems, generalising `gas_marked_path F` /
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

- Target: `lowering/bodyMemAssignAttrStorageScript.sml`; dispatch `lowering/bodyMemAssignScript.sml`
- Judgments: `lowering/stmtSimDefsScript.sml`, `lowering/exprSimMemDefsScript.sml`,
  `lowering/bodyMemoryPredsScript.sml`, `lowering/bodyMemoryDefsScript.sml`
- Counted outcomes: `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`,
  `lowering/gasSummaryComposeScript.sml`, `lowering/gasExemptCertScript.sml`,
  `lowering/stmtSimForcedScript.sml`
- Worked memory twins: `lowering/bodyMemAssignTopWordScript.sml`,
  `lowering/bodyMemAssignLocalWordScript.sml`
- Value unwrap on a memory path: `lowering/exprSimMemUnwrapScript.sml`,
  `lowering/bodyRhsRoomMemoryScript.sml` (`expr_sim_mem_room`)
- S1 twins: `lowering/bodySimStmtCasesScript.sml`, `lowering/stmtSimAssignAttrStorageScript.sml`
  (and their versions at commit ab7b4209c, above)
- Source semantics: `semantics/vyperInterpreterScript.sml` (`eval_stmt` Assign)
