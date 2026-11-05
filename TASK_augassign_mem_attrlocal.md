# TASK: Prove the memory case of x.f op= e on a word field of a local struct

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem body_augassign_attr_local_mem:
  !cx ty id fld bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/bodyMemAugAssignAttrLocalScript.sml` with `cheat` as its proof. All existing
definitions and other theorem statements are frozen. New proof-only helper
lemmas are weakly frozen; put them in `lowering/bodyMemAugAssignAttrLocalScript.sml` or a new
leaf theory next to it, never in shared ancestors.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `bodyMemAugAssignAttrLocalTheory` builds normally (proof steps on, default step limit) with
   no CHEAT from its own file and no parser warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build bodyMemAugAssignAttrLocalTheory
```

## Background

The statement is one subcase of the S3 (memory-safety) body induction's
augmented-assignment case, dispatched in lowering/bodyMemAugAssignScript.sml.
The target judgment is `stmt_frag_mem` (lowering/stmtSimDefsScript.sml):
under `gas_admissible` of the statement's source action, a counted
`gas_outcome` (lowering/gasOutcomeScript.sml) on a memory-checked path
(`memory = T`): either a `gas_summary_at` with the full post/exit, or an
exemption certificate `gas_exempt_cert` (lowering/gasExemptCertScript.sml)
for the statement's own action. e's memory simulation `expr_sim_mem`
(lowering/exprSimMemDefsScript.sml) comes from the IH `body_expr_mem_ok cx e`
(lowering/bodyMemoryPredsScript.sml) once the target's place, value and type
are read.

`x op= e` is NOT literally `x = x op e` at the counted level: the
exemption certificate is syntactic in the source action, so a certificate
for `Builtin ty (Bop bop) [Name ty id; e]` does not transfer to
`eval_stmt cx (AugAssign ...)`. Compose the statement's own pieces instead:
the target read (no gas; rewrite the source's place/read/type prefix, which
only reads state, into a form the certificate rules cover, e.g. via
`gas_exempt_cert_get_scopes`/`_bind_value`), then e's `expr_sim_mem`
(forced: `bind (eval_expr cx e) (read_result cx)`), then the operator's
`binop_frag_mem` (lowering/bodyBinopFragMemoryScript.sml,
lowering/bodyBinopFamiliesMemoryScript.sml; `binop_frag_typed_mem` as used in
lowering/bodyBopMemoryScript.sml `body_bop_word_mem`), then the store.
`compile_bop_typed_sim_mem` (lowering/bodyBinopFragMemoryScript.sml) is the
closest worked composition of operand simulation + operator on this
interface; lowering/stmtSimForcedScript.sml (`forced_then_*`) composes a
forced expression with a gas-free continuation.

Worked memory composition for this exact shape: the local and top-level
word leaves are proved, in lowering/bodyMemAugAssignLocalScript.sml and
lowering/bodyMemAugAssignTopWordScript.sml. Follow their structure
(`compile_augassign_*_mem` with suspend/Resume phases: load, rhs from
`expr_sim_mem` with the exempt branch, operator via `binop_frag_typed_mem`
and `binop_frag_val_mem_def`/`binop_frag_mem_def`, store, post frames
chained with `not_fresh_at_mono` and `return_buf_frame_frame`).

The S1 proof this ports is on commit e80ec2cf7 (branch
bot/opus/seq-692-s1-stmts-decls): `git show
e80ec2cf7:lowering/stmtSimAugAssignAttrScript.sml`. Its source-side helpers
are NOT in this tree (the stmtSimAugAssignAttr here is an older, different
file), so copy the ones you need into the target file as `[local]`
`*_mem_src` theorems, generalising `gas_marked_path F`/`gas_marked_exec F`
to a `memory` variable, as the two proved leaves do. Don't edit the
stmtSimAugAssign* files.

Missing piece to build: the MSTORE of the result at the field address
`p + offset` on a memory-safe path (the field analogue of
`assign_local_word_store_path_mem` in lowering/bodyMemAssignLocalWordScript.sml).
Use `emit_mstore_mem_ok` with the bound from `body_field_region_frontier`
(lowering/bodyFieldMemoryPropsScript.sml); the ADD is `attr_add_frag_mem`/
`attr_add_prefix_mem_ok` there; the MLOAD of the field on a memory path
via `body_read1_frag_mem` (lowering/bodyUnwrapMemoryScript.sml) or the
`compile_attribute_name_body_*_mem` lemmas.

S1 twin: `body_augassign_attr_local` (lowering/bodySimStmtCasesScript.sml)
via `compile_augassign_attr_local_case` (lowering/stmtSimAugAssignAttrScript.sml),
whose header explains the split: ADD of f's offset to p (dst), MLOAD dst,
e, `compile_binop`, MSTORE dst; dst must survive e's and the operator's
code. Source: `eval_augassign_attr_local`, `augassign_attr_local_place`.
Code: `augassign_attr_local_code_parts`. Memory store into a local region:
lowering/bodyMemAssignLocalWordScript.sml and lowering/bodyMemAssignAttrLocalScript.sml
(plain `x.f = e`'s memory case, if proved by the time you run).

## Domain Constraints

- No executable definition changes, added assumptions, admissions,
  timeout overrides, or search tactics wrapped in `TRY`/`ORELSE`.
- Keep every full post, frame and storage agreement; use counted GAS paths
  and all source gas tails; don't discard exemption certificates.
- Don't edit files outside `lowering/bodyMem*`/`lowering/body*Memory*` and
  new leaf theories; don't edit the stmtSimAugAssign* theories.
- At most `-j4`.

## Available Resources

- Target: `lowering/bodyMemAugAssignAttrLocalScript.sml`; dispatch `lowering/bodyMemAugAssignScript.sml`
- Judgments: `lowering/stmtSimDefsScript.sml`, `lowering/exprSimMemDefsScript.sml`,
  `lowering/bodyMemoryPredsScript.sml`, `lowering/bodyMemoryDefsScript.sml`
- Counted outcomes: `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`,
  `lowering/gasSummaryComposeScript.sml`, `lowering/gasExemptCertScript.sml`
- Worked memory twins (plain assignment): `lowering/bodyMemAssignLocalWordScript.sml`,
  `lowering/bodyMemAssignTopWordScript.sml`
- Operator: `lowering/bodyBinopFragMemoryScript.sml`, `lowering/bodyBinopFamiliesMemoryScript.sml`,
  `lowering/bodyBopMemoryScript.sml`
- S1 twins: `lowering/bodySimStmtCasesScript.sml`, `lowering/stmtSimAugAssign*Script.sml`
- Source semantics: `semantics/vyperInterpreterScript.sml` (`eval_stmt` AugAssign)
