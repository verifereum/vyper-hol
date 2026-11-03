# TASK: Align assignment helpers with the existing body supply domain

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem body_assign_local_rhs_pre[local]:
  !cx id e tops bindings ctx cenv env env' ret_ty es ty.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\ source_supply es /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty ==>
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    expr_body_pre cenv cx env e es
```

```sml
Theorem body_assign_local_memory:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\ source_supply es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res, es') /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (expr_type e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      es res es'
```

```sml
Theorem body_assign_attr_local[local]:
  !cx id fld e tops ctx func cenv env env' ret_ty lctx RetQ es res es' sid
   fty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ source_supply es /\
    type_stmt env ret_ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      es = (res, es') /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      es res es'
```

```sml
Theorem body_assign_attr_storage[local]:
  !cx src id fld e tops ctx func cenv env env' ret_ty lctx RetQ es res es'
   fty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ source_supply es /\
    supported_storage_field_write tops (src, id) fld /\
    type_place_target env
      (AttributeTarget (TopLevelNameTarget (src, id)) fld) =
      SOME (Type fty) /\
    is_word_type fty /\
    type_stmt env ret_ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) = SOME env' /\
    stmt_exprs_ok cenv
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e)) /\
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e)) es res es'
```

```sml
Theorem body_augassign_attr_local[local]:
  !cx ty id fld bop e tops ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' =
         (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ source_supply es /\
    type_stmt env ret_ty
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) =
      SOME env' /\
    stmt_exprs_ok cenv
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) /\
    eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
      es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      es res es'
```

```sml
Theorem body_augassign_toplevel_word[local]:
  !cx ty src id bop e tops ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget (src, id)) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_scalar_target tops (src, id) /\
    supported_expr tops e /\ expr_sim_inv cenv cx env es /\ source_supply es /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e) =
      SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) /\
    eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e) es =
      (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es res es'
```

```sml
Theorem body_annassign_rhs_pre[local]:
  !cenv cx env e es tops id typ ctx.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ source_supply es /\ well_typed_expr env e /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) ==>
    expr_body_pre cenv cx env e es
```

```sml
Theorem body_annassign_declared_rhs[local]:
  !cenv cx env e es tops id typ st c st1 ctx func.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ source_supply es /\ well_typed_expr env e /\
    id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    body_expr_ok cx e /\ declare_local cenv id typ st = (c,st1) ==>
    expr_sim ctx func c cx (expr_type e) e es /\
    expr_vv_sim ctx func c cx (expr_type e) e es
```

```sml
Theorem body_annassign_memory:
  !cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res
   es'.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    expr_sim_inv cenv cx env es /\ source_supply es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    eval_stmt cx (AnnAssign id typ e) es = (res, es') /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    (expr_type e = typ \/ is_bytestring_type typ \/
     has_length_word typ /\ is_empty_value_expr e) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e)) es res es'
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
Every other existing theorem header in the two allowed files is also frozen, byte-for-byte, as recorded in `.agent-files/seq240/assignment-supply-frozen-headers.json`.

## Completion Criteria

1. Both bodySimStmtCasesTheory and bodySimDeclCasesTheory build with the nine amended helpers proved.
2. No new admissions; preserve the inherited admitted residuals and their exact statements.
3. No definition or stage/top-level statement changes. All existing headers match the snapshot.

## Build

`holbuild --max-heap 8000 -j2 build bodySimStmtCasesTheory bodySimDeclCasesTheory`

## Background

The body domain already includes source_supply. Nine internal assignment/declaration helper statements omitted it while their expression-precondition dependency requires it. The exact additions were independently audited PROVABLE and approved. All callers of the two exported helpers already carry the supply fact. The public body simulation interfaces stay unchanged.

## Domain Constraints

- Modify ONLY lowering/bodySimStmtCasesScript.sml and lowering/bodySimDeclCasesScript.sml.
- All existing statements are FROZEN at the amended source in this task and snapshot, including local statements and inherited admitted residuals. No more premises or statement changes.
- Keep executable definitions byte-identical. Do not introduce definitions or axioms.
- Keep inherited admitted residuals unchanged; this task does not complete those pending compiler cases. Add no admissions or suspend labels to bypass proof repair.
- New consumed helpers may be added only as [local] when needed by a concrete proof. Do not add unconsumed machinery.
- Retain original proof code until replaced by a checked proof; no temporary cheat.
- No TRY/ORELSE wrapping search, timeout increases, interactive HOL or Holmake.
- Use shared holbuild/default resources, at most -j2. No parallel build in this worktree outside your one build tool.
- No edits to task scaffolding or .alan state. Commits end with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- lowering/bodySimStmtCasesScript.sml: the six amended assignment/augassign helpers and existing case consumers.
- lowering/bodySimDeclCasesScript.sml: the three amended declaration helpers and case consumers.
- lowering/bodySimScript.sml: body_stmt_ok_def and body_stmts_ok_def carry source_supply.
- lowering/bodySimMainScript.sml: unchanged body_stmt_sim/body_stmts_sim interface consumers.
- lowering/exprSimHypsScript.sml: expr_body_pre_def and post-evaluation supply transport.
- lowering/bodyStoragePreservationScript.sml: already checked storage/supply mutual boundary.
- lowering/memoryLocalRhsPropsScript.sml: already checked lowered-memory typing domain.

## Notes

The initial failure was body_assign_local_rhs_pre at its stmt_expr_body_pre application. The nine exact amended headers were checked independently by a read-only family/producer/consumer audit. The newly amended headers have not yet been rebuilt after the added conjunct; their types and premise syntax are the existing source_supply domain used throughout these files. All other source statements must remain unchanged, especially bodySimMain, inherited admitted residuals, and pure/frame helpers.
