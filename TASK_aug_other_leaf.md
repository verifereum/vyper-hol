# TASK: Residual augmented assignments of the body simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/bodyAugAssignOtherScript.sml

## Theorem Statement (FROZEN)

Both are at the end of `lowering/bodyAugAssignOtherScript.sml`.

```sml
Theorem body_augassign_toplevel_aug:
  !cx ty src id bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget (src, id)) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_aug_target tops bindings (TopLevelNameTarget (src, id)) /\
    supported_expr tops e /\ expr_sim_inv cenv cx env es /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (TopLevelNameTarget (src, id)) bop e) ==>
       occurs_abi_decode_target target tops) /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e) =
      SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es

Theorem body_augassign_other_leaf:
  !cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build bodyAugAssignOtherTheory` passes at the default step limit, with both theorems proved.
2. The only `cheat`s left in `lowering/bodyAugAssignOtherScript.sml` are the two marked `ADMITTED` (`immutable_deploy_augassign_case`, `augassign_place_effectful_index_case`); leave them and their statements alone. Add no other admission, axiom or oracle.
3. Every other theorem the proofs use keeps its statement. The roots `compile_augassign_place_memory_case`, `compile_augassign_place_storage_case` and `compile_augassign_toplevel_case` are `cheat` here on purpose (other tasks prove them): use them as they are and don't edit their files.
4. Commit only `lowering/bodyAugAssignOtherScript.sml` (and a new helper theory next to it, if you add one), with the trailer `Bot: opus (Claude Opus 5.5)`. Many other files in the worktree are modified (a local overlay that admits unbuilt ancestors): never stage or commit them, nor the task or alan state files.

## Build

```sh
holbuild -j4 build bodyAugAssignOtherTheory
```

Keep checkpoints, cache and proof steps enabled; never change the tactic timeout or pass `--skip-checkpoints`.

## Background

`bodySimStmtCases.body_augassign_other` (lowering/bodySimStmtCasesScript.sml, ~line 2166, frozen) is the body simulation's case for the augmented assignments `t op= e` that its specific cases don't cover. `body_augassign_other_leaf` is that statement with one extra premise the body file will supply: the statement-level abi-decode premise of `body_stmt_ok_def` (lowering/bodySimScript.sml). `target_env_ok` comes from `body_inv_target_env_ok` (lowering/stmtSimAssignPlaceScript.sml, admitted there on purpose; use it). `stmt_frag` is the counted statement simulation (lowering/stmtSimDefsScript.sml): the source runs at `es with gas_obs := gs` for the readings the code produces.

`body_augassign_toplevel_aug` is the storage/transient word variable of any width (`supported_aug_target`), which the body file's `body_augassign_toplevel_word` covers only for full words (`supported_scalar_target`).

## Domain Constraints

- Edit only `lowering/bodyAugAssignOtherScript.sml` (or add a new helper theory next to it that it imports). Don't modify any definition, any other file, or project configuration.
- No `cheat`, axioms, oracle dependencies, or search tactics (`metis_tac`, `first_assum irule`, ...) under `TRY`/`ORELSE`.
- No `holbuild run`/`repl`, Holmake, or interactive sessions.
- `body_inv` describes the main module only; don't assume it says anything about other modules.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| target file | lowering/bodyAugAssignOtherScript.sml | the statements, decl lemmas (`supported_aug_toplevel_decl`, `supported_aug_attr_toplevel_field`), `augassign_immutable_runtime_untyped`, the admitted lemmas |
| frozen consumer | lowering/bodySimStmtCasesScript.sml | `body_augassign_other`, `body_augassign_toplevel_word` and its local helpers (`supported_scalar_target_decl`, `find_var_decl_storage_some`, `env_assignable_find_NONE`, cheats there, local, not usable) |
| top-level root | lowering/stmtSimAugAssignStorageScript.sml:268 | `compile_augassign_toplevel_case` |
| place roots | lowering/stmtSimAugAssignPlaceMemoryScript.sml, lowering/stmtSimAugAssignPlaceStorageScript.sml (ends) | `compile_augassign_place_memory_case`, `compile_augassign_place_storage_case` |
| shared aug-place facts | lowering/stmtSimAugAssignPlaceScript.sml | `aug_place_typing`, `aug_place_name_root_memory`, ... |
| target_env_ok | lowering/stmtSimAssignPlaceScript.sml | `body_inv_target_env_ok` |
| body glue | lowering/bodyAugPlaceTargetScript.sml | `aug_place_body_target_idx`, `aug_place_body_target_sim`, `aug_place_target_indices_pre`, `aug_place_supported_root_not_immutable`, `aug_place_supported_stmt_target_info` |
| target judgments | lowering/targetPlaceSimScript.sml, lowering/targetPlaceSimCasesScript.sml | `target_case_def`, `target_pre_def`, `target_indices_pre_def`, `immutable_root_def`, `target_root_def`, `target_case_all` |
| body defs | lowering/bodySimScript.sml | `body_inv_def`, `body_expr_ok_def`, `body_base_target_ok_def`, `body_stmt_ok_def` |
| body facts | lowering/bodySimExprCasesScript.sml, lowering/bodyExprPreFactsScript.sml, lowering/bodyStorageMetadataScript.sml | `body_expr_ok_case`, `stmt_expr_body_pre`, `supported_expr_body_calls`, `build_maps_variable`, `find_var_decl_storage_mem`, `supported_variable_decl_mem` |
| supported subset | lowering/supported/supportedStmtsScript.sml, supportedTargetsScript.sml, supportedDeclsScript.sml, supportedStmtTraverseScript.sml | `supported_stmt_def` (AugAssign), `supported_target_def`, `supported_aug_target_def`, `supported_target_info_def`, `supported_target_pure_def`, `supported_immutable_type_def`, `supported_stmt_expr_exists_def` |
| typing | semantics/type/vyperTypeSystemScript.sml:1131, semantics/prop/vyperTypeEnvScript.sml, semantics/prop/vyperTypeInvariantsScript.sml | `type_stmt` AugAssign, `type_place_target_TopLevelNameTarget`, `env_consistent_toplevel_storage_static`, `env_context_consistent_def`, `bare_global_assignable_complete_def` |
| expression judgments | lowering/exprSimHypsDefsScript.sml, lowering/exprSimSourceScript.sml | `expr_sim_case_def`, `expr_body_pre_def`, `expr_body_pre_gas_obs`, `expr_sim_inv_gas_obs` |
| earlier proof (non-counted frag, older defs) | alan-ref/seq890-bodySimStmtCases.sml:2423 | `body_augassign_toplevel_word`: how the decl facts come from body_inv; read for ideas only |
| proof conventions | AGENTS.md | repo rules |
