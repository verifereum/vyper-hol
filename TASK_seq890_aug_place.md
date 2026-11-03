# TASK: Prove the augmented assignment to a field or element place

## Meta
Status: ready
Priority: P1
Created: 2026-11-03
Location: lowering/bodySimStmtCasesScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem body_augassign_place:
  !cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es
   res es'.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    eval_stmt cx (AugAssign ty t bop e) es = (res, es') /\
    ((?bt fld. t = AttributeTarget bt fld) \/ (?bt k. t = SubscriptTarget bt k)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e)) es res es'
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All existing theorem statements, attributes and definitions (including executable
lowering and semantics definitions) are frozen.

## Completion Criteria

- `holbuild -j4 build bodySimStmtCasesTheory` succeeds at the default 2.5s tactic timeout,
  with `body_augassign_place` proved (no `cheat` in it or in any new lemma it uses).
- No new admissions or axioms. The other cheats in bodySimStmtCasesScript.sml stay as they are.
- New helper lemmas go in bodySimStmtCasesScript.sml just above `body_augassign_place`, named with the prefix
  `aug_place_` (other runs edit the same file in parallel), or in a new theory under `lowering/`
  named `bodySimAugPlace*` that bodySimStmtCasesScript.sml imports.

## Build

```sh
holbuild -j4 build bodySimStmtCasesTheory
```

## Background

`x.a.b = v`, `x[i] = v`, `self.m[k].f = v` and the like: an assignment whose target is a
field (`AttributeTarget bt fld`) or an element (`SubscriptTarget bt k`) of any base. The source
(`eval_stmt` Assign / AugAssign, semantics/vyperInterpreterScript.sml ~1433; `eval_target_place`,
`read_place`, `write_place` in semantics/vyperStateScript.sml) evaluates the place and writes the
value there. The lowering (`compile_stmt` Assign / AugAssign, lowering/defs/stmtLoweringScript.sml)
takes the place's pointer and location from `compile_get_target_ptr` and stores by location
(`compile_assign_value`; AugAssign loads and stores with MLOAD/MSTORE, SLOAD/SSTORE or TLOAD/TSTORE).

The target/place judgment is the intended interface: `target_case_all` and `target_place_sim`
(lowering/targetPlaceSimCasesScript.sml) give the target fragment's run and `target_post`
(lowering/targetPlaceSimScript.sml), with the place's pointer, location and type. Use it as-is;
`target_subscript_case` there is an existing admitted lemma (proved elsewhere) and is an acceptable
dependency. The judgments of the index expressions come from `body_expr_ok` / `body_inv`
(`target_idx_case`, `expr_sim_case`, `expr_vv_case`). The supported subset never roots such a
target at an immutable (`supported_place_root`, `supported_subscript_base`,
`supported_storage_field_write` in lowering/supported/), which gives `target_pre`'s
`~immutable_root`. `stmt_frag` asks only for `stmt_state_rel` after the statement, so writing
inside a local's memory region is allowed.

The proved siblings in the same file are the closest models: `body_assign_attr_local`,
`body_assign_attr_storage`, `body_assign_toplevel_copy`, `body_augassign_attr_local`,
`body_augassign_attr_storage`, and `body_assign_local_memory`.

Order on both sides: target place, load the current word, evaluate `e`, binop, store. The
conditional premise gives `body_expr_ok cx e` at the states where the target and the read succeed.
`type_stmt` makes the target's type a word equal to `ty`. Proved models: stmtSimAugAssign*Script.sml.

## Domain Constraints

- Keep the default 2.5s tactic timeout. Do not skip proof steps. No TRY/ORELSE around
  metis or other search tactics.
- Use holbuild only; no HOL REPL sessions.
- Do not change definitions, executable code, theorem statements or attributes of existing
  theorems. Add new lemmas only.
- Do not edit other task files. Commit with trailer `Bot: opus (Claude Opus 5.5)`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target and siblings | lowering/bodySimStmtCasesScript.sml | `body_augassign_place`, the proved `body_assign_*` / `body_augassign_*` lemmas, `stmt_expr_body_pre`, `body_assign_case` / `body_augassign_case` (the dispatch) |
| Body judgments | lowering/bodySimScript.sml | `body_inv`, `body_expr_ok`, `body_base_target_ok`, `body_stmt_ok` |
| Statement judgment | lowering/stmtSimScript.sml | `stmt_frag`, `stmt_env`, `frame_ret_ok` |
| Target/place judgment | lowering/targetPlaceSimScript.sml, lowering/targetPlaceSimCasesScript.sml | `target_sim`, `target_case`, `target_pre`, `target_post`, `place_ptr_rel`, `target_idx_case`, `target_case_all`, `target_place_sim` |
| Assignment lemmas | lowering/stmtSimAssign*Script.sml, lowering/stmtSimAugAssign*Script.sml | word/copy stores to memory, storage and transient, field variants |
| Expression judgments | lowering/exprSimScript.sml, lowering/exprSimHypsScript.sml, lowering/exprSimUnwrapScript.sml | `expr_sim`, `expr_vv_sim`, `vv_holds`, `expr_sim_inv`, `storage_holds_load` |
| State relation | lowering/exprLoweringPropsScript.sml, lowering/defs/compileEnvScript.sml | `stmt_state_rel`, `state_rel`, `storage_rel` |
| Supported subset | lowering/supported/supportedStmtsScript.sml, lowering/supported/supportedExprFormsScript.sml, lowering/supported/supportedTargetsScript.sml | `supported_stmt`, `supported_target`, `supported_aug_target`, `supported_target_info`, `supported_place_root` |
| Lowering | lowering/defs/stmtLoweringScript.sml, lowering/defs/exprLoweringScript.sml | `compile_stmt`, `compile_assign_value`, `compile_get_target_ptr` (~2043) |
| Source | semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml | `eval_stmt`, `eval_target_place`, `eval_base_place`, `write_place`, `read_place` |
| Repo conventions | AGENTS.md | proof style and build rules |

## Notes

The statement parses and builds with `cheat` (bodySimStmtCasesTheory is green), and it is
dispatched from `body_assign_case` / `body_augassign_case`. It was checked against the definitions
by reading (PROVABLE): no immutable roots in the supported subset, the evaluation orders agree, and
`stmt_frag` allows writes into a local's memory.
