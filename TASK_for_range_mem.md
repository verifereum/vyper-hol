# TASK: Memory-safe for-range statement fragments

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (vyper-hol)

## Theorem Statement (FROZEN)

In `lowering/stmtForRangeLitMemoryScript.sml`:

```sml
Theorem compile_for_range_lit_frag_mem:
  !P d ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es tyv.
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    P (es with gas_obs := []) /\
    (!st0 c st1 ex inc ei j.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts))
      (eval_stmt cx
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts)) es
```

In `lowering/stmtForRangeMemoryScript.sml`:

```sml
Theorem compile_for_range_checked_frag_active_mem:
  !P Q d (ctx, func, cx, lctx, RetQ, cenv, env, ty)
   id fty e1 e2 bound stmts es tyv.
    is_int_type fty /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\ bound < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tyv /\
    is_word_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tyv /\
    expr_sim_mem ctx func cenv cx fty e1 es /\
    (!gs tv es1.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       ?n1. tv = IntV n1 /\ value_has_type tyv (IntV n1) /\
            expr_sim_mem ctx func cenv cx fty e2 es1 /\
            !gs2 tv2 es2.
              (do raw <- eval_expr cx e2; read_result cx raw od)
                (es1 with gas_obs := gs2) = (INL tv2, es2) ==>
              ?n2. tv2 = IntV n2 /\ value_has_type tyv (IntV n2) /\
                   P es2) /\
    (!gs n1 es1 n2 es2.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL (IntV n1), es1) /\
       (do raw <- eval_expr cx e2; read_result cx raw od) es1 =
         (INL (IntV n2), es2) /\
       n1 <= n2 /\ Num (n2 - n1) <= bound /\ 0 < Num (n2 - n1) ==> Q) /\
    well_typed_expr env e1 /\ well_typed_expr env e2 /\
    (!x t. FLOOKUP env.var_types x = SOME t ==>
           well_formed_type env.type_defs t) /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    (!st0 c st1 ex inc ei n1 j.
       declare_local cenv id fty st0 = (c, st1) /\
       Q /\ P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) ==>
       stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei n1 j gs r2 es2 sc rest.
       Q /\ P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) =
         (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts))
      (eval_stmt cx (For id fty (Range e1 e2) bound stmts)) es
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build stmtForRangeLitMemoryTheory stmtForRangeMemoryTheory` passes at the default step limit.
2. Neither theorem's proof, nor any helper you add, contains `cheat`.
3. No duplicate or near-duplicate lemmas: reuse existing ones (search `lowering/`).

**If a theorem is false as stated:** produce the counterexample, state the tightest sufficient fix, and do NOT silently weaken the statement.

## Build

```
holbuild -j4 build stmtForRangeLitMemoryTheory stmtForRangeMemoryTheory
```

## Background

These are the memory-safe twins of S1's `compile_for_range_lit_frag` (`stmtSimFor`) and `compile_for_range_checked_frag_active` (`stmtSimForRange`): the same statements with `stmt_frag` replaced by `stmt_frag_mem d` and `expr_sim` by `expr_sim_mem`. `stmt_frag_mem` (`lowering/stmtSimDefsScript.sml`) is `stmt_framed_frag` with `gas_outcome T` (memory-safe runs) instead of `F`, plus `return_buf_frame d`, `alloca_history`, and a monotone `vs_alloca_next` in its pre and post. They are consumed by the for-loop case of the S3 body induction (`lowering/bodyMemForRangeLitScript.sml`, `lowering/bodyMemForRangeScript.sml`).

S1's proofs of both lemmas, and of the loop machinery under them (`for_iteration`, `for_loop` in `stmtSimForLoop`, `compile_for_range_frag` in `stmtSimFor`), are finished on another branch; copies are in `alan-ref/s1/`. They are the template. The memory side already has the loop combinator `frag_exec_loop_mem` (`lowering/fragLoopMemoryScript.sml`) and memory-safe counted paths (`lowering/fragGasPathMemScript.sml`).

## Domain Constraints

- This is a frozen proof branch: other branches' theories are admitted locally (their proofs replaced by `cheat`, hidden from git). Cheat warnings from those inherited ancestors are expected; the new proofs and helpers you write must have none.
- Put helper lemmas in new theories under `lowering/` named `stmtFor*Memory*` (or in the target theory itself). Do not edit existing theories (no changes to shared ancestors, statements or definitions).
- No `cheat`, no new axioms, no `TRY`/`ORELSE` around search tactics (`metis_tac` and the like): select goals explicitly. Each tactic step must finish within holbuild's default 2.5 s step limit; split slow steps, never raise the limit.
- The S1 proofs under `alan-ref/s1/` are reference text from another branch and are not built here. Its theory versions can differ from this tree's; build against this tree's theories (lowering/), and read the reference only for the proof structure.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| S1 reference proofs | `alan-ref/s1/stmtSimForScript.sml`, `alan-ref/s1/stmtSimForLoopScript.sml`, `alan-ref/s1/stmtSimForRangeScript.sml`, `alan-ref/s1/stmtSimForPartsScript.sml`, `alan-ref/s1/stmtSimForRoundsScript.sml` | finished `gas_outcome F` proofs to port |
| judgments | `lowering/stmtSimDefsScript.sml` | `stmt_frag`, `stmt_framed_frag`, `stmt_frag_mem`, `stmt_res_ok`, `stmt_exit` |
| expression judgment | `lowering/exprSimMemDefsScript.sml` | `expr_sim_mem`, `expr_vv_sim_mem` |
| posts and frames | `lowering/loweringPostsScript.sml` | `return_buf_frame`, `cenv_top_ext`, `expr_post`, `stmt_lands` |
| alloca history | `venom/proofs/allocaHistoryScript.sml` | `alloca_history` and its preservation lemmas |
| counted outcomes | `lowering/gasOutcomeScript.sml`, `lowering/gasSummary*Script.sml`, `lowering/gasContextScript.sml` | `gas_outcome`, `gas_admissible`, summaries |
| counted paths | `lowering/fragGasPathScript.sml`, `lowering/fragGasPathMemScript.sml`, `lowering/fragGasSeqScript.sml`, `lowering/fragGasModeScript.sml` | paths and their memory-safe versions |
| memory fragments | `lowering/fragExecMemScript.sml`, `lowering/fragLoopMemoryScript.sml` | `frag_exec_mem`, `mem_safe_run`, `frag_exec_loop_mem` |
| memory statement examples | `lowering/stmtIfMemoryScript.sml` (If), `lowering/stmtSimSeqMemScript.sml`, `lowering/stmtSimJumpMemScript.sml` (break/continue), `lowering/stmtSimDeclMemScript.sml` (declarations) | finished `stmt_frag_mem` proofs |
| S1 counterparts in this tree | `lowering/stmtSimIfCountedScript.sml`, `lowering/stmtSimForPartsScript.sml`, `lowering/stmtSimForRoundsScript.sml` | the If proof's `F` version; for-loop block layouts and source rounds |
| lowering | `lowering/defs/stmtLoweringScript.sml` | `compile_stmt` for `For`, `declare_local`, `stmt_env`, `stmts_env` |
| source semantics | `semantics/vyperInterpreterScript.sml` | `eval_stmt`, `eval_for`, `eval_iterator` |

## Notes

A read of the statements found both provable: the extra `stmt_frag_mem` obligations come from the loop entry (`return_buf_frame` via `not_fresh_at`, `ce_return_buf` kept by `cenv_top_ext`), the single loop-variable ALLOCA and the body post (`alloca_history`, frontier), and the range checks touch no memory.
