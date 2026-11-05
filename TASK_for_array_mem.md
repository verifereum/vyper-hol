# TASK: Memory-safe for-array statement fragment

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (vyper-hol)

## Theorem Statement (FROZEN)

In `lowering/stmtForArrayMemoryScript.sml`:

```sml
Theorem compile_for_array_frag_mem:
  !d ctx func cx cenv lctx RetQ ty id et n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
          (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
  LENGTH vs = n /\
  n < dimword (:256) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var arr_ptr) arr_sz) /\
  name <> id /\ lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  P es /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    ?base. eval_operand (Var arr_ptr) s = SOME base /\
      w2n base + LENGTH vs * type_memory_size tv <= s.vs_alloca_next /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs) (w2n base + k * type_memory_size tv) s.vs_memory /\
        w2n base + k * type_memory_size tv < dimword (:256))) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: ei.scopes)) /\
  (!ei k gs r es2.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes; gas_obs := gs |>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts))
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts)) es
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build stmtForArrayMemoryTheory` passes at the default step limit.
2. The theorem's proof, and any helper you add, contains no `cheat`.
3. No duplicate or near-duplicate lemmas: reuse existing ones (search `lowering/`).

**If the theorem is false as stated:** produce the counterexample, state the tightest sufficient fix, and do NOT silently weaken the statement.

## Build

```
holbuild -j4 build stmtForArrayMemoryTheory
```

## Background

This is the memory-safe twin of S1's `compile_for_array_frag` (`stmtSimForArrayFrag`): the same statement with `stmt_frag` replaced by `stmt_frag_mem d`, plus one premise S1 lacks: the array's region ends below the alloca frontier (`w2n base + LENGTH vs * type_memory_size tv <= s.vs_alloca_next`), which the per-iteration element reads need for memory safety. `stmt_frag_mem` (`lowering/stmtSimDefsScript.sml`) is `stmt_framed_frag` with `gas_outcome T` (memory-safe runs) instead of `F`, plus `return_buf_frame d`, `alloca_history`, and a monotone `vs_alloca_next` in its pre and post. It is consumed by the for-loop case of the S3 body induction (`lowering/bodyMemForArrayScript.sml`).

S1's proof (`compile_for_array_frag` and the tower under it: `stmtSimForArrayFrag`, `stmtSimForArrayLoop`, `stmtSimForArrayParts`, `stmtSimForArray`) is finished; copies of that branch's files are in `alan-ref/s1/`. It is the template. Several of those theories also exist in this tree but are not built with proofs here (admitted locally); their statements are usable. The memory side already has the loop combinator `frag_exec_loop_mem` (`lowering/fragLoopMemoryScript.sml`) and memory-safe counted paths (`lowering/fragGasPathMemScript.sml`).

## Domain Constraints

- This is a frozen proof branch: other branches' theories are admitted locally (their proofs replaced by `cheat`, hidden from git). Cheat warnings from those inherited ancestors are expected; the new proofs and helpers you write must have none.
- Put helper lemmas in new theories under `lowering/` named `stmtFor*Memory*` (or in the target theory itself). Do not edit existing theories (no changes to shared ancestors, statements or definitions).
- No `cheat`, no new axioms, no `TRY`/`ORELSE` around search tactics (`metis_tac` and the like): select goals explicitly. Each tactic step must finish within holbuild's default 2.5 s step limit; split slow steps, never raise the limit.
- The S1 proofs under `alan-ref/s1/` are reference text from another branch and are not built here. Its theory versions can differ from this tree's; build against this tree's theories (lowering/), and read the reference only for the proof structure.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| S1 reference proofs | `alan-ref/s1/stmtSimForArrayFragScript.sml`, `alan-ref/s1/stmtSimForArrayLoopScript.sml`, `alan-ref/s1/stmtSimForArrayPartsScript.sml`, `alan-ref/s1/stmtSimForArrayScript.sml`, `alan-ref/s1/stmtSimForRoundsScript.sml` | finished `gas_outcome F` proofs to port |
| this tree's array tower | `lowering/stmtSimForArray*Script.sml` | statements usable (proofs admitted locally) |
| judgments | `lowering/stmtSimDefsScript.sml` | `stmt_frag`, `stmt_framed_frag`, `stmt_frag_mem`, `stmt_res_ok`, `stmt_exit` |
| posts and frames | `lowering/loweringPostsScript.sml` | `return_buf_frame`, `cenv_top_ext`, `stmt_lands` |
| alloca history | `venom/proofs/allocaHistoryScript.sml` | `alloca_history` and its preservation lemmas |
| local pointers | `lowering/defs/compileEnvScript.sml` | `local_ptrs_rel`, `stmt_state_rel` pieces |
| counted outcomes | `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`, `lowering/gasSummaryComposeScript.sml`, `lowering/gasContextScript.sml` | `gas_outcome`, `gas_admissible`, summaries |
| counted paths | `lowering/fragGasPathScript.sml`, `lowering/fragGasPathMemScript.sml`, `lowering/fragGasSeqScript.sml`, `lowering/fragGasModeScript.sml` | paths and their memory-safe versions |
| memory fragments | `lowering/fragExecMemScript.sml`, `lowering/fragLoopMemoryScript.sml` | `frag_exec_mem`, `mem_safe_run`, `frag_exec_loop_mem` |
| memory copies | `lowering/stmtSimDeclMemScript.sml` | memory-safe `compile_store_memory` / MCOPY runs into a fresh alloca |
| memory statement examples | `lowering/stmtIfMemoryScript.sml`, `lowering/stmtSimSeqMemScript.sml`, `lowering/stmtSimJumpMemScript.sml` | finished `stmt_frag_mem` proofs |
| lowering | `lowering/defs/stmtLoweringScript.sml` | `compile_stmt` for `For`, `declare_local`, `stmt_env`, `stmts_env` |
| source semantics | `semantics/vyperInterpreterScript.sml` | `eval_stmt`, `eval_for`, `eval_iterator` |

## Notes

A read of the statement found the extra `stmt_frag_mem` obligations dischargeable as for the range loops (loop entry, loop-variable ALLOCA, body post), with the element reads at `base + k * type_memory_size tv` kept below the frontier by the added region premise. S1's proof uses a gas_obs-shifting lemma (`stmt_frag_start_gas_obs`) that needs a `stmt_frag_mem` version.
