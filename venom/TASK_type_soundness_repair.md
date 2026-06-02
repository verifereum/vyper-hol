# TASK: Repair type soundness proofs after definition strengthening

## Session Start — MANDATORY

**At the start of every session:**

1. Merge main into this branch:
```bash
git merge main --no-edit
```
If there are conflicts, resolve them (keep both sides where possible, prefer main for shared infrastructure changes). Do NOT rebase — merge only.

2. Check what came in: `git log HEAD..main --oneline --stat` (before merging). If any changes affect your work (typing definitions, interpreter changes, framework theories your proofs depend on), read the diffs after merging, rebuild affected theories, and adapt your work before proceeding.

**Do NOT interact with the outside world.** No `git fetch`, `git push`, `git pull`, `gh` commands, or any network operations. All work is local only. If you need something pushed or fetched, stop and ask the user.

**Work in this worktree only.** Do NOT commit to `main`, do NOT `cd` into the root repo or other worktrees. All your work happens under this worktree's directory.

## Meta
Status: planned
Priority: P0
Created: 2026-04-19
Location: semantics/prop/

## Theorem Statement (FROZEN — updated: accounts_well_typed precondition + conclusion added)

```sml
Theorem eval_preserves_swt:
  (!cx s. !env ret_ty st res st'.
    well_typed_stmt env ret_ty s /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
                evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
                value_has_type ret_tv v)) /\
  (!cx ss. !env ret_ty st res st'.
    well_typed_stmts env ret_ty ss /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
                evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
                value_has_type ret_tv v)) /\
  (!cx it. !env typ st res st'.
    well_typed_iterator env typ it /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!vs tyv. res = INL vs /\
              evaluate_type (get_tenv cx) typ = SOME tyv ==>
              EVERY (value_has_type tyv) vs)) /\
  (!cx g. !env st res st'.
    (?ty. well_typed_atarget env g ty) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    eval_target cx g st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (!cx gs. !env st res st'.
    EVERY (\g. ?ty. well_typed_atarget env g ty) gs /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    eval_targets cx gs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (!cx bt. !env st res st'.
    (?ty. well_typed_target env bt ty) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s)))) /\
  (!cx tyv nm body vs. !env typ ret_ty st res st'.
    well_typed_stmts (env with var_types updated_by (flip FUPDATE (nm, typ)))
                     ret_ty body /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    nm NOTIN FDOM env.var_types /\
    eval_for cx tyv nm body vs st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!v ret_tv. res = INR (ReturnException v) /\
               evaluate_type (get_tenv cx) ret_ty = SOME ret_tv ==>
               value_has_type ret_tv v)) /\
  (!cx e. !env st res st'.
    well_typed_expr env e /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    eval_expr cx e st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!tv. res = INL tv ==>
       (?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
              toplevel_value_typed tv tyv) /\
       (!v st''. materialise cx tv st' = (INL v, st'') ==>
          state_well_typed st'' /\ env_consistent env cx st'' /\ accounts_well_typed st''.accounts /\
          (?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 value_has_type tyv v)))) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!s. res <> INR (Error (TypeError s))) /\
    (!vs. res = INL vs ==>
      LIST_REL (\v e. ?tyv.
        evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
        value_has_type tyv v) vs es))
```

The derived theorem `type_preservation` (which drops `well_typed_iterator` from P2 and extracts P0) must also build. Its statement is in the same file.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper files
 * (e.g. <project>Lib.sml, <project>Script.sml) and
 * holmake tool first.
 ************************************************************
 *)

## Completion Criteria

1. holmake tool with holmake(workdir="semantics/prop/") passes with zero CHEAT warnings and zero FAILs.
2. No new cheats relative to main (the file currently has zero cheats on main, so zero cheats required).
3. No duplicate or near-duplicate lemmas — each helper should exist once in its most general form.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (e.g., `EVAL_TAC` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holmake tool: holmake(workdir="semantics/prop", timeout=120)
```

## Background

Type soundness (progress + preservation) for the Vyper interpreter: well-typed programs preserve `state_well_typed` and `env_consistent` through evaluation, never raise TypeError exceptions, and successful expression evaluation produces values matching their declared types.

This is a proof repair task. The branch `typecleanup` (issue #308) strengthened:
1. The `eval_preserves_swt` and `type_preservation` theorem statements to include no-TypeError conjuncts (`∀s. res ≠ INR (Error (TypeError s))`) in all 9 mutual induction propositions (P0-P8).
2. Several typing definitions in `vyperTypeSoundnessDefsScript.sml` to constrain argument types that previously allowed TypeErrors through:
   - `well_typed_binop` In/NotIn: element type must match array element type
   - `well_typed_builtin_app` Keccak256/Sha256: argument must be sized type (bytes/string)
   - `well_typed_builtin_app` AsWeiValue: argument must be numeric
   - `well_typed_builtin_app` Slice: start/length must be int types
   - `well_typed_builtin_app` ECRecover/ECAdd/ECMul: argument type constraints
   - `well_typed_builtin_app` **MakeArray**: changed from `F` (excluded) to two cases:
     - `MakeArray NONE bd`: tuple construction → `ty = TupleT ts /\ compatible_bound bd (LENGTH ts)`
     - `MakeArray (SOME elem_ty) bd`: array construction → `ty = ArrayT elem_ty bd /\ compatible_bound bd (LENGTH ts) /\ EVERY ($= elem_ty) ts`
   - `well_typed_builtin_app` **Acc**: changed from `F` (excluded) to `LENGTH ts = 1 /\ (?bd. HD ts = BaseT (BytesT bd)) /\ ty = account_item_type item`
   - `subscript_type_ok` TupleT: `EVERY ($= result_ty) ts` (unchanged, still homogeneous restriction; TODO comment added for future TupleElement AST node)
   - `well_typed_expr` TopLevelName: `ty <> NoneT` (HashMaps not first-class)
   - `well_typed_expr` **TypeBuiltin (AbiEncode)**: changed from excluded to explicitly typed: `ty = BaseT (BytesT (Dynamic n))`, `target_ty = TupleT (MAP expr_type es)`
   - `well_typed_type_builtin_args` **Convert**: added `valid_conversion (HD ts) target_ty` constraint
   - `well_typed_type_builtin_args` **AbiEncode**: changed from `F` to `ts <> [] /\ target_ty = TupleT ts`
   - `well_typed_expr` ExtCall: `MAP expr_type args = arg_types`, drv typed via well_typed_opt + return type
   - `well_typed_expr` Send/RawCallTarget/RawLog/RawRevert/SelfDestructTarget/CreateTarget: `well_typed_opt env drv`, argument type constraints
   - In/NotIn: `?bd. t2 = ArrayT t1 bd`
   - `well_typed_stmt` AssertReason: reason expr must have StringT type
3. New definitions added in `vyperTypeSoundnessDefsScript.sml`:
   - **`valid_conversion_def`**: enumerates all valid (source_type, target_type) pairs for `convert()` based on `evaluate_convert_def`. Covers: bool↔bytes/int/uint, bytes↔bytes/uint/int/string, numeric↔numeric, int↔address, flag↔int/uint, int↔bytes, int↔decimal, decimal↔int/uint. All other pairs → F.
   - **`account_well_typed_def`**: `a.balance < 2^256 /\ LENGTH a.code <= 24576`
   - **`accounts_well_typed_def`**: `!addr. account_well_typed (lookup_account addr acc)`
4. Deleted `vyperTypeErrorCounterexampleScript.sml` — no longer needed after TopLevelName NoneT fix.
5. Added helper lemmas in `vyperTypeSoundnessHelpersScript.sml`:
   - `materialise_no_type_error` (proved)
   - `materialise_type_error_NoneTV` (proved)
   - `materialise_type_error_imp_HashMapRef` (proved)
   - `evaluate_type_NoneTV_imp_NoneT` (proved)
   - `well_typed_expr_TopLevelName_NotNoneT` (proved)
   - `well_typed_expr_NoneT_eval_not_HashMapRef` (proved — no cheats)

The proofs need repair because: (a) the no-TypeError conjunct is new and needs proving for every induction case, (b) the definition changes altered `well_typed_expr`/`well_typed_binop`/`well_typed_builtin_app`/`subscript_type_ok` shapes which changes what `gvs[well_typed_expr_def]` and similar produce.

## Domain Constraints

- HOL4 `suspend`/`Resume`/`Finalise` mechanism structures the large mutual induction. Each Resume block handles one case. New Resume blocks can be added; existing ones modified.
- `not_return_tac` and `tp_bind_err_tac` are shared tactics that handle the "not a return/TypeError" disjuncts. They need extending for the no-TypeError conjunct.
- `materialise_no_type_error` lemma: `materialise` only raises TypeError on `HashMapRef`. Since `well_typed_expr` now excludes `TopLevelName NoneT`, `materialise_no_type_error` gives `¬(∀tyv. toplevel_value_typed tv tyv ⇒ tyv = NoneTV)` which with `well_typed_expr` gives the no-TypeError conjunct for materialise cases.
- **New proof obligations from MakeArray/AbiEncode inclusion**: These were previously excluded (`F`) from `well_typed_builtin_app`, meaning cases would simplify away. Now they produce real subgoals that need: (1) `MakeArray NONE` → tuple typing (heterogeneous element types), (2) `MakeArray (SOME elem_ty)` → array typing (homogeneous), (3) `AbiEncode` → bytes result type. Each requires showing `evaluate_builtin` preserves value_has_type for these cases.
- **New proof obligations from Acc inclusion**: `evaluate_builtin` for Acc produces values from account state. Need `accounts_well_typed` invariant to show these satisfy `value_has_type`. **RESOLVED**: `accounts_well_typed st.accounts` added as precondition and `accounts_well_typed st'.accounts` added as conclusion to all P0-P8.
- **New proof obligations from valid_conversion**: Convert cases now have `valid_conversion` constraint. Need to show `evaluate_convert` preserves `value_has_type` for each valid conversion pair. The `valid_conversion` definition mirrors `evaluate_convert_def` cases.
- Do not modify interpreter definitions (`vyperInterpreterScript.sml`, `vyperValueOperationScript.sml`).
- `simp[Once run_block_def]` hangs — use `ONCE_REWRITE_TAC[run_block_def]` (not relevant here but good to know).
- Prefer `irule`/`drule_all` over `metis_tac` for large assumption contexts.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Main theorem file | `semantics/prop/vyperTypeSoundnessScript.sml` | eval_preserves_swt + type_preservation (~3892 LOC) |
| Definition file | `semantics/prop/vyperTypeSoundnessDefsScript.sml` | All typing definitions (CHANGED in this branch) |
| Helper file | `semantics/prop/vyperTypeSoundnessHelpersScript.sml` | lemmas incl materialise_no_type_error (NEW) |
| ~~Counterexample file~~ | `vyperTypeErrorCounterexampleScript.sml` | DELETED (no longer needed) |
| value_has_type, safe_cast | `semantics/prop/vyperTypingScript.sml` | Core type compatibility (587 LOC) |
| assign_preserves_type | `semantics/prop/vyperAssignPreservesTypeScript.sml` | Array/struct assignment (464 LOC) |
| assign_target preservation | `semantics/prop/vyperAssignTargetScript.sml` | assign_target preserves scopes (471 LOC) |
| eval_preserves_tv | `semantics/prop/vyperEvalPreservesScopesScript.sml` | Evaluation preserves type-value (1942 LOC) |
| eval_preserves_immutables_dom | `semantics/prop/vyperEvalPreservesImmutablesDomScript.sml` | Immutables domain (2036 LOC) |
| eval_preserves_scopes_dom | `semantics/prop/vyperEvalExprPreservesScopesDomScript.sml` | Scopes domain (856 LOC) |
| scope_preservation | `semantics/prop/vyperScopePreservationScript.sml` | push_scope, pop_scope (513 LOC) |
| state preservation | `semantics/prop/vyperStatePreservationScript.sml` | monad ops (218 LOC) |
| immutables preservation | `semantics/prop/vyperImmutablesPreservationScript.sml` | set_immutable, write_storage_slot (70 LOC) |
| encode/decode | `semantics/prop/vyperEncodeDecodeScript.sml` | encode/decode roundtrip (2120 LOC) |
| lookup/storage | `semantics/prop/vyperLookupStorageScript.sml` | Storage lookup (890 LOC) |
| lookup_scopes | `semantics/prop/vyperLookupScript.sml` | Scope lookup (1172 LOC) |
| array operations | `semantics/prop/vyperArrayScript.sml` | Array index/set/append/pop (449 LOC) |
| eval_binop properties | `semantics/prop/vyperEvalBinopScript.sml` | Binary operation typing (393 LOC) |
| Interpreter definition | `semantics/vyperInterpreterScript.sml` | evaluate_def (the mutual definition) |
| AST definition | `syntax/vyperASTScript.sml` | expr, stmt, assignment_target types |
| Value definitions | `semantics/vyperValueScript.sml` | value, type_value |
| Value operations | `semantics/vyperValueOperationScript.sml` | safe_cast, evaluate_binop, evaluate_builtin, TypeError sources |
| State definitions | `semantics/vyperStateScript.sml` | evaluation_state, materialise (HashMapRef→TypeError) |
| Context definitions | `semantics/vyperContextScript.sml` | eval_context, ecrecover, ec_add, ec_mul |
| Storage definitions | `semantics/vyperStorageScript.sml` | decode_value, encode_value, read/write_storage_slot |
| Holmakefile | `semantics/prop/Holmakefile` | `INCLUDES = ../ ../../syntax ../../frontend $(VFMDIR)/util $(VFMDIR)/spec` |

## Notes

- The existing proof file uses `suspend`/`Resume` for every induction case. Most cases were proved on main (without the no-TypeError conjunct). The repair needs to extend each Resume block to also prove the no-TypeError conjunct.
- For cases that only use `not_return_tac` for the "not a ReturnException" part, the no-TypeError conjunct often follows from: (1) the same IH gives no-TypeError, (2) monadic operations that don't produce TypeError, or (3) `materialise_no_type_error` when `materialise` is used.
- The `ReturnSome` case was the first failure. A prover agent partially addressed it by adding `materialise_type_error_NoneTV`, `materialise_type_error_imp_HashMapRef`, `evaluate_type_NoneTV_imp_NoneT`, `well_typed_expr_TopLevelName_NotNoneT` lemmas and extending the ReturnSome Resume block. The helper `well_typed_expr_NoneT_eval_not_HashMapRef` is now proved (no cheats).
- The key proof strategy for no-TypeError: if `materialise` produces TypeError, then `is_HashMapRef tv` (by `materialise_type_error_imp_HashMapRef`). But `well_typed_expr` excludes `TopLevelName NoneT`, and `NoneT` is the only type producing `HashMapRef` at evaluation. So `toplevel_value_typed tv tyv` with `tyv ≠ NoneTV` means `materialise` can't produce TypeError (via `materialise_no_type_error`).
- Existing tactics `not_return_tac` and `tp_bind_err_tac` are the main extension points.
- The definition changes may cause some `gvs[well_typed_expr_def]` or `gvs[well_typed_binop_def]` calls to produce different subgoal shapes.
- `well_typed_expr_NoneT_eval_not_HashMapRef` is now proved (no cheats). Proof style is broad (many lemmas in single simp[] call); consider extracting subgoals if it becomes fragile.
- **MakeArray proof**: `evaluate_builtin` for `MakeArray` produces either `TupleV (REVERSE vs)` or `ArrayV elem_ty bd (LIST_TO_SET' vs)`. For tuple case, need `EVERY (value_has_type (TupleTV ...))` or equivalent; for array case, need `value_has_type (ArrayTV elem_ty bd)`. The `compatible_bound` constraint should suffice for empty check.
- **AbiEncode proof**: `evaluate_builtin` for `AbiEncode` produces encoded bytes. Need to show `value_has_type (BytesTV ...)`. The `target_ty = TupleT (MAP expr_type es)` constraint from `well_typed_type_builtin_args` ensures argument types match.
- **Acc proof**: `evaluate_builtin` for `Acc` reads account fields. Need `accounts_well_typed` to establish `value_has_type (account_item_type item)`. **RESOLVED**: `accounts_well_typed st.accounts` now a precondition of `eval_preserves_swt`. Need to prove: (1) `accounts_well_typed` is preserved through evaluation (accounts can be modified by SEND/ExtCall/IntCall), (2) Acc builtin values satisfy `value_has_type` given `accounts_well_typed`.
- **Convert proof with valid_conversion**: Need a lemma: `valid_conversion src_ty tgt_ty ⇒ evaluate_convert never raises TypeError when value_has_type src_ty v`, and the result satisfies `value_has_type tgt_ty`. This mirrors the Python compiler's convert logic.
