# TASK: Repair the local-memory and storage-copy assignment sims for lowered RHS types

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root

## Theorem Statement (FROZEN)

`lowering/stmtSimAssignStorageCopyScript.sml` (restated: the premise `lowered_value_type cenv e = expr_type e` is new):

```sml
Theorem compile_assign_storage_copy_stmt_frag:
  !ctx func cx lctx RetQ cenv ty src id e es res es' ts tr typ id_str slot
   tvt.
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) es =
      (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ lowered_value_type cenv e = expr_type e /\
    ~is_word_type typ /\
    (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    (!ann t args. e = TypeBuiltin ann Empty t args ==> t = typ) /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    0 < type_slot_size tvt /\
    type_memory_bytes cenv typ = type_memory_size tvt /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME typ /\
    slot + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (n2w slot, tvt) ==>
       ranges_disjoint slot (type_slot_size tvt)
                       (w2n k') (type_slot_size tv')) /\
    (!v es1.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL v, es1) ==>
       value_has_type tvt v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) es res es'
```

`lowering/bodySimStmtCasesScript.sml` (`body_assign_local_memory` restated: its case condition reads `lowered_value_type cenv e = ty` where it read `expr_type e = ty`, and it takes the lowered-type shape premise, the last one; the other two are unchanged):

```sml
Theorem body_assign_local_memory:
  !cx id e tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'
   ty.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res, es') /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      es res es'

Theorem body_assign_toplevel_copy[local]:
  !cx nsid e tops ctx func cenv env env' ret_ty lctx RetQ es res es' mut ty
   slot.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
    supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) =
      SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx
      (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e) es =
      (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es res es'

Theorem body_assign_case:
  !cx t e.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_ok cx t) /\
    body_expr_ok cx e ==>
    body_stmt_ok cx (Assign (BaseTarget t) e)

```

`lowering/bodySimDeclCasesScript.sml` (`body_annassign_memory` restated the same way, `lowered_value_type cenv e = typ` and the shape premise; `body_annassign_case` unchanged):

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
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    eval_stmt cx (AnnAssign id typ e) es = (res, es') /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
     has_length_word typ /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e)) es res es'

Theorem body_annassign_case:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ok cx e) ==>
    body_stmt_ok cx (AnnAssign id typ e)

```

Do not modify these statements. Prove them as-is, or produce a counterexample.

`body_assign_other` and `body_annassign_other` keep their (restated) statements and their existing `cheat` proofs, and so do the new `body_assign_widened_aggregate_call` and `body_annassign_widened_aggregate_call` (the complement of the shape premise, an internal call widened as a DynArray or tuple): out of scope, do not touch. `body_assign_case` and `body_annassign_case` already split on the shape premise.

The lowered-type shape premise replaces two helpers that were false for internal calls (`lowered_value_type_shape`, `lowered_value_type_arg_fits`, both deleted, as is stmtSimDeclMem's `lowered_value_type_bytestring`). It is already threaded, and these built: `lowered_value_type_memory_bound`, `memory_rhs_destination_bound` (both take it); `memory_rhs_read_destination_footprint`, `memory_rhs_lowered_runtime_layout`, stmtSimDeclMem's `annassign_widen_footprint` and `compile_annassign_memory_widen_stmt_frag` take it too (frozen, as they now read in the source).

Weakly frozen: this helper in `lowering/memoryLocalRhsPropsScript.sml` fails its build in the internal-call case (goal: `value_runtime_typed env (cenv.ce_func_return_type (nsid_to_string func_id)) v`):

```sml
Theorem memory_rhs_read_lowered_typed:
  !cenv e env tops cx es v es'.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env (lowered_value_type cenv e) v
```

You may restate it, and the theorems in `memoryLocalRhsPropsScript.sml` that use it, only by adding premises drawn from `cenv.ce_func_return_type = build_func_return_type tops`, `supported_program tops`, `get_module_code cx NONE = SOME tops`, `expr_sim_inv cenv cx env es`. Report every restatement in your result.

In `stmtSimAssignStorageCopyScript.sml`, the local lemmas `storage_copy_lowered_type`, `storage_copy_success_compatible` and the AbiEncode helpers (`storage_copy_bytes_type`, `storage_copy_abi_value`, `storage_copy_abi_eval`) become unnecessary under the new premise: delete them, and simplify the local proofs that used them.

## Completion Criteria

- `stmtSimAssignStorageCopyTheory`, `stmtSimDeclMemTheory`, `memoryLocalRhsPropsTheory`, `bodySimStmtCasesTheory` and `bodySimDeclCasesTheory` build with the command below at the default per-step limit.
- No new `cheat` in these five theories. Cheats already there (`body_assign_other`, `body_annassign_other`, and others present before this task) stay as they are.
- No changed premises beyond what this file allows.

## Build

```sh
holbuild -j4 build stmtSimAssignStorageCopyTheory stmtSimDeclMemTheory memoryLocalRhsPropsTheory bodySimStmtCasesTheory bodySimDeclCasesTheory
```

## Background

The lowering now types internal-call results at the callee's return type (`lowered_value_type_def`, `compile_call_def` in `lowering/defs/exprLoweringScript.sml`), and `body_inv_def` (`lowering/bodySimScript.sml`) carries `cenv.ce_func_return_type = build_func_return_type tops`. A call is typed so that the callee's `sig.ret_ty` widens to the call's `expr_type` (`type_widens_to`). `compile_stmt` stages an assignment's RHS at `lowered_value_type cenv e`. A storage copy whose destination is a bytestring now copies `type_memory_bytes cenv (lowered_value_type cenv e)` bytes (`copy_size`, `lowering/defs/stmtLoweringScript.sml` near line 405); `assign_storage_copy_suffix` still talks about `mem_size`.

Notes from read-only audits (not built):
- `body_assign_local_memory` / `body_annassign_memory`: if `lowered_value_type cenv e = ty` for an internal call returning `ret`, then `ret` widens to `expr_type e` (call typing) and `expr_type e` widens to `ty` (`atarget_accepts`); widening is antisymmetric, so `expr_type e = ty`. A widened non-bytestring call (`DynArray[uint256,2]` into `DynArray[uint256,4]`) no longer reaches these theorems; it goes to the `_other` theorems. The bytestring disjunct with a narrower call result is covered by the bytestring copy, given `type_memory_bytes ret <= type_memory_bytes ty`.
- No lemma yet links the frame's function signatures to `build_func_return_type`: `expr_sim_inv` → `env_consistent` → `env_context_consistent` → `fn_sigs_consistent` gives `sig.ret_ty` = the `ret` of `lookup_callable_function cx.in_deploy fn tops`; `supported_program` gives distinct function names. A `build_func_return_type_distinct` mirroring `build_func_param_types_distinct` (`lowering/intCallLookupScript.sml`) should close the gap.
- `memory_rhs_read_lowered_typed`: the semantics casts a call's result to `evaluate_type ret` (`vyperInterpreterScript.sml`, the IntCall case, `safe_cast_result_well_typed`).
- `body_assign_toplevel_copy` discharges the new storage-copy premise: its target type `typ` is a supported storage type (`supported_storage_type`: nested types with `uint256`/`int256`/`bytes32` leaves, so no bytestrings) and not a DynArray, internal-call return types are `supported_value_type`, and for such types `type_widens_to` is equality; for the non-call RHS forms whose lowered type differs (string/bytes literals, `AbiEncode`, Concat-like buffers), the type is a bytestring, which a supported storage target excludes.

## Domain Constraints

- Keep every executable definition unchanged. No new premise beyond what this file allows, no feature exclusion, no new cheat.
- The commit at HEAD titled `TEMP: stand-in cheats ...` stands in for proofs being repaired on another branch (`exprSimIfExp`, `exprSimOperators`' ternary cases, `body_ifexp_case`). Don't touch those theories or that commit.
- If an ancestor theory outside the five targets fails to build for a reason other than box load, stop and report it; don't repair it.
- Search for existing helpers before adding one.
- No `TRY`/`ORELSE` around `metis_tac` or other search. Never raise tactic timeouts. No `holbuild run`/`repl`, no Holmake, no `--skip-*` flags, no `--force`.
- A step timeout at a line you didn't touch is box load: rerun that theory once before treating it as a proof problem.
- Commit proof source only (not task/state files). Commit trailer: `Bot: opus (Claude Opus 5.5)`. Do not push.

## Available Resources

- The five target scripts above
- `lowering/defs/exprLoweringScript.sml`, `lowering/defs/stmtLoweringScript.sml`, `lowering/defs/compileVyperScript.sml` (`build_func_return_type_def`), `lowering/defs/contextScript.sml`
- `lowering/bodySimScript.sml` (`body_inv_def`), `lowering/exprSimHypsScript.sml` (`expr_body_pre_def`, `expr_sim_inv`), `lowering/intCallLookupScript.sml`
- `lowering/supported/` (`supported_program`, `supported_storage_type`, `supported_value_type`, `supported_effect_expr`)
- `semantics/type/vyperTypeSystemScript.sml` (`well_typed_expr`, `type_widens_to`, `arg_type_fits`), `semantics/vyperInterpreterScript.sml`, `semantics/prop/` (typing soundness, `fn_sigs_consistent`)

## Notes

The three frozen restatements were approved by the project's design reviewer; each was checked PROVABLE by a read-only audit. Report a counterexample if you find one.
