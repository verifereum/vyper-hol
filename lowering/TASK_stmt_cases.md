# TASK: statement simulation of a word-local declaration and of literal reasons

## Meta
Status: planned
Priority: P1
Created: 2026-10-26
Location: lowering/ (file lowering/stmtSimCasesScript.sml)

## Theorem Statement (FROZEN)

In lowering/stmtSimCasesScript.sml, three theorems:

```sml
Theorem compile_annassign_word_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es res es' etv.
    eval_stmt cx (AnnAssign id vtyp e) es = (res, es') /\
    cenv.ce_alloca_locals /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    32 <= type_memory_bytes cenv vtyp /\
    type_memory_bytes cenv vtyp < dimword (:256) /\
    (!tyv. evaluate_type (get_tenv cx) vtyp = SOME tyv ==>
           type_memory_size tyv = 32) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              ?v. tv = Value v /\ word_value v /\
                  typed_val_to_w256 etv v = val_to_w256 v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'

Theorem compile_raise_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty ml str es res es'.
    eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es res es'

Theorem compile_assert_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty e ml str es res es'.
    eval_stmt cx
      (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es res es'
```

The judgment (`stmt_frag`, `stmt_env`, `stmt_res_ok`, `stmt_exit`, `stmt_lands`, `cenv_top_ext`) is in lowering/stmtSimScript.sml; `expr_sim`, `expr_post`, `expr_exit` in lowering/exprSimScript.sml; `frag_exec` in lowering/fragExecScript.sml; `stmt_state_rel` in lowering/exprLoweringPropsScript.sml.

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build stmtSimCasesTheory` passes with no CHEAT in stmtSimCases.
2. Helpers in their most general form, no duplicates of existing lemmas. Put them in stmtSimCasesScript.sml (above the theorem that uses them) or, if they belong with the code they speak of, export a `[local]` lemma of loweringSlice (e.g. `annassign_alloca_frag`) by dropping `[local]`, without changing its statement.
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Proofs under ~50 lines each; no step near the 2.5 s tactic timeout (never raise it).

**If a theorem is false as stated:** give a concrete counterexample and the tightest fix. Do NOT weaken the statement.

## Build

```
holbuild -j4 build stmtSimCasesTheory
```
(run from the project root, the directory containing holproject.toml)

## Background

vyper-hol issue #637 proves that the Vyper→Venom statement lowering (`compile_stmt`, lowering/defs/stmtLoweringScript.sml) simulates the source interpreter (`eval_stmt`, semantics/vyperInterpreterScript.sml) one statement form at a time, as `stmt_frag` lemmas that compose (`stmt_frag_cons`). stmtSim proves Pass, Break, Continue, Expr, If, bare Raise/Assert and For over a literal range.

- `compile_annassign_word_stmt_frag`: `x: T = e` for a word type, every outcome of `e`. `stmt_env` runs `declare_local` (binds `id` to a fresh pointer variable), then `compile_stmt`: ALLOCA, `lower_value` of `e`, MSTORE. loweringSlice's `compile_annassign_word_frag` proves the success case in frag_exec form (its post has no lookup_var/allocas frame); the error case exits after the ALLOCA through `expr_sim`.
- The reason lemmas: `compile_reason_message` on a string literal (`compile_bytelike_literal`) and `compile_revert_with_reason`, straight-line code ending in REVERT; the source raises `AssertException str`, which `expr_exit` accepts as `Revert_abort`. The assert form adds the condition and JNZ, as the proved `compile_assert_frag` does.

## Domain Constraints

- Project rules in AGENTS.md at the project root: holbuild only, no interactive g/e sessions, `rename1` rather than generated names.
- Don't edit files under semantics/, venom/ or lowering/defs/, nor any existing theorem's statement. In stmtSimScript.sml change nothing.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| statement judgment | lowering/stmtSimScript.sml | stmt_frag_def, stmt_env_def, stmt_exit_def, stmt_lands_def, cenv_top_ext_def, cenv_top_ext_refl, stmt_state_rel_cenv_cong, declare_local_ptr, declare_local_reserved, for_body_entry (the same cong at a declaration), emit_abort_exit, step_revert_zero |
| proved statement patterns | lowering/stmtSimScript.sml | compile_expr_stmt_frag (expr error → exit), cond_jump_frag, compile_assert_frag (condition, JNZ, fail block, ok block), compile_raise_frag |
| word declaration | lowering/loweringSliceScript.sml | compile_annassign_word_frag, compile_annassign_word_parts, annassign_alloca_frag (local), annassign_mstore_frag (local), stmt_state_rel_exec_alloca, stmt_state_rel_declare_word, eval_stmt_annassign_value, expr_frag_def |
| expression judgment | lowering/exprSimScript.sml | expr_sim_def, expr_post_def, expr_exit_def, expr_res_ok_def, expr_sim_expr_frag, expr_exit_INR_type |
| frag_exec | lowering/fragExecScript.sml | frag_exec_def, frag_exec_then, frag_exec_seq, frag_exec_pointwise, frag_exec_conseq, frag_exec_run_inst_seq, frag_exec_exit_prefix, fn_has_code_split, fn_has_code_mid, fn_has_code_new_block, cs_appends_emit_helpers, exit_result_not_error |
| straight-line code | lowering/freshWritesScript.sml | straight_fresh_def, frag_exec_straight_fresh, frag_exec_straight_fresh_abort |
| locals | lowering/localPtrsPropsScript.sml | local_ptrs_rel_exec_alloca_fresh, alloca_inv_exec_alloca, local_ptrs_rel_fresh_not_local_ptr |
| ALLOCA / memory run lemmas | lowering/builtinPropsScript.sml, lowering/loweringHaltScript.sml | step_ALLOCA, step_alloca_frame |
| lowering | lowering/defs/stmtLoweringScript.sml, lowering/defs/exprLoweringScript.sml, lowering/defs/contextScript.sml | compile_stmt_def (AnnAssign, Raise, Assert cases), declare_local_def, declare_stmt_local_def, emit_local_alloca_def, compile_reason_message_def, compile_revert_with_reason_def, compile_bytelike_literal_def, compile_store_byte_chunks_def, unwrap_value_def, compile_alloc_buffer_def |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | step_inst_base (MSTORE, MLOAD, MCOPY, ADD, AND, REVERT), exec_alloca_def |
| source | semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml, semantics/vyperValueOperationScript.sml | evaluate_def (AnnAssign, Raise, Assert), new_variable_def, materialise_def, evaluate_literal_def |

## Notes

Analysis of each statement is in SML comments above it in lowering/stmtSimCasesScript.sml.
