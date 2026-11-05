# TASK: Prove the memory case of x = e for a local x held in memory

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem body_assign_local_memory_mem:
  !cx id e ty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/
     is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/bodyMemAssignLocalMemScript.sml` with `cheat` as its
proof. All existing definitions and other theorem statements are frozen.
New proof-only helper lemmas are weakly frozen; put them in
`lowering/bodyMemAssignLocalMemScript.sml` or new leaf theories next to it
(`lowering/bodyMemAssignLocalMem*Script.sml`), never in shared ancestors.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `bodyMemAssignLocalMemTheory` builds normally (proof steps on, default
   step limit) with no CHEAT from its own file or from any new leaf theory
   you add, and no parser warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build bodyMemAssignLocalMemTheory
```

## Background

The statement is one subcase of the S3 (memory-safety) body induction's
assignment case, dispatched in `lowering/bodyMemAssignScript.sml`. The
target judgment is `stmt_frag_mem` (`lowering/stmtSimDefsScript.sml`):
under `gas_admissible` of the statement's source action, a counted
`gas_outcome` (`lowering/gasOutcomeScript.sml`) on a memory-checked path
(`memory = T`, every instruction's memory access below `vs_alloca_next`):
either a `gas_summary_at` with the full post/exit, or an exemption
certificate `gas_exempt_cert` (`lowering/gasExemptCertScript.sml`). e's
memory simulation comes from `body_expr_mem_ok cx e`
(`lowering/bodyMemoryPredsScript.sml`).

Lowering: `compile_stmt` for `Assign (BaseTarget bt) e` and
`compile_assign_value` in `lowering/defs/stmtLoweringScript.sml`. Two
shapes:
- empty value (`has_length_word (expr_type e) /\ is_empty_value_expr e`):
  one `MSTORE [Var p; Lit 0w]` of a zero length word at the local's pointer.
- otherwise: compile e, unwrap, then `compile_assign_value` at
  `dst_ty = ty`, `src_ty = lowered_value_type cenv e`. When the source is in
  memory it stages through a fresh buffer (`compile_alloc_buffer` of
  `type_memory_bytes cenv src_ty`, a flat copy of that many bytes from the
  source, then `compile_store_memory` into the local); otherwise
  `compile_store_memory` straight from the source.

Memory obligations and where they come from:
- The staging copy reads `type_memory_bytes cenv (lowered_value_type cenv e)`
  bytes at the source pointer sw. `expr_sim_mem_room`
  (`lowering/bodyRhsRoomMemoryScript.sml`) gives
  `w2n sw + type_memory_size ltv <= vs_alloca_next` at `ltv`, the
  evaluation of `lowered_value_type cenv e`, for a value left in memory.
  `annassign_bytes_rhs_located_mem` (`lowering/bodyDeclBytesMemoryScript.sml`)
  is a proved use of it for a declaration; it is stated for bytestrings, so
  you need the same thing for this statement's types.
- Do NOT rely on the staging buffer's ALLOCA advancing the frontier past
  anything: inside a `For` loop that ALLOCA was already allocated on an
  earlier iteration. `compile_scratch_prefix_body_path` (used in
  `annassign_memory_assign_widen_body_path`, bodyDeclBytesMemory) handles
  the buffer generally.
- The destination region: `local_ptrs_rel` in `stmt_state_rel` gives the
  local's pointer w with `w2n w + sz <= vs_alloca_next` and
  `type_memory_size entry.type <= sz` (see `assign_local_word_store_path_mem`
  in `lowering/bodyMemAssignLocalWordScript.sml`).

Closest proved memory twins (declarations, `AnnAssign`), whose path lemmas
are stated for a NEW local (`lookup_scopes id es.scopes = NONE`, the new
entry added to the top scope); for `x = e` the local exists and the write
is `write_place cx (MemoryPlace id [])` / `stmt_state_rel_write_local`
(`find_containing_scope`), so you need write-local versions:
- `lowering/bodyDeclBytesMemoryScript.sml`: `compile_annassign_bytes_stmt_frag_mem`,
  `annassign_memory_assign_widen_body_path`, `annassign_bytes_post_path_mem`.
- `lowering/bodyDeclCopyMemoryScript.sml`: `compile_annassign_copy_stmt_frag_mem`,
  `annassign_copy_post_path_mem`, `val_store_size_type_size`.
- `lowering/bodyDeclMemoryCountedScript.sml`: `annassign_memory_store_body_path`,
  `annassign_memory_assign_body_path`.
- `lowering/bodyDeclEmptyMemoryScript.sml`: the empty-value MSTORE.
- `lowering/bodyMemAssignLocalWordScript.sml`: the proved word-local
  assignment twin (outer structure of the counted outcome for `x = e`: the
  exempt branch, exception branch, normal branch, frames chained with
  `not_fresh_at_mono` and `return_buf_frame_frame`; source facts
  `assign_local_admissible_rhs`, `assign_local_admissible_run`,
  `assign_local_continuation_all_tails`, `assign_local_exempt`).
- `lowering/bodyCopyMemoryScript.sml`: staged copy into a local from a Name
  source (`compile_assign_value_name_staged_body_frag_mem`), may help.

S1 (non-memory) proof this ports, proved on another branch; copies are in
`alan-ref/s1/` (read-only reference, not built):
- `alan-ref/s1/bodySimStmtCasesScript.sml`: `body_assign_local_memory`
  (case split: empty value vs the widen frag), its helpers
  `body_assign_local_rhs_pre`, `body_assign_local_memory_read`,
  `assign_local_memory_bytes_pos` (the last gives `0 < type_memory_bytes cenv ty`,
  which the S1 statement had as a premise and this one derives).
- `alan-ref/s1/stmtSimAssignMemScript.sml`: `compile_assign_local_memory_widen_stmt_frag`,
  `local_memory_assign_widen_run`, `local_memory_store_run_framed`,
  `compile_assign_local_empty_stmt_frag`, `local_header_store_state`.
In this tree `lowering/stmtSimAssignMemScript.sml` and
`lowering/bodySimStmtCasesScript.sml` are older versions whose proofs are
admitted; their exported theorems are usable (and admitted lemmas there
are acceptable dependencies), their `[local]` ones aren't: copy what you
need into your target file as `[local]` helpers. Don't edit those files.

## Domain Constraints

- No executable definition changes, added assumptions, admissions,
  timeout overrides, or search tactics wrapped in `TRY`/`ORELSE`.
- Keep every full post, frame and storage agreement; use counted GAS paths
  and all source gas tails; don't discard exemption certificates.
- Don't edit files outside `lowering/bodyMemAssignLocalMem*` and new leaf
  theories next to it. Files under `alan-ref/` are reference only.
- At most `-j4`.

## Available Resources

- Target: `lowering/bodyMemAssignLocalMemScript.sml`; dispatch `lowering/bodyMemAssignScript.sml`
- Judgments: `lowering/stmtSimDefsScript.sml`, `lowering/exprSimMemDefsScript.sml`
  (`expr_sim_mem`, `expr_store_bound`, `vv_store_bound`),
  `lowering/bodyMemoryPredsScript.sml`, `lowering/bodyMemoryDefsScript.sml`
- Counted outcomes: `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`,
  `lowering/gasSummaryComposeScript.sml`, `lowering/gasExemptCertScript.sml`,
  `lowering/stmtSimForcedScript.sml`
- Memory twins: listed above (bodyDecl*Memory, bodyMemAssignLocalWord,
  bodyCopyMemory, bodyRhsRoomMemory)
- S1 reference: `alan-ref/s1/`
- Lowering: `lowering/defs/stmtLoweringScript.sml`
- Source semantics: `semantics/vyperInterpreterScript.sml` (`eval_stmt` Assign)
