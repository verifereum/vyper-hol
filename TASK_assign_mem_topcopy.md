# TASK: Prove the memory case of self.x = e for an aggregate storage or transient variable

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem body_assign_toplevel_copy_mem:
  !cx nsid e mut ty slot d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_variable_decl tops nsid =
      SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\ expr_type e = ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
It is in `lowering/bodyMemAssignTopCopyScript.sml` with `cheat` as its
proof. All existing definitions and other theorem statements are frozen.
New proof-only helper lemmas are weakly frozen; put them in
`lowering/bodyMemAssignTopCopyScript.sml` or new leaf theories next to it
(`lowering/bodyMemAssignTopCopy*Script.sml`), never in shared ancestors.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `bodyMemAssignTopCopyTheory` builds normally (proof steps on, default
   step limit) with no CHEAT from its own file or from any new leaf theory
   you add, and no parser warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build bodyMemAssignTopCopyTheory
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
`compile_assign_value` (LocStorage / LocTransient branches) in
`lowering/defs/stmtLoweringScript.sml`: compile e, unwrap it to a memory
pointer, then copy its words from memory to the variable's slots: one
`MLOAD` + `SSTORE`/`TSTORE` when the size is at most 32, otherwise
`compile_memory_to_storage` (a loop of `MLOAD` + store per word). The
empty-value form (`has_length_word ... /\ is_empty_value_expr e`) stores a
zero length word instead.

Memory obligations: the only memory accesses after e's code are the
`MLOAD`s of the source value. `storage_rhs_lowered_type` and
`storage_not_bytestring` (S1 `bodySimStmtCases`, see below) give
`lowered_value_type cenv e = expr_type e` and a non-bytestring type, so
`dst_ty = src_ty` (no normalization buffer) and `val_store_size tv v =
type_memory_size tv` (`val_store_size_type_size`,
`lowering/bodyDeclCopyMemoryScript.sml`, `[local]` there). With that,
`expr_store_bound` from e's `expr_sim_mem` post bounds the source region:
`w2n sw + type_memory_size tv <= vs_alloca_next`. No existing lemma proves
`compile_memory_to_storage`'s memory safety; the reverse direction's loop
lemmas (`body_storage_iteration_mem_ok`,
`lowering/bodyStorageCopyMemoryScript.sml`) show the shape.

Closest proved memory twin: `lowering/bodyMemAssignTopWordScript.sml`
(`compile_assign_storage_typed_stmt_frag_mem`, a word storage variable:
`forced_then_outcome` from `lowering/stmtSimForcedScript.sml`,
`eval_assign_toplevel_action`, `assign_storage_store_path_mem`, the wrapper
`body_assign_toplevel_word_mem` deriving the storage facts from
`body_inv`/`type_stmt`).

S1 (non-memory) proof this ports, proved on another branch; copies are in
`alan-ref/s1/` (read-only reference, plain text, not built):
- `alan-ref/s1/bodySimStmtCases.sml.txt`: `body_assign_toplevel_copy`
  and its helpers `body_assign_copy_rhs_pre`, `body_assign_copy_region`,
  `body_assign_copy_target`, `storage_not_bytestring`,
  `storage_rhs_lowered_type`, `storage_value_fit_equal`.
- `alan-ref/s1/stmtSimAssignStorageCopy.sml.txt`:
  `compile_assign_storage_copy_stmt_frag` and its run lemmas
  (`storage_copy_bulk_run`, `storage_copy_one_run`,
  `storage_copy_success_run`, `assign_storage_empty_stmt_frag`, ...).
In this tree `lowering/stmtSimAssignStorageCopyScript.sml` and
`lowering/bodySimStmtCasesScript.sml` are older versions whose proofs are
admitted; their exported theorems are usable (admitted lemmas there are
acceptable dependencies) and their `[local]` ones aren't: copy what you
need into your target file as `[local]` helpers. Don't edit those files.

## Domain Constraints

- No executable definition changes, added assumptions, admissions,
  timeout overrides, or search tactics wrapped in `TRY`/`ORELSE`.
- Keep every full post, frame and storage agreement; use counted GAS paths
  and all source gas tails; don't discard exemption certificates.
- Don't edit files outside `lowering/bodyMemAssignTopCopy*` and new leaf
  theories next to it. Files under `alan-ref/` are reference only.
- At most `-j4`.

## Available Resources

- Target: `lowering/bodyMemAssignTopCopyScript.sml`; dispatch `lowering/bodyMemAssignScript.sml`
- Judgments: `lowering/stmtSimDefsScript.sml`, `lowering/exprSimMemDefsScript.sml`
  (`expr_sim_mem`, `expr_store_bound`), `lowering/bodyMemoryPredsScript.sml`,
  `lowering/bodyMemoryDefsScript.sml`
- Counted outcomes: `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`,
  `lowering/gasExemptCertScript.sml`, `lowering/stmtSimForcedScript.sml`
- Memory twins: `lowering/bodyMemAssignTopWordScript.sml`,
  `lowering/bodyDeclCopyMemoryScript.sml`, `lowering/bodyStorageCopyMemoryScript.sml`,
  `lowering/instMemFrontierScript.sml`, `lowering/fragExecMemScript.sml`
- S1 reference: `alan-ref/s1/`
- Storage layout: `semantics/prop/vyperStorageLayoutSafetyScript.sml`, `lowering/storageCopyLiveScript.sml`
- Lowering: `lowering/defs/stmtLoweringScript.sml`
- Source semantics: `semantics/vyperInterpreterScript.sml` (`eval_stmt` Assign)
