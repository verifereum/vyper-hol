# TASK: Prove body memory safety for S3

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Locations: lowering/bodyMemoryScript.sml and additive lowering memory proofs

## Theorem Statement (FROZEN)

The counted body endpoint retains the existing outer hypotheses, adds the
approved syntax-wide ABI-target coverage supplied by actual function membership,
and replaces externally fixed source results with the actual source action.

```sml
Theorem body_stmts_sim_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) (eval_stmts cx ss) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
The approved shared definitions are canonical in exprSimMemDefs (expr_sim_mem,
expr_vv_sim_mem), stmtSimDefs (stmt_frag_mem), loweringPosts (return_buf_frame)
and bodyMemoryDefs (frame_ret_ok_mem). Do not change their statements.

## Completion Criteria

1. Prove the universal body endpoint through actual expression, assignment,
   loop and internal-call memory execution. A body-footprint assumption,
   restricted coverage family or renamed admission does not deliver it.
2. Migrate the existing additive body predicates/consumers to the counted
   source-action schema, threading approved ABI coverage and preserving their
   remaining hypotheses and checked facts. Derive coverage from the actual
   FunctionDecl body at S3 entry; no new top-level premise.
3. Build bodyMemoryTheory and edited additive memory theories with all kernel
   guards intact; no newly admitted helpers or changed stage hypotheses.
4. Commit proof sources and necessary roots; retain existing successful proof
   code while repairing it. Do not put internal task/plan files in a public PR.

## Build

`holbuild -j2 build bodyMemoryTheory`

Use focused edited theory targets during development. The complete root has
not yet parsed under this join: its additive ancestors require this migration.

## Background

This is the body half of S3. The source-action endpoint and selected-execution
completion/run-safety migration were approved by argon in owner ruling
637493940. The separate common counted join c8ae8464f supplies definitions,
mode-T values/stack/forcing and nil/pass/cons/break/continue roots.
Independent read-only audit: full body theorem UNKNOWN, no full-premise
counterexample found. Generic Expr/If/Assert composers are PROVABLE at the
composition level; that audit is not a proof or build.

The body definitions body_stmt_mem_ok, body_stmts_mem_ok and their projection
now supply actual eval_stmt/eval_stmts actions with the same outer hypotheses.
Their existing proofs and consumers still need repair. body_expr_mem_ok keeps
its outer schema. Do not add stmts_no_control_escape to the universal theorem:
stmt_frag_mem already requires admissibility at each concrete entry.

## Domain Constraints

No new axiom, admission, timeout override or TRY/ORELSE search wrapper.
Keep proof steps, cache and checkpoints enabled. No holbuild run/repl.
Search before adding helpers: export/move existing facts rather than duplicating
local or renamed copies. Preserve theory-local simp scope when exporting.
No source-semantics, executable compiler or supported-program changes.
No new stage/program safety premise, oracle equality or no-GAS exclusion.
Retain complete posts, local/alloca preservation, allocation history/frontier,
caller-owned return buffers and arbitrary RetQ for every terminal gas tail.
Finite storage observations concern the selected actual source execution;
all-oracle gas_admissible covers result shape only. The shared selected-run
finite-storage selector is unresolved: do not silently add all-gas H goodness,
move it into admissibility or claim source-trace transport through gas_obs.

- Own additive memory proof sources and their required build roots. Functional
  S1/source/definition files are read-only, except exporting existing local
  helpers unchanged where actual memory consumers need them. Preserve their
  proofs/statements and local rewrite scope. No new inherited simp rules.
- The common stack adapter lives in exprSimMemoryStack; nil/pass/cons live in
  stmtSimZero/stmtSimPass/stmtSimSeqMem, jumps in stmtSimJumpMem. Old body copies
  were removed. Import these owners rather than restoring duplicates.
- Existing generic Expr/If/Assert memory composers are independent migrations
  supplied through separate frozen jobs. Do not modify their target proofs
  while another owner job runs. Ask owner for a checked handoff if needed.
- Keep frag_exec_loop_mem unchanged; low-level prefix transfer alone does not
  establish actual counted target execution. Retain one actual target path and
  its executed GAS marks; no general frag_exec-to-path converse is available.
- Constructor body_inv generalization belongs to the deployment lane; await
  its checked handoff rather than independently changing it here.
- lower_vyper_runtime_unit_run_mem_safe and other unfinished memory admissions
  may not prove this root. Pre-existing unrelated functional admissions can
  remain dependencies but identify them honestly.
- Do not edit allocation-history producer proofs or shared gas judgments.
- The main S3 consumer loweringMemCorrect is owner-coordinated: do not edit it
  until the coordinator supplies integration after pending #961/#1051.

## Available Resources

- lowering/exprSimMemDefsScript.sml, stmtSimDefsScript.sml, loweringPostsScript.sml:
  canonical counted memory contracts.
- lowering/exprSimMemoryValuesScript.sml, exprSimMemoryStackScript.sml,
  exprSimMemoryForceScript.sml, exprSimBufferForceScript.sml: checked common roots.
- lowering/stmtSimSeqMemScript.sml, stmtSimZeroScript.sml, stmtSimPassScript.sml,
  stmtSimJumpMemScript.sml: checked common statement roots.
- lowering/stmtSimExprScript.sml, stmtSimIfCountedScript.sml,
  stmtSimAssertScript.sml: canonical ordinary counted composition siblings.
  Legacy stmtSimIf and bodySimMain in this join still contain fixed-result text.
- lowering/gasOutcomeScript.sml, gasSummaryScript.sml, fragGasSeqMemScript.sml,
  fragGasSeqAbortScript.sml: actual counted memory paths, including abort prefixes.
- lowering/exprSimStorageCopyScript.sml: existing copy execution/layout/content
  lemmas, original necessary locals already exported. Reuse them.
- lowering/bodyStorageCopyMemoryScript.sml: checked singleton and seven-instruction
  memory prefixes; complete copy loop and typed aggregate consumer remain owed.
- lowering/bodyAllocMemoryScript.sml, bodyImmutableUnwrapMemoryScript.sml,
  bodyToplevelAggregateMemoryScript.sml: checked old-schema allocation/runtime
  immutable-copy consumers needing counted migration, not fresh proof products.

## Notes

Owner checkpoint af7cdb885 passed two-target canonical-copy reuse validation
1232.081s before the counted join abef7cc21. The old fixed-result freeze was
byteidentical 02d899a8a until that approved join. Do not count removed duplicate
layout/copy-prefix proofs as new results. Current source does not yet build
under counted judgments. Preserve the S47 handoff, reconcile obsolete blocked
exports and old freezes with this task, and continue from the actual source.
