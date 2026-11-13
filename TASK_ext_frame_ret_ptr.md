# TASK: pointer safety of an external function's return statements

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (target script lowering/extFrameRetOkPtrScript.sml)

## Theorem Statement (FROZEN)

In lowering/extFrameRetOkPtrScript.sml:

```sml
Theorem external_frame_ret_ok_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    frame_ret_ok_ptr NONE unit.cu_context [] func
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\v es gt r. T) cenv ret
```

The judgment `frame_ret_ok_ptr` (and `stmt_frag_ptr`, `stmt_exit_ptr`,
`ghost_inv`, `expr_sim_ptr`, `expr_vv_sim_ptr`, `ptr_val_ok`, `ptr_mem_ok`,
`cx_dead`, `frag_exec_ptr`) is in lowering/bodyPtrDefsScript.sml; the
counted paths `gas_path_ptr`, `gas_outcome_ptr` in
lowering/fragGasPathPtrScript.sml; the per-step check `ptr_safe_step`,
`ptr_inst_ok` in venom/compiler/ptrSafeRunScript.sml, with `access_ok`,
`taint_ok`, `ret_taint`, `step_taint` in venom/compiler/ptrDisciplineScript.sml.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build extFrameRetOkPtrTheory` passes, with no `cheat` or
   `suspend` in lowering/extFrameRetOkPtrScript.sml or in any extRet* theory
   you add. `external_frame_ret_widened_ptr` (lowering/extRetWidenedPtrScript.sml)
   is proved by a separate run: use it as stated, don't edit that file.
2. Helpers go in new leaf theories in lowering/ that extFrameRetOkPtr
   imports (add them to its `Ancestors`). Do not edit any other existing
   file: not bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, fragGasSeqPtr,
   gasSummaryComposePtr, the ptr toolkit theories (entryHaltPtr,
   representationCleanPtr, returnMetadataPtr, typedCopy*Ptr, ...),
   ptrSafeRun, ptrDiscipline, the S1 theories, semantics/ or lowering/defs/.
   If you need one changed, stop and report the exact change and why.
3. No duplicate lemmas: search before adding one; reuse what exists.
4. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with
   `>~`, `>-`, `>|`. No step near the 2.5 s tactic timeout (never raise it).

**If the theorem is false as stated:** give a concrete counterexample and
the tightest fix. Do NOT weaken the statement.

## Build

```
holbuild -j4 build extFrameRetOkPtrTheory extRetWidenedPtrTheory extRetReturnMetadataPtrTheory extRetAbiArrayBackedgePtrTheory extRetAbiArrayHeaderPtrTheory extRetAbiArrayInitPtrTheory extRetAbiArrayParentPtrTheory extRetAbiArrayStaticBodyPtrTheory extRetAbiArrayStaticCountedPtrTheory extRetAbiArrayStaticLoopPtrTheory extRetAbiBytesArithPtrTheory extRetAbiBytesCountedPtrTheory extRetAbiBytesHeaderPtrTheory extRetAbiBytesLivePtrTheory extRetAbiChildBoundaryPtrTheory extRetAbiChildComposePtrTheory extRetAbiReadBoundsPtrTheory extRetAbiReadCleanPtrTheory extRetAbiReturnConsumerPtrTheory extRetAbiSingletonCountedPtrTheory extRetAbiSingletonLivePtrTheory extRetAbiSingletonReturnPtrTheory extRetAbiSingletonWrapperPtrTheory extRetAbiSourceArrayDispatchPtrTheory extRetAbiSourceArrayStaticCountedPtrTheory extRetAbiSourceBytesCountedPtrTheory extRetAbiSourceChildPtrTheory extRetAbiSourceComplexBytesPtrTheory extRetAbiSourceComplexDispatchPtrTheory extRetAbiSourceInputPtrTheory extRetAbiSourceStaticCountedPtrTheory extRetAbiStaticCountedPtrTheory extRetAbiStorageFramePtrTheory extRetAbiWrappedSourcePtrTheory extRetBufferAllocCountedPtrTheory extRetBufferCursorStatePtrTheory extRetBufferStatePtrTheory extRetBulkCopyCountedPtrTheory extRetBytesCopyCountedPtrTheory extRetCapacityAuditPtrTheory extRetCapacityFramePtrTheory extRetCopyCountedPtrTheory extRetCopyInputsPtrTheory extRetCopySuffixPtrTheory extRetCountedPtrTheory extRetCursorResourcePtrTheory extRetDispatchProtectionPtrTheory extRetDispatchResultPtrTheory extRetEvaluatedStaticPtrTheory extRetFrameFactsPtrTheory extRetLoweredBytesFramePtrTheory extRetNoneFramePtrTheory extRetNormalEvidencePtrTheory extRetOperandBoundaryPtrTheory extRetPointwiseSourcePtrTheory extRetRawFramePtrTheory extRetRawStmtPtrTheory extRetRawValuePtrTheory extRetRecursiveContractAuditPtrTheory extRetRecursivePlanPtrTheory extRetRobustSourceChildrenPtrTheory extRetScalarCopyCountedPtrTheory extRetScratchInitPtrTheory extRetScratchResourceInitPtrTheory extRetScratchResourcePtrTheory extRetSignatureFramePtrTheory extRetSingletonCapacityPtrTheory extRetSingletonFramePtrTheory extRetSingletonStmtPtrTheory extRetSingletonWordCapacityPtrTheory extRetSomeComposePtrTheory extRetSourceAllocationPtrTheory extRetSourceWindowPtrTheory extRetStaticBoundedConsumerPtrTheory extRetStaticCapacityPtrTheory extRetStaticFrameConsumerPtrTheory extRetStaticFrameMetadataPtrTheory extRetStaticLoweredFramePtrTheory extRetStaticPlanSelectionPtrTheory extRetStaticReservedPtrTheory extRetStaticStmtPtrTheory extRetSupportedShapePtrTheory extRetTypedStaticConsumerPtrTheory extRetWordConsumerPtrTheory extRetWordExactStmtPtrTheory extRetWordExprConsumerPtrTheory extRetWordFramePtrTheory extRetWordInputsPtrTheory extRetWordStmtPartsPtrTheory extRetWordStmtPtrTheory extRetWordSuffixPtrTheory extRetZeroStmtPtrTheory
```
(from the project root, the directory containing holproject.toml).

## Background

S3 of the Vyper compiler correctness proof shows the lowered code is
pointer-safe: every memory access stays inside the allocation its pointer
came from, and data from not-yet-written allocation bytes (taint) reaches
only dead bytes. The body induction (lowering/bodySimPtrMainScript.sml,
`body_sim_ptr_mutual`) takes `frame_ret_ok_ptr` as a hypothesis for the
`Return` statement; this theorem discharges it for the external function's
frame (`d = NONE`, `PG = []`, `RetQ` trivially true). So the content is:
each `Return eo` the frame can execute, lowered by `stmt_env` /
`compile_stmt` (lowering/defs/stmtLoweringScript.sml, `Return` clauses
near line 1005; `compile_external_return` near line 338; ABI encoder in
lowering/defs/abiEncoderScript.sml), runs along a pointer-safe counted path
to its halt, and the RETURN's returned memory range holds no tainted byte
(`cx_dead`'s `d_ret` is empty).

The S1 (simulation) twin `loweringRuntimeCorrect$external_frame_ret_ok` and
the memory-safety twin are themselves still admitted, so there is no whole
proof to replay; their per-branch fragment lemmas are proved (below).

## Domain Constraints

- The ptr judgments conclude counted paths (`gas_outcome_ptr` over
  `gas_path_ptr`). The ptr toolkit lemmas are stated over the fixed-run
  `frag_exec_ptr`; use them for per-instruction pointer facts and build
  the counted paths with the combinators of fragGasSeqPtr and
  gasSummaryComposePtr.
- Five return-metadata lemmas of an older branch were not ported because
  `supportedPlaceAssignable$supported_nested_type_assignable` is false (an
  empty struct is supported but not assignable). If you need an
  `assignable_type` fact, take it as a premise of your helper and
  discharge it from the context; don't port those as stated.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target | lowering/extFrameRetOkPtrScript.sml | the theorem; intuition in comments |
| Ptr judgments | lowering/bodyPtrDefsScript.sml | frame_ret_ok_ptr, stmt_frag_ptr, ghost_inv, expr_sim_ptr, frag_exec_ptr |
| Counted ptr paths | lowering/fragGasPathPtrScript.sml, lowering/fragGasSeqPtrScript.sml, lowering/gasSummaryComposePtrScript.sml, lowering/gasPathPtrExecScript.sml | gas_path_ptr, run_inst_seq_gas_path_ptr, inst_seq_ptr, gas_outcome_ptr_bind/_bind_normal/_prefix/_conseq, gas_path_ptr_exec |
| How sibling ptr cases use them | lowering/bodySimPtrMainScript.sml, lowering/bodyPtr*CasesScript.sml, lowering/exprSimPtrScript.sml | the body induction and its case statements |
| Ptr check | venom/compiler/ptrSafeRunScript.sml, venom/compiler/ptrDisciplineScript.sml | ptr_safe_step, ptr_inst_ok, access_ok, taint_ok, ret_taint, new_site_bytes, written_taint |
| Ptr return fragments (proved) | lowering/entryHaltPtrScript.sml | Return NONE (STOP), prim word, AbiCopy static copy, AbiCopy 0 |
| Clean value bytes | lowering/representationCleanPtrScript.sml | ptr_val_ok_static_clean and bytes/string cases |
| Return metadata | lowering/returnMetadataPtrScript.sml, lowering/retAbiPlanPropsScript.sml | ret enc info / max size from the package, struct fields |
| Other ptr toolkit | lowering/fragExecPtrScript.sml, lowering/typedCopy*PtrScript.sml, lowering/wordCopyRobustPtrScript.sml, lowering/robustCopyTransportPtrScript.sml, lowering/ghostPcTransportPtrScript.sml, lowering/allocationPtrScript.sml, lowering/ptrCoverageScript.sml, lowering/ptrSafetyTransportScript.sml | per-instruction ptr facts: allocas, copies, stores, ghost transport |
| S1 external return fragments (proved) | lowering/loweringHaltScript.sml (compile_external_return_abi_unlock_frag ~l.1553), lowering/rawReturnCorrectScript.sml, lowering/rawReturnHaltScript.sml, lowering/stmtSimReturnWidenScript.sml (compile_return_normalize_frag), lowering/stmtSimReturnScript.sml, lowering/vyperLoweringCorrectScript.sml (external_return_*_result_rel) | the runs of each return branch, without the ghost |
| S1 ABI encoder proofs | lowering/abiEncoder*Script.sml | runs of compile_abi_encode_to_buf: bytes, dynamic arrays, complex, loops |
| Memory-safety twins (proved fragments) | lowering/entryHaltMemScript.sml, lowering/rawReturnMemScript.sml, lowering/abiEncoderArrayDynamicMemoryScript.sml | same branches with the memory check in place of the ptr check |
| Where the theorem is used | lowering/loweringPtrCorrectScript.sml | composition into the S3 statement |
| Supported subset | lowering/supported/supportedDeclsScript.sml, supportedTypesScript.sml, supportedProgramScript.sml | supported_program forces nr = F; return types are NoneT or supported_place_type |

## Notes

A read of the sources (not a build) found these branches reachable for
this frame: Return NONE (STOP), prim word, raw return (`rr` forces a Bytes
return), AbiCopy static, dynamic encode (AbiBytestring / AbiDynArray /
AbiComplex, the return wrapped in a one-element tuple), and the
`needs_normalize` widening copy (a dynamic non-bytestring value returned at
a wider declared type). No counterexample was found: in each branch the
bytes in the RETURN range are written with untainted data first.

## Repairs first (2026-11-13, merged train-16 head 8af3fb5d5)

These ported leaves fail on this base and are part of this run's work
(proof-only; helper statements in extRet* leaves you own may change, frozen
statements may not). Build the target's cone to see them:

- `extRetBytesCopyCountedPtr` (`compile_bytestring_copy_len_counted_ptr`):
  `compile_bytestring_copy_len` now rounds with a `NOT 31` mask and a
  different operand order (lowering/defs). About 80 leaves wait on it.
- `extRetRawStmtPtr` (`external_return_raw_stmt_parts`) and the raw-return
  leaves after it: the raw return now allocates a buffer, stores the value
  with `compile_store_memory_typed`, then calls `compile_external_return`.
- `extRetFrameFactsPtr` (`supported_lookup_external_raw_decl`): public
  variables are now supported, and `lookup_function ... External` returns
  their getters (`VariableDecl (Public nr)` clauses of `lookup_function_def`),
  so the lemma is false as stated. The target's frozen premise
  `lookup_function NONE tx.function_name External tops = SOME (...)` now
  covers getter functions too; their bodies are a single `Return (SOME ne)`
  of a top-level read.
- Any leaf behind these that then fails.

## State at the 2026-11-12 port

This branch ports the earlier frame-ret work onto the merge-train-16 head.
Every extRet* leaf is proved. Two admissions remain:

- the equal-type `cheat` in `external_frame_ret_ok_ptr`
  (`lowered_value_type cenv' x = expr_type x`, the non-widened `Return (SOME x)`
  branch not already covered by the static-copy lemmas above it): this run's
  work;
- `external_frame_ret_widened_ptr` in lowering/extRetWidenedPtrScript.sml:
  another run's.

Train 16 changed the package call in the statement: external functions are
now packaged with `use_trans = T` and the key map `K global_nonreentrant_slot`
(was `F`, `assign_nkeys tops 0`), and public variables are supported (getters).
Decision 18 holds: `expr_sim_ptr`/`expr_vv_sim_ptr` give `ptr_val_ok` at
`post_value_type cenv e` (lowering/loweringPostsScript.sml).

- Two constants are named `ceil32` (contractABI's and venomLayout's). Where a
  leaf means the ABI one, add `Overload ceil32[local] = “contractABI$ceil32”`.
- An Ancestors entry opens only that theory's names: a lemma used
  unqualified must come from a theory listed directly.
