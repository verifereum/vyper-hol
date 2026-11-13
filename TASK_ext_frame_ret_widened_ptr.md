# TASK: pointer safety of an external function's widened return

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root (target script lowering/extRetWidenedPtrScript.sml)

## Theorem Statement (FROZEN)

In lowering/extRetWidenedPtrScript.sml:

```sml
Theorem external_frame_ret_widened_ptr:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, F, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr, key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  get_tenv cx = type_env tops /\
  expr_sim_inv next cx env es /\
  stmt_exprs_ok next (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  expr_sim_ptr d ctx PG func next cx (expr_type e) e es /\
  expr_vv_sim_ptr d ctx PG func next cx (expr_type e) e es /\
  lowered_value_type next e <> expr_type e ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) next
    (stmt_env next lctx ret (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
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

1. `holbuild -j4 build extRetWidenedPtrTheory` passes, with no `cheat` or
   `suspend` in lowering/extRetWidenedPtrScript.sml or in any extRet* theory
   you add. lowering/extFrameRetOkPtrScript.sml and the extRet* leaves it
   imports are another run's work (several need repair on this base): don't
   build or edit them.
2. Helpers go in new leaf theories in lowering/ that extRetWidenedPtr imports
   (add them to its `Ancestors`). Do not edit any other existing file: not
   extFrameRetOkPtr, bodyPtrDefs, bodyPtrPreds, fragGasPathPtr, fragGasSeqPtr,
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
holbuild -j4 build extRetWidenedPtrTheory
```
(from the project root, the directory containing holproject.toml).

## Background

S3 of the Vyper compiler correctness proof shows the lowered code is
pointer-safe: every memory access stays inside the allocation its pointer
came from, and data from not-yet-written allocation bytes (taint) reaches
only dead bytes. The body induction (lowering/bodySimPtrMainScript.sml,
`body_sim_ptr_mutual`) takes `frame_ret_ok_ptr` as a hypothesis for the
`Return` statement; `external_frame_ret_ok_ptr` discharges it for the external function's
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
| Target | lowering/extRetWidenedPtrScript.sml | the theorem; its user is the widened branch at the end of lowering/extFrameRetOkPtrScript.sml |
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

## State at the 2026-11-12 port

This branch ports the earlier frame-ret work onto the merge-train-16 head.
Every extRet* leaf is proved. Two admissions remain:

- the equal-type `cheat` in `external_frame_ret_ok_ptr`
  (`lowered_value_type cenv' x = expr_type x`, the non-widened `Return (SOME x)`
  branch not already covered by the static-copy lemmas above it): another
  run's;
- `external_frame_ret_widened_ptr` in lowering/extRetWidenedPtrScript.sml
  (`Return (SOME e)` where `lowered_value_type next e <> expr_type e`, a
  widened internal call read by Return's normalize branch): this run's work.
  extRetWidenedCallEvidence shows why it failed before Decision 18 and is
  reference only.

Train 16 changed the package call in the statement: external functions are
now packaged with `use_trans = T` and the key map `K global_nonreentrant_slot`
(was `F`, `assign_nkeys tops 0`), and public variables are supported (getters).
Decision 18 holds: `expr_sim_ptr`/`expr_vv_sim_ptr` give `ptr_val_ok` at
`post_value_type cenv e` (lowering/loweringPostsScript.sml).

- Two constants are named `ceil32` (contractABI's and venomLayout's). Where a
  leaf means the ABI one, add `Overload ceil32[local] = “contractABI$ceil32”`.
- An Ancestors entry opens only that theory's names: a lemma used
  unqualified must come from a theory listed directly.
