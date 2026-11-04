# TASK: Repair the lowering simulation proofs after describing values at post_value_type

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root

## Theorem Statement (FROZEN)

Every theorem statement in the target theories below is frozen: prove each
one as it stands. The change being absorbed is in the definitions only
(commit 8a210f067, `lowering/exprSimScript.sml` and
`lowering/exprSimHypsScript.sml`):

```sml
Definition post_value_type_def[simp]:
  post_value_type cenv (Call ty (IntCall fid) args drv) =
    (if is_word_type ty \/ is_bytestring_type ty then ty
     else lowered_value_type cenv (Call ty (IntCall fid) args drv)) /\
  post_value_type cenv e = expr_type e
End
```

- `expr_post_def`: `expr_val_rel cx (post_value_type cenv e) ...` and
  `expr_val_at cenv cx (post_value_type cenv e) ...` (were `expr_type e`).
- `vv_post_def`: `vv_holds cenv cx (post_value_type cenv e) ...` and
  `vv_at cenv cx (post_value_type cenv e) ...` (were `expr_type e`).
- `vv_holds_def`, `LocatedValue` clause: `t' = t` became
  `(t' = t \/ p.ptr_location = LocMemory /\ is_bytestring_type t /\ is_bytestring_type t')`.
- `expr_sim_inv_def` gained the conjunct
  `!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==> cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty`.
- [simp] helpers: `post_value_type_word`, `post_value_type_bytestring`,
  `post_value_type_not_int_call` (exprSim), `post_value_type_no_calls`
  (exprSimHyps: `int_calls_expr e = [] ==> post_value_type cenv e = expr_type e`).

**Do not modify these definitions or any exported theorem statement.**
Prove each statement as-is, or produce a counterexample. A helper marked
`[local]` may be restated if its only consumers are in its own theory.

## Completion Criteria

1. `holbuild -j4 build <targets>` (targets below) passes at the default
   tactic timeout with proof steps on.
2. No new `cheat`: the theorems cheated at the start (list in Notes) stay
   as they are; no other theorem is cheated, and none of those lists grows.
3. No new axioms, no `TRY`/`ORELSE` around `metis_tac` or other search, no
   timeout overrides.

**If an exported statement is false after the change** (e.g. it concludes a
fact at `expr_type e` for an operand that may be an internal call with a
widened aggregate type): stop on that theorem, record the statement and the
counterexample in LEARNINGS, and go on with the others. Do NOT weaken or
restate it.

Known in advance: the tuple-base subscript (\`compile_subscript_tuple_sim\`
and its users in exprSimPlaces / bodySimExprCases' \`body_subscript_case\`)
reads a widened internal-call tuple base at its annotation's offsets, so it
holds only when \`post_value_type cenv base_e = expr_type base_e\`. If that is
the only failure there, record it and move on; it is handled outside this
task.

## Build

```
holbuild -j4 build abiDecodeStaticPropsTheory bodyMemoryDefsTheory bodySimTheory bodySimEntryTheory bodySimExprCasesTheory ctorAbiActualTheory ctorAbiActualArrayBodyTheory ctorAbiActualArrayClosureTheory ctorAbiActualArrayContextTheory ctorAbiActualArrayEntryTheory ctorAbiActualArrayFiniteTheory ctorAbiActualArrayHeaderTheory ctorAbiActualArrayRunTheory ctorAbiActualRecursiveTheory entryArgPtrsTheory entryChecksPropsTheory entryDecodePlanPropsTheory entryDecodePropsTheory entryDecodeStaticPropsTheory entryDecodeStructureTheory entryHaltMemTheory entrySinkExtractionTheory entryStateRelTheory exprOpenCasesTheory exprOpenCopiesTheory exprOpenDispatchTheory exprOpenFirstOperandTheory exprOpenMainTheory exprOperandVarTheory exprReasonOperandTheory exprSafeOperandTheory exprSafeOperandBuiltinsTheory exprSimTheory exprSimAccountsTheory exprSimAggregateChildrenTheory exprSimAggregateLayoutTheory exprSimAggregateLoopsTheory exprSimAggregateSourceTheory exprSimAggregatesTheory exprSimArithTheory exprSimArrayIndexTheory exprSimAttributeTheory exprSimAttributeFieldsTheory exprSimBinopFragTheory exprSimBufferTheory exprSimBufferEmptyExecTheory exprSimBufferStoreTheory exprSimBuiltinsTheory exprSimCalldataTheory exprSimCalldataSliceTheory exprSimCallsTheory exprSimCompareTheory exprSimConvertTheory exprSimCopyTheory exprSimECArithTheory exprSimHashTheory exprSimHypsTheory exprSimIfExpTheory exprSimLeavesTheory exprSimLenTheory exprSimLiteralBufferTheory exprSimMainTheory exprSimMemoryTransportTheory exprSimOperandsTheory exprSimOperatorsTheory exprSimOpsTheory exprSimPlacesTheory exprSimPopTheory exprSimPrecompilesTheory exprSimSendTheory exprSimStorageCopyTheory exprSimTupleTheory exprSimUnopTheory exprSimUnwrapTheory exprSimWordArgsTheory exprSimWordBuiltinsTheory exprWordOperandTheory freshWritesTheory intCallArgsTheory intCallResultTheory intCallReturnTheory intCallReturnMemTheory stmtPoppedKeysTheory stmtSimTheory stmtSimAssignTheory stmtSimAssignStoreTheory stmtSimAugAssignTheory stmtSimDeclTheory stmtSimDeclStoreTheory stmtSimForTheory stmtSimForLoopTheory stmtSimForPartsTheory stmtSimForRangeTheory stmtSimIfTheory stmtSimLogTheory stmtSimReasonTheory stmtSimReasonCodeTheory stmtSimReasonExprTheory stmtSimReasonStorageTheory stmtSimReturnTheory storageCopyLiveTheory targetPlaceSimTheory targetPlaceSimCasesTheory tupleLoadPropsTheory tupleMemoryFrameTheory tupleMemoryLayoutTheory valueCopyTheory valueCopyBytesTheory valueCopySourceTheory
```

## Background

An internal call's result buffer is laid out at the callee's declared return
type, which a widening call site annotates with a wider type of another
stride (`DynArray[Bytes[32], 2]` used as `DynArray[Bytes[64], 2]`). The
postconditions now describe such a value at `post_value_type`. For every
call-free expression (`int_calls_expr e = []`), every word and every
bytestring `post_value_type cenv e = expr_type e`, so most proofs need only
that rewrite. A common break: `fs[expr_post_def]` leaves
`post_value_type cenv e` unrewritten because the fact that discharges the
[simp] lemma's condition comes later in the assumption list; `rfs[]` after it,
or an explicit `post_value_type_word`/`post_value_type_no_calls` step, fixes
it (see `lowering/exprSimOpsScript.sml` lines 505 and 523). Producers of
`expr_sim_inv` for a changed env must carry the new fn_sigs conjunct: env
updates in the statement sims change `var_types`, not `fn_sigs`.

## Domain Constraints

- Change proofs only. Prefer the shortest fix; keep each step under the
  2.5 s tactic timeout (split steps, cut rewrite sets).
- Don't edit `lowering/defs/`, `semantics/`, or these five theories,
  which another job is repairing: stmtSimDeclMem, memoryLocalRhsProps,
  stmtSimAssignStorageCopy, bodySimStmtCases, bodySimDeclCases.
- Never `holbuild run`/`repl`; probe with a scratch lemma in a theory you build.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Changed defs | lowering/exprSimScript.sml, lowering/exprSimHypsScript.sml | post_value_type, expr_post, vv_holds, vv_post, expr_sim_inv |
| Example fixes | lowering/exprSimOpsScript.sml:505,523 | rfs[] after fs[expr_post_def] |
| lowered_value_type | lowering/defs/exprLoweringScript.sml:161 | the lowering's physical type of a value |
| Typing link | lowering/exprSimHypsScript.sml, post_value_type_widens | \`expr_sim_inv\` + \`well_typed_expr\` give \`type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)\`; with \`arg_type_fits_def\`/\`type_widens_to_def\` (semantics/type/vyperTypeSystemScript.sml:622-643), equality for types without a Dynamic bound |
| Repo conventions | AGENTS.md | proof style, naming |

## Notes

Theorems cheated at the start (reference; approximate scan):

```
bodySimDeclCasesScript.sml: body_annassign_other:
bodySimDeclCasesScript.sml: body_annassign_widened_aggregate_call:
bodySimDeclCasesScript.sml: body_for_other:
bodySimExprCasesScript.sml: body_bop_in_literal_case:
bodySimExprCasesScript.sml: body_create_case:
bodySimExprCasesScript.sml: body_extcall_case:
bodySimExprCasesScript.sml: body_ifexp_case:
bodySimExprCasesScript.sml: body_ifexp_widened_call_arm:
bodySimExprCasesScript.sml: body_intcall_case:
bodySimExprCasesScript.sml: body_make_array_widened_call_elem:
bodySimExprCasesScript.sml: body_pop_nested_case:
bodySimExprCasesScript.sml: body_raw_call_calldata_case:
bodySimExprCasesScript.sml: body_raw_call_case:
bodySimExprCasesScript.sml: body_raw_log_case:
bodySimExprCasesScript.sml: body_raw_revert_case:
bodySimExprCasesScript.sml: body_selfdestruct_case:
bodySimExprCasesScript.sml: body_struct_lit_widened_call_elem:
bodySimStmtCasesScript.sml: body_append_storage_other:
bodySimStmtCasesScript.sml: body_assign_other:
bodySimStmtCasesScript.sml: body_assign_tuple_other:
bodySimStmtCasesScript.sml: body_assign_tuple_widened_call[local]:
bodySimStmtCasesScript.sml: body_assign_widened_aggregate_call:
bodySimStmtCasesScript.sml: body_augassign_other:
e2eCorrectnessScript.sml: e2e_deploy_correctness:
e2eCorrectnessScript.sml: evm_correspondence_to_call_result[local]:
exprSimAggregatesScript.sml: compile_abi_decode_case:
exprSimAggregatesScript.sml: compile_abi_encode_case:
exprSimAggregatesScript.sml: compile_convert_other_case:
exprSimBinopFragScript.sml: binop_frag_pow:
exprSimBinopFragScript.sml: binop_frag_shift_572:
exprSimBinopFragScript.sml: binop_frag_shr_narrow:
exprSimBuiltinsScript.sml: compile_acc_code_case:
exprSimBuiltinsScript.sml: compile_blockhash_case:
exprSimBuiltinsScript.sml: compile_concat_case:
exprSimBuiltinsScript.sml: compile_extract32_case:
exprSimBuiltinsScript.sml: compile_len_ctor_code_case:
exprSimBuiltinsScript.sml: compile_slice_case:
exprSimBuiltinsScript.sml: compile_uint2str_case:
exprSimCallsScript.sml: compile_create_sim:
exprSimCallsScript.sml: compile_extcall_sim:
exprSimCallsScript.sml: compile_raw_call_calldata_sim:
exprSimCallsScript.sml: compile_raw_call_sim:
exprSimCallsScript.sml: compile_raw_log_sim:
exprSimCallsScript.sml: compile_raw_revert_sim:
exprSimCallsScript.sml: compile_selfdestruct_sim:
exprSimCopyScript.sml: unwrap_ctor_code_copy_sim:
exprSimIfExpScript.sml: compile_expr_ifexp:
exprSimIfExpScript.sml: compile_ifexp_vv_sim:
exprSimLeavesScript.sml: compile_msg_gas_sim:
exprSimLeavesScript.sml: compile_prevhash_sim:
exprSimOperatorsScript.sml: compile_bop_in_literal_sim:
exprSimOperatorsScript.sml: compile_bop_rest_case:
exprSimOperatorsScript.sml: compile_ifexp_aggregate_case:
exprSimOperatorsScript.sml: compile_ifexp_case:
exprSimOperatorsScript.sml: compile_ifexp_word_case:
exprSimOperatorsScript.sml: compile_neg_case:
exprSimPlacesScript.sml: compile_pop_immutable_sim:
exprSimPlacesScript.sml: compile_pop_nested_sim:
exprSimPlacesScript.sml: compile_pop_storage_sim:
exprSimPlacesScript.sml: compile_subscript_array_case:
exprSimPlacesScript.sml: compile_subscript_map_case:
exprSimUnwrapScript.sml: unwrap_ctor_immutable_word_sim:
loweringMemCorrectScript.sml: body_stmts_sim_mem:
loweringMemCorrectScript.sml: external_entry_reaches_body_mem:
loweringMemCorrectScript.sml: external_entry_value_revert_mem:
loweringMemCorrectScript.sml: external_frame_ret_ok_mem:
loweringRuntimeCorrectScript.sml: external_body_frame:
loweringRuntimeCorrectScript.sml: external_body_revert_data_reverts:
loweringRuntimeCorrectScript.sml: external_body_source_ok:
loweringRuntimeCorrectScript.sml: external_entry_reaches_body:
loweringRuntimeCorrectScript.sml: external_entry_value_revert:
loweringRuntimeCorrectScript.sml: external_frame_ret_ok:
loweringRuntimeCorrectScript.sml: stmts_env_ret_ty:
stmtSimLogScript.sml: compile_log_stmt_frag:
targetPlaceSimCasesScript.sml: target_subscript_case:
vyperLoweringCorrectScript.sml: lower_vyper_runtime_unit_o1_shape_extras:
vyperLoweringCorrectScript.sml: vyper_to_venom_correct:
```
