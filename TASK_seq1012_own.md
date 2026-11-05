# TASK: Repair the lowering simulation proofs after the expr_val_own conjunct in expr_post/vv_post

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

Every theorem statement in the target theories is frozen: prove each one as
it stands. The change being absorbed is in the definitions only
(`lowering/loweringPostsScript.sml`, commit 75231b5b4):

- New `expr_val_own_def` / `vv_own_def`: `expr_val_at_def` / `vv_at_def`
  without the local-region disjunct (the value sits in one of the
  expression's own allocations, clear of every live local, or has
  footprint 0), and without the `val_wf` conjunct.
- `expr_post_def` gains, after the `expr_val_at` conjunct,
  `(post_value_type cenv e <> expr_type e ==> expr_val_own cenv cx (post_value_type cenv e) sa sb es' v op s)`.
- `vv_post_def` gains, after the `vv_at` conjunct,
  `(post_value_type cenv e <> expr_type e ==> vv_own cenv cx (post_value_type cenv e) sa sb es' tv vv s)`.

Why: only an internal call whose value is laid out at the callee's declared
return type (post_value_type differs from expr_type) has a non-trivial
conjunct; its value is its own return buffer. `exprSimLayoutTransport`'s
`expr_val_at_layout_transport` already uses it, and `exprSim` builds.

**Do not modify these definitions or any exported theorem statement**,
except as below.

## Completion Criteria

1. `holbuild -j4 build <targets>` (Build below) passes at the default tactic
   timeout with proof steps on.
2. No new `cheat`: the theorems cheated at the start (Notes) stay as they
   are; no other theorem is cheated.
3. No new axioms, no `TRY`/`ORELSE` around `metis_tac` or other search, no
   timeout overrides.

**Approved exceptions (the only allowed statement changes).**
- A helper that concludes `expr_post`/`vv_post` of an arbitrary expression `e`
  may gain exactly one hypothesis, `post_value_type cenv e = expr_type e`,
  where every consumer discharges it (`post_value_type_no_calls`,
  `post_value_type_word`, `post_value_type_bytestring`,
  `post_value_type_not_int_call`, `post_value_type_lowered`, or a hypothesis
  in scope).
- Otherwise, prove the new conjunct. A copy into a fresh buffer of the
  expression's own (the unwrap/copy helpers) gets `expr_val_own` from the
  same allocation witness that gives `expr_val_at`'s first disjunct. A post
  of `e` concluded from a post of the same `e` and operand carries it (it is
  monotone in the end compile state like `expr_val_at`; reuse the
  `expr_val_at` frame lemmas' proofs).
List every helper you changed in LEARNINGS. If a consumer can do neither,
record it in LEARNINGS and move on.

## Repair patterns

- Destructuring (`fs[expr_post_def]`) gains an assumption; nothing to do.
- Concluding a post for a concrete non-IntCall constructor: the conjunct is
  `expr_type x <> expr_type x ==> ...` after `post_value_type_def` [simp];
  `simp[]` closes it. For a StackValue vv add `vv_own_def` beside `vv_at_def`
  (see `expr_vv_sim_stack` in exprSim, line ~791).
- Word results (`is_word_type`): `post_value_type_word` makes the conjunct T.
- Wherever a proof destructures `expr_val_at_def`/`vv_at_def` to rebuild it
  (frame, start/end-counter monotonicity), do the same for the own forms.

## Build

```
holbuild -j4 build abiDecodeStaticPropsTheory abiEncoderWindowArrayTheory abiEncoderWindowArrayBodyTheory abiEncoderWindowArrayEntryTheory abiEncoderWindowArrayExitTheory abiEncoderWindowArrayFinishTheory abiEncoderWindowArrayInvariantTheory abiEncoderWindowArrayLoopTheory abiEncoderWindowArrayRoundTheory abiEncoderWindowBytesTheory abiEncoderWindowChildTheory abiEncoderWindowComplexTheory abiEncoderWindowCursorTheory abiEncoderWindowMembersTheory abiEncoderWindowPhaseTheory abiEncoderWindowRunTheory abiEncoderWindowSequenceTheory abiEncoderWindowSourceTheory abiEncoderWindowSourceRunTheory abiEncoderWindowStructuralMembersTheory appendStorageRelTheory bodyAppendStorageAdapterTheory bodyAppendStorageFactsTheory bodyExprPreFactsTheory bodyMemoryDefsTheory bodySimTheory bodySimDeclCasesTheory bodySimEntryTheory bodySimExprCasesTheory bodySimLogTheory bodySimMainTheory bodySimStmtCasesTheory calldataAggregateTypedTheory calldataBulkLeafTheory calldataBulkLiveTheory calldataBytesLeafTheory calldataBytesLiveTheory calldataDynInitTheory calldataDynOwnedTheory calldataDynStepTheory calldataFiniteTypedTheory calldataMembersTheory calldataReconstructionTheory calldataRecursiveExecutionTheory calldataRecursiveProducersTheory calldataRegistrationTheory calldataRegistrationExecTheory calldataRegistrationLocalsTheory calldataWordLeafTheory calldataWordLiveTheory configuredE2ECorrectnessTheory convertScalarBridgeTheory convertScalarBytesTheory convertScalarBytesRunTheory convertScalarChecksTheory convertScalarDecimalTheory convertScalarDecimalFragTheory convertScalarDecimalRunTheory convertScalarDispatchTheory convertScalarEncodingTheory convertScalarFlagsTheory convertScalarOutputsTheory convertScalarPropsTheory convertScalarSimTheory convertScalarTypingTheory ctorAbiActualTheory ctorAbiActualArrayBodyTheory ctorAbiActualArrayClosureTheory ctorAbiActualArrayContextTheory ctorAbiActualArrayEntryTheory ctorAbiActualArrayFiniteTheory ctorAbiActualArrayHeaderTheory ctorAbiActualArrayRunTheory ctorAbiActualRecursiveTheory ctorArgDecodeTheory ctorRegisterArgsTheory e2eCallChecksTheory e2eCompositionChecksTheory e2eCorrectnessTheory entryArgPtrsTheory entryChecksPropsTheory entryDecodePlanPropsTheory entryDecodePropsTheory entryDecodeStaticPropsTheory entryDecodeStructureTheory entryHaltMemTheory entrySinkExtractionTheory entryStateRelTheory exprOpenCasesTheory exprOpenCopiesTheory exprOpenDispatchTheory exprOpenFirstOperandTheory exprOpenMainTheory exprOperandVarTheory exprReasonOperandTheory exprSafeOperandTheory exprSafeOperandBuiltinsTheory exprSimTheory exprSimAccountsTheory exprSimAggregateChildrenTheory exprSimAggregateLayoutTheory exprSimAggregateLoopsTheory exprSimAggregateSourceTheory exprSimAggregatesTheory exprSimArithTheory exprSimArrayIndexTheory exprSimAttributeTheory exprSimAttributeFieldsTheory exprSimBinopFragTheory exprSimBufferTheory exprSimBufferEmptyExecTheory exprSimBufferStoreTheory exprSimBuiltinsTheory exprSimCalldataTheory exprSimCalldataSliceTheory exprSimCallsTheory exprSimCompareTheory exprSimConvertTheory exprSimConvertBytesTheory exprSimConvertFromBytesTheory exprSimConvertScalarTheory exprSimCopyTheory exprSimECArithTheory exprSimHashTheory exprSimHypsTheory exprSimIfExpTheory exprSimIfExpCompatTheory exprSimLayoutTransportTheory exprSimLeavesTheory exprSimLenTheory exprSimLiteralBufferTheory exprSimMainTheory exprSimMemoryTransportTheory exprSimOperandsTheory exprSimOperatorsTheory exprSimOpsTheory exprSimPlacesTheory exprSimPopTheory exprSimPopNestedTheory exprSimPopStorageTheory exprSimPrecompilesTheory exprSimSendTheory exprSimStorageCopyTheory exprSimTupleTheory exprSimUint2StrTheory exprSimUnopTheory exprSimUnwrapTheory exprSimWordArgsTheory exprSimWordBuiltinsTheory exprWordOperandTheory freshWritesTheory intCallArgsTheory intCallResultTheory intCallReturnTheory intCallReturnMemTheory loweringMemCorrectTheory loweringRuntimeCorrectTheory memoryLocalRhsPropsTheory rawReturnCorrectTheory rawReturnValueTheory stmtPoppedKeysTheory stmtSimTheory stmtSimAppendStorageTheory stmtSimAppendStorageComposeTheory stmtSimAssignTheory stmtSimAssignAttrTheory stmtSimAssignAttrStorageTheory stmtSimAssignMemTheory stmtSimAssignStorageTheory stmtSimAssignStorageCopyTheory stmtSimAssignStoreTheory stmtSimAssignTupleTheory stmtSimAssignTupleMemTheory stmtSimAssignTupleTargetsTheory stmtSimAugAssignTheory stmtSimAugAssignAttrTheory stmtSimAugAssignAttrStorageTheory stmtSimAugAssignStorageTheory stmtSimDeclTheory stmtSimDeclEmptyTheory stmtSimDeclMemTheory stmtSimDeclStoreTheory stmtSimForTheory stmtSimForArrayTheory stmtSimForArrayFragTheory stmtSimForArrayLoopTheory stmtSimForArrayPartsTheory stmtSimForLoopTheory stmtSimForPartsTheory stmtSimForRangeTheory stmtSimIfTheory stmtSimLogTheory stmtSimLogAllocateTheory stmtSimLogArgsTheory stmtSimLogArgsGrowthTheory stmtSimLogArgsRunTheory stmtSimLogComposeTheory stmtSimLogDataTheory stmtSimLogDataFrameTheory stmtSimLogDataInputTheory stmtSimLogDataRunTheory stmtSimLogEmitTheory stmtSimLogEncodeFieldsTheory stmtSimLogEncodeFrameTheory stmtSimLogEncodeLayoutTheory stmtSimLogMembersRunTheory stmtSimLogScalarEncodeTheory stmtSimLogScalarMembersTheory stmtSimLogScalarPrefixTheory stmtSimLogSourceTheory stmtSimLogSourceAllocateTheory stmtSimLogStoreComposeTheory stmtSimLogStoreContinueTheory stmtSimLogStoreEncodeTheory stmtSimLogStoreFreshTheory stmtSimLogSuffixTheory stmtSimLogSuffixActualTheory stmtSimLogSuffixCodeTheory stmtSimLogSuffixFrameTheory stmtSimLogTopicFreshTheory stmtSimLogTopicsTheory stmtSimLogTraceTheory stmtSimReasonTheory stmtSimReasonCodeTheory stmtSimReasonExprTheory stmtSimReasonStorageTheory stmtSimReturnTheory stmtSimReturnWidenTheory storageCopyLiveTheory storageStoreFrameTheory targetPlaceSimTheory targetPlaceSimCasesTheory tupleAssignCodeTheory tupleAssignMemoryTheory tupleAssignPartsTheory tupleAssignPrefixTheory tupleLoadPropsTheory tupleLocalStorePropsTheory tupleLocalStoreRunTheory tupleMemoryFrameTheory tupleMemoryLayoutTheory tupleStagePropsTheory tupleTargetStorePropsTheory tupleTargetStoreRunTheory tupleTypedLoadTheory typedMemoryCopyTheory valueCopyTheory valueCopyBytesTheory valueCopySourceTheory loweringPostsTheory
```

## Domain Constraints

- Change proofs only (and the two approved hypothesis forms). Prefer the
  shortest fix; keep each step under the 2.5 s tactic timeout.
- Don't edit `lowering/defs/` or `semantics/`.
- Never `holbuild run`/`repl`; probe with a scratch lemma in a theory you build.

## Notes

Theorems cheated at the start (these stay cheated; don't prove or touch them):

```
bodySimDeclCasesScript.sml: body_annassign_other
bodySimDeclCasesScript.sml: body_annassign_widened_aggregate_call
bodySimExprCasesScript.sml: body_bop_in_literal_case
bodySimExprCasesScript.sml: body_create_case
bodySimExprCasesScript.sml: body_extcall_case
bodySimExprCasesScript.sml: body_ifexp_widened_call_arm
bodySimExprCasesScript.sml: body_intcall_case
bodySimExprCasesScript.sml: body_make_array_widened_call_elem
bodySimExprCasesScript.sml: body_pop_nested_target_frag
bodySimExprCasesScript.sml: body_raw_call_calldata_case
bodySimExprCasesScript.sml: body_raw_call_case
bodySimExprCasesScript.sml: body_raw_log_case
bodySimExprCasesScript.sml: body_raw_revert_case
bodySimExprCasesScript.sml: body_selfdestruct_case
bodySimExprCasesScript.sml: body_struct_lit_widened_call_elem
bodySimExprCasesScript.sml: body_subscript_widened_call_base
bodySimStmtCasesScript.sml: body_assign_other
bodySimStmtCasesScript.sml: body_assign_tuple_other
bodySimStmtCasesScript.sml: body_assign_tuple_widened_call
bodySimStmtCasesScript.sml: body_assign_widened_aggregate_call
bodySimStmtCasesScript.sml: body_augassign_other
e2eCorrectnessScript.sml: e2e_deploy_correctness
e2eCorrectnessScript.sml: evm_correspondence_to_call_result
exprSimAggregatesScript.sml: compile_abi_decode_case
exprSimAggregatesScript.sml: compile_abi_encode_case
exprSimAggregatesScript.sml: compile_convert_other_case
exprSimBuiltinsScript.sml: compile_acc_code_case
exprSimBuiltinsScript.sml: compile_concat_case
exprSimBuiltinsScript.sml: compile_extract32_case
exprSimBuiltinsScript.sml: compile_slice_case
exprSimCallsScript.sml: compile_create_sim
exprSimCallsScript.sml: compile_extcall_sim
exprSimCallsScript.sml: compile_raw_call_calldata_sim
exprSimCallsScript.sml: compile_raw_call_sim
exprSimCallsScript.sml: compile_raw_log_sim
exprSimCallsScript.sml: compile_raw_revert_sim
exprSimCallsScript.sml: compile_selfdestruct_sim
exprSimLeavesScript.sml: compile_msg_gas_sim
exprSimOperatorsScript.sml: compile_bop_in_literal_sim
exprSimOperatorsScript.sml: compile_bop_rest_case
exprSimPlacesScript.sml: compile_subscript_array_case
exprSimPlacesScript.sml: compile_subscript_map_case
exprSimPopNestedScript.sml: pop_nested_expr_target_frag
exprSimPopNestedScript.sml: pop_nested_immutable_deploy_sim
exprSimPopNestedScript.sml: pop_nested_local_sim
exprSimPopNestedScript.sml: pop_nested_storage_effectful_sim
loweringMemCorrectScript.sml: body_stmts_sim_mem
loweringMemCorrectScript.sml: external_entry_reaches_body_mem
loweringMemCorrectScript.sml: external_entry_value_revert_mem
loweringMemCorrectScript.sml: external_frame_ret_ok_mem
loweringMemCorrectScript.sml: lower_vyper_runtime_unit_ptr_taint
loweringRuntimeCorrectScript.sml: external_body_frame
loweringRuntimeCorrectScript.sml: external_body_revert_data_reverts
loweringRuntimeCorrectScript.sml: external_body_source_ok
loweringRuntimeCorrectScript.sml: external_entry_reaches_body
loweringRuntimeCorrectScript.sml: external_entry_value_revert
loweringRuntimeCorrectScript.sml: external_frame_ret_ok
loweringRuntimeCorrectScript.sml: stmts_env_ret_ty
targetPlaceSimCasesScript.sml: target_subscript_case
vyperLoweringCorrectScript.sml: lower_vyper_runtime_unit_defs_reach_uses
vyperLoweringCorrectScript.sml: vyper_to_venom_correct
```
