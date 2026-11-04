# TASK: Repair the lowering simulation proofs after describing values at post_value_type (on #992's head)

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root

## Theorem Statement (FROZEN)

Every theorem statement in the target theories below is frozen: prove each
one as it stands. The change being absorbed is in the definitions only
(`lowering/exprSimScript.sml` and `lowering/exprSimHypsScript.sml`; this
branch is #992's squashed head f0338c81a plus the port commit 45f533868,
which already repairs most theories):

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
restate it, except as below.

**Approved exception (the only allowed statement change).** An exported
helper that relates `expr_post`/`vv_post` of an arbitrary expression `e` to
facts at `expr_type e`, in either direction, may gain exactly one new
hypothesis, `post_value_type cenv e = expr_type e`, and nothing else.
Instances: `copy_buffer_expr_post` (exprSimCopy), `expr_post_operand_kept_stable`,
`expr_post_operand_kept`, `expr_post_operand_kept_at` (exprSimOperands),
`unwrap_copy_sim` and `unwrap_value_sim` (exprSimUnwrap: their memory-size
premise is at `expr_type e`), the helpers in exprSimAggregateChildren /
exprSimAggregates that use them for an arbitrary child, and any helper of
the same shape. Where a consumer already has #992's
`lowered_value_type cenv e = expr_type e`, discharge with
`post_value_type_lowered` (exprSim). Add the hypothesis, repair the proof, and discharge
it at each consumer: from `post_value_type_no_calls`, `post_value_type_word`,
`post_value_type_bytestring` or `post_value_type_not_int_call`, or from a
hypothesis already in scope. If a consumer cannot discharge it (its operand
may be a widened aggregate internal call), record that consumer in LEARNINGS
and move on. List every helper you changed this way in LEARNINGS. A
counterexample to the unmodified statement of such a helper is not needed.

Already handled: the tuple-base subscript takes
`~nocalls ==> post_value_type cenv obj = expr_type obj`, and
`body_subscript_case` delegates the widened base to the cheated
`body_subscript_widened_call_base`. The statement sims in bodySimStmtCases /
bodySimDeclCases already split off widened internal calls into the cheated
`body_*_widened_*` theorems; their non-widened branches carry
`lowered_value_type cenv e = expr_type e` (or `int_calls_expr e = []`), which
gives `post_value_type cenv e = expr_type e` by `post_value_type_lowered` /
`post_value_type_no_calls`.

## Build

```
holbuild -j4 build abiDecodeStaticPropsTheory abiEncoderWindowArrayTheory abiEncoderWindowArrayBodyTheory abiEncoderWindowArrayEntryTheory abiEncoderWindowArrayExitTheory abiEncoderWindowArrayFinishTheory abiEncoderWindowArrayInvariantTheory abiEncoderWindowArrayLoopTheory abiEncoderWindowArrayRoundTheory abiEncoderWindowBytesTheory abiEncoderWindowChildTheory abiEncoderWindowComplexTheory abiEncoderWindowCursorTheory abiEncoderWindowMembersTheory abiEncoderWindowPhaseTheory abiEncoderWindowRunTheory abiEncoderWindowSequenceTheory abiEncoderWindowSourceTheory abiEncoderWindowSourceRunTheory abiEncoderWindowStructuralMembersTheory appendStorageRelTheory bodyAppendStorageAdapterTheory bodyAppendStorageFactsTheory bodyExprPreFactsTheory bodyMemoryDefsTheory bodySimTheory bodySimDeclCasesTheory bodySimEntryTheory bodySimExprCasesTheory bodySimLogTheory bodySimMainTheory bodySimStmtCasesTheory calldataAggregateTypedTheory calldataBulkLeafTheory calldataBulkLiveTheory calldataBytesLeafTheory calldataBytesLiveTheory calldataDynInitTheory calldataDynOwnedTheory calldataDynStepTheory calldataFiniteTypedTheory calldataMembersTheory calldataReconstructionTheory calldataWordLeafTheory calldataWordLiveTheory configuredE2ECorrectnessTheory convertScalarBridgeTheory convertScalarBytesTheory convertScalarBytesRunTheory convertScalarChecksTheory convertScalarDecimalTheory convertScalarDecimalFragTheory convertScalarDecimalRunTheory convertScalarDispatchTheory convertScalarEncodingTheory convertScalarFlagsTheory convertScalarOutputsTheory convertScalarPropsTheory convertScalarSimTheory convertScalarTypingTheory ctorAbiActualTheory ctorAbiActualArrayBodyTheory ctorAbiActualArrayClosureTheory ctorAbiActualArrayContextTheory ctorAbiActualArrayEntryTheory ctorAbiActualArrayFiniteTheory ctorAbiActualArrayHeaderTheory ctorAbiActualArrayRunTheory ctorAbiActualRecursiveTheory ctorArgDecodeTheory e2eCallChecksTheory e2eCompositionChecksTheory e2eCorrectnessTheory entryArgPtrsTheory entryChecksPropsTheory entryDecodePlanPropsTheory entryDecodePropsTheory entryDecodeStaticPropsTheory entryDecodeStructureTheory entryHaltMemTheory entrySinkExtractionTheory entryStateRelTheory exprOpenCasesTheory exprOpenCopiesTheory exprOpenDispatchTheory exprOpenFirstOperandTheory exprOpenMainTheory exprOperandVarTheory exprReasonOperandTheory exprSafeOperandTheory exprSafeOperandBuiltinsTheory exprSimTheory exprSimAccountsTheory exprSimAggregateChildrenTheory exprSimAggregateLayoutTheory exprSimAggregateLoopsTheory exprSimAggregateSourceTheory exprSimAggregatesTheory exprSimArithTheory exprSimArrayIndexTheory exprSimAttributeTheory exprSimAttributeFieldsTheory exprSimBinopFragTheory exprSimBufferTheory exprSimBufferEmptyExecTheory exprSimBufferStoreTheory exprSimBuiltinsTheory exprSimCalldataTheory exprSimCalldataSliceTheory exprSimCallsTheory exprSimCompareTheory exprSimConvertTheory exprSimConvertFromBytesTheory exprSimConvertScalarTheory exprSimCopyTheory exprSimECArithTheory exprSimHashTheory exprSimHypsTheory exprSimIfExpTheory exprSimLeavesTheory exprSimLenTheory exprSimLiteralBufferTheory exprSimMainTheory exprSimMemoryTransportTheory exprSimOperandsTheory exprSimOperatorsTheory exprSimOpsTheory exprSimPlacesTheory exprSimPopTheory exprSimPrecompilesTheory exprSimSendTheory exprSimStorageCopyTheory exprSimTupleTheory exprSimUint2StrTheory exprSimUnopTheory exprSimUnwrapTheory exprSimWordArgsTheory exprSimWordBuiltinsTheory exprWordOperandTheory freshWritesTheory intCallArgsTheory intCallResultTheory intCallReturnTheory intCallReturnMemTheory loweringMemCorrectTheory loweringRuntimeCorrectTheory memoryLocalRhsPropsTheory rawReturnCorrectTheory rawReturnValueTheory stmtPoppedKeysTheory stmtSimTheory stmtSimAppendStorageTheory stmtSimAppendStorageComposeTheory stmtSimAssignTheory stmtSimAssignAttrTheory stmtSimAssignAttrStorageTheory stmtSimAssignMemTheory stmtSimAssignStorageTheory stmtSimAssignStorageCopyTheory stmtSimAssignStoreTheory stmtSimAssignTupleTheory stmtSimAssignTupleMemTheory stmtSimAssignTupleTargetsTheory stmtSimAugAssignTheory stmtSimAugAssignAttrTheory stmtSimAugAssignAttrStorageTheory stmtSimAugAssignStorageTheory stmtSimDeclTheory stmtSimDeclEmptyTheory stmtSimDeclMemTheory stmtSimDeclStoreTheory stmtSimForTheory stmtSimForLoopTheory stmtSimForPartsTheory stmtSimForRangeTheory stmtSimIfTheory stmtSimLogTheory stmtSimReasonTheory stmtSimReasonCodeTheory stmtSimReasonExprTheory stmtSimReasonStorageTheory stmtSimReturnTheory storageCopyLiveTheory storageStoreFrameTheory targetPlaceSimTheory targetPlaceSimCasesTheory tupleAssignCodeTheory tupleAssignMemoryTheory tupleAssignPartsTheory tupleAssignPrefixTheory tupleLoadPropsTheory tupleLocalStorePropsTheory tupleLocalStoreRunTheory tupleMemoryFrameTheory tupleMemoryLayoutTheory tupleStagePropsTheory tupleTargetStorePropsTheory tupleTargetStoreRunTheory tupleTypedLoadTheory valueCopyTheory valueCopyBytesTheory valueCopySourceTheory
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
- Don't edit `lowering/defs/` or `semantics/`.
- Already repaired on an older base by an earlier run (reuse its fixes when
  the same proof breaks): see `git show 45f533868`. exprSimIfExp,
  exprSimConvert and entryChecksProps are #992's newer proofs and were not
  repaired yet. The usual repair is to read facts from vv_post/expr_post at
  `post_value_type cenv e` (e.g. `t = post_value_type cenv e`, then
  `copy_buffer_post_transport_physical`; see unwrap_runtime_code_copy_sim
  and unwrap_ctor_code_copy_base_sim in exprSimCopy).
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

Theorems cheated at the start (these stay cheated; don't prove or touch them):

```
bodySimDeclCasesScript.sml: body_annassign_other
bodySimDeclCasesScript.sml: body_annassign_widened_aggregate_call
bodySimDeclCasesScript.sml: body_for_array
bodySimExprCasesScript.sml: body_bop_in_literal_case
bodySimExprCasesScript.sml: body_create_case
bodySimExprCasesScript.sml: body_extcall_case
bodySimExprCasesScript.sml: body_ifexp_widened_call_arm
bodySimExprCasesScript.sml: body_intcall_case
bodySimExprCasesScript.sml: body_make_array_widened_call_elem
bodySimExprCasesScript.sml: body_pop_nested_case
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
exprSimBuiltinsScript.sml: compile_blockhash_case
exprSimBuiltinsScript.sml: compile_concat_case
exprSimBuiltinsScript.sml: compile_extract32_case
exprSimBuiltinsScript.sml: compile_len_ctor_code_case
exprSimBuiltinsScript.sml: compile_slice_case
exprSimCallsScript.sml: compile_create_sim
exprSimCallsScript.sml: compile_extcall_sim
exprSimCallsScript.sml: compile_raw_call_calldata_sim
exprSimCallsScript.sml: compile_raw_call_sim
exprSimCallsScript.sml: compile_raw_log_sim
exprSimCallsScript.sml: compile_raw_revert_sim
exprSimCallsScript.sml: compile_selfdestruct_sim
exprSimCopyScript.sml: unwrap_ctor_code_copy_sim
exprSimLeavesScript.sml: compile_msg_gas_sim
exprSimLeavesScript.sml: compile_prevhash_sim
exprSimOperatorsScript.sml: compile_bop_in_literal_sim
exprSimOperatorsScript.sml: compile_bop_rest_case
exprSimPlacesScript.sml: compile_pop_nested_sim
exprSimPlacesScript.sml: compile_pop_storage_sim
exprSimPlacesScript.sml: compile_subscript_array_case
exprSimPlacesScript.sml: compile_subscript_map_case
exprSimUnwrapScript.sml: unwrap_ctor_immutable_word_sim
loweringMemCorrectScript.sml: body_stmts_sim_mem
loweringMemCorrectScript.sml: external_entry_reaches_body_mem
loweringMemCorrectScript.sml: external_entry_value_revert_mem
loweringMemCorrectScript.sml: external_frame_ret_ok_mem
loweringMemCorrectScript.sml: lower_vyper_runtime_unit_dload_offset_ok
loweringMemCorrectScript.sml: lower_vyper_runtime_unit_ptr_taint
loweringRuntimeCorrectScript.sml: external_body_frame
loweringRuntimeCorrectScript.sml: external_body_revert_data_reverts
loweringRuntimeCorrectScript.sml: external_body_source_ok
loweringRuntimeCorrectScript.sml: external_entry_reaches_body
loweringRuntimeCorrectScript.sml: external_entry_value_revert
loweringRuntimeCorrectScript.sml: external_frame_ret_ok
loweringRuntimeCorrectScript.sml: stmts_env_ret_ty
stmtSimLogScript.sml: compile_log_stmt_frag
targetPlaceSimCasesScript.sml: target_subscript_case
vyperLoweringCorrectScript.sml: vyper_to_venom_correct
```

## Owner guidance: IfExp same-layout arms

`compile_ifexp_vv_sim` (and `compile_ifexp_forced_frag`) are true as stated;
don't build counterexamples to them. An arm with
`same_memory_layout cenv (lowered_value_type cenv a) (expr_type a)` is an
internal call whose physical type evaluates: `expr_body_pre` gives it
(see `post_type_evaluates` in exprSimLen, which you may move to exprSimHyps
and export), so invalid physical types such as `UintT 0` don't arise. The
route: prove a transport lemma from the arm's facts at
`post_value_type cenv a` to facts at `expr_type a`, at the level of
`expr_val_rel`/`expr_val_at` (and `val_in_memory`), under
`same_memory_layout`, `type_widens_to` (from `post_value_type_widens`) and
evaluability of both types. Punnable leaves of equal size have the same
encoding (equal words, or bytestrings of equal rounded size); arrays and
tuples go elementwise. Then give the IfExp helpers that need it a form
taking those facts at `expr_type a` instead of `expr_post`, or keep their
equality premise and add a sibling that takes the transported facts. New
helper lemmas are allowed; exported statements stay frozen except as the
approved exception says.

## Owner contract revision: IfExp same-layout disjunct (supersedes the frozen statements below)

The frozen hypotheses of `compile_ifexp_vv_sim` lack what the transport needs.
Restate these, and only these, as follows (owner-approved internal restatement):

- In `compile_ifexp_vv_sim` (exported) and `compile_ifexp_forced_frag` (local),
  the last disjunct of the arm condition
  `same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)` becomes
  ```
  same_memory_layout cenv (lowered_value_type cenv e) (expr_type e) /\
  arg_type_fits (lowered_value_type cenv e) (expr_type e) /\
  (?tvp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvp)
  ```
- `ifexp_body_pre_lowered_type_compatible` concludes the same strengthened
  disjunct. Its proof gets `arg_type_fits` from `post_value_type_widens` /
  `type_widens_to_def` (the case `lowered = expr_type` is the first disjunct)
  and evaluability from `post_type_evaluates` (now exported in exprSimHyps).
- Then prove the transport lemma (see "Owner guidance" above) from facts at
  the physical type to facts at `expr_type a` under
  `same_memory_layout` + `arg_type_fits` + both types evaluating, and use it in
  `compile_ifexp_forced_frag`'s same-layout arms. Consumers of the restated
  theorems (exprSimOperators' IfExp case, bodySimExprCases) use the
  strengthened `ifexp_body_pre_lowered_type_compatible`.
- List these restatements in LEARNINGS. Everything else stays frozen.
