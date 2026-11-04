# TASK target ledger (2026-11-04, current D0002 repair pass)

Partial accounting only. S = whole-target checked; B = known failing prerequisite
or consumer; P = still outstanding in this pass. All names below omit Theory.
No failure or unsupported route here is a checked counterexample. Baseline cheats
remain baseline; successful targets are not claimed globally oracle-free.

## Checked targets (S)

The 29 independent targets checked in the previous inventory (E0020;
TO_seq1012_cone-20261104T041205Z_m0366_t001 through m0368_t001):

exprSim freshWrites exprSimOps exprSafeOperand exprSafeOperandBuiltins
exprOperandVar exprWordOperand exprSimStorageCopy exprSimCompare exprSimArith
exprSimArrayIndex exprSimUnop exprSimMemoryTransport valueCopyBytes exprSimCopy
exprSimOperands stmtSim stmtSimDeclStore stmtSimIf stmtSimForParts stmtSimLog
tupleMemoryLayout stmtSimDecl stmtSimAssignStore stmtSimAssign stmtSimForLoop
stmtSimFor stmtSimForRange stmtSimReason

D0002 repaired cone, current whole-target checks:

- TO_seq1012_cone-20261104T060655Z_m0593_t001:
  exprSimAccounts exprSimCalldata valueCopy exprSimAggregates exprSimUnwrap
  exprSimHyps
- TO_seq1012_cone-20261104T060655Z_m0632_t001 (batch passes after scalar/bytes
  equality repairs in Precompiles, CalldataSlice, and Send):
  abiDecodeStaticProps entryArgPtrs entryChecksProps entryDecodePlanProps
  entryDecodeProps entryDecodeStaticProps entryDecodeStructure entryHaltMem
  entrySinkExtraction entryStateRel exprSimAggregateLayout exprSimAggregateLoops
  exprSimAggregateSource exprSimBinopFrag exprSimBuffer exprSimBufferEmptyExec
  exprSimBufferStore exprSimCalldataSlice exprSimCalls exprSimConvert exprSimHash
  exprSimLiteralBuffer exprSimPrecompiles exprSimSend exprSimWordArgs
  exprSimWordBuiltins
- TO_seq1012_cone-20261104T060655Z_m0633_t001:
  ctorAbiActual ctorAbiActualArrayBody ctorAbiActualArrayClosure
  ctorAbiActualArrayContext ctorAbiActualArrayEntry ctorAbiActualArrayFinite
  ctorAbiActualArrayHeader ctorAbiActualArrayRun ctorAbiActualRecursive
  intCallArgs intCallResult valueCopySource tupleMemoryFrame
- Explicit finished targets in failed batches m0634/m0635 (same prefix):
  exprOpenFirstOperand exprSimLeaves bodySim stmtPoppedKeys exprOpenCopies
- TO_seq1012_cone-20261104T060655Z_m0645_t001:
  exprOpenCases exprOpenDispatch exprOpenMain targetPlaceSim
  exprSimAggregateChildren exprSimIfExp exprSimOperators exprSimPop
  (exprSimAttributeFields also explicitly finished).
- TO_seq1012_cone-20261104T060655Z_m0651_t001:
  bodyMemoryDefs bodySimEntry stmtSimAugAssign storageCopyLive targetPlaceSimCases

## Subsequent checked repairs and current validation

The prior Len/EC/Reason/Return blocked routes are resolved, not permitted skips:
- EC: exprSimHyps and exprSimECArith whole-target checks m0677/m0691;
  rigid fixed uint256[2] widening proves post type equality.
- Reason: exprReasonOperand, stmtSimReasonExpr/Storage/Code pass m0734 and
  m0870. The physical continuation interface avoids equality for Storage/Code.
- Return: stmtSimReturn, tupleLoadProps, intCallReturn, intCallReturnMem pass
  m0758 and m0870. Approved compile_return_tuple_int_frag premise supplies equality.
- Len: exprSimLen passes m0854, committed d2c08f6a4. Physical evaluation and
  two-type header boundaries keep runtime typing at the annotation. No exported
  Len statement changed; no equality premise on the frozen Len consumer.

All mNNNN evidence above and below has prefix
TO_seq1012_cone-20261104T060655Z_ unless another prefix is explicitly stated.

Exact full TASK build attempted in m0866 with proof steps/default tactic limits.
It failed in exprSimAttribute.attr_vv_post at drule_all base_vv_holds_struct
(line 388): context has vv_holds at post_value_type cenv obj, whereas helper
expects StructT sid = expr_type obj. No invariant/well_typed hypothesis is
available inside attr_vv_post; consumer propagation or a rigid StructT type
boundary needs a new scoped plan. This is a proof failure, not a counterexample.

Explicit finished targets from m0866:
stmtSimLog stmtSimAssign stmtSimForParts bodySim stmtSimForLoop exprSimBuffer
exprSimAttributeFields bodyMemoryDefs stmtSimFor stmtSimForRange storageCopyLive
targetPlaceSim bodySimEntry exprOpenFirstOperand stmtPoppedKeys targetPlaceSimCases
exprSimBufferStore entryDecodeStructure entryDecodePlanProps entrySinkExtraction
exprSimBufferEmptyExec intCallArgs valueCopySource exprSimAggregateChildren
exprSimAggregateLayout exprSimAccounts exprSimCalldata exprSimAggregateSource
exprSimPop exprOpenCopies.

Independent follow-up m0869 finished:
ctorAbiActualArrayBody exprOpenCases exprSimBuiltins exprSimAggregateLoops
ctorAbiActualArrayHeader exprOpenDispatch exprSimAggregates ctorAbiActualArrayFinite
exprOpenMain ctorAbiActualArrayEntry ctorAbiActualArrayContext.
It then hit a 2.5s tactic timeout in ctorAbiActualArrayRun,
ctor_actual_dynamic_array_loop_run line 169:
fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]
after 27 operand constructor cases with a large untouched Child assumption.
No source edits made; requires scoped tactic repair before certification.

A filtered broad validation m0872 finished tupleMemoryFrame, then hit a 2.5s
simp[mk_inst_def] timeout in entryChecksProps.step_cds_check_ops line 102 after
PURE_ONCE_REWRITE_TAC[step_inst_base_def]. The large opcode case expression
needs a targeted selector rewrite, not a timeout override. Previous successful
checks of entryChecksProps are historical, not current default-timeout certification.

## Current residual target/failure partition (E0042-E0044 repairs)

Resolved and committed:
- Attribute: rigid StructT boundary and approved local attr_vv_post equality;
  exprSimAttribute passes m0902 (1439cc0f3).
- Constructor liveness: single-operand boundary; Run, Closure, Recursive pass
  m0916 (9b1a4f409), ctorAbiActual also finished in m0939.
- Entry opcode projection simplification: entryChecksProps passes m0933
  (49154ced8).

Exact requested batch m0939 now reaches exprSimTuple.tuple_base_read line844.
The local helper has vv_holds at post_value_type cenv obj but attempts to use
base_vv_holds_loc at TupleT tys = expr_type obj, with no equality premise.
The metis tactic times out; this is not checked falsehood evidence. This local
arbitrary-child helper needs scoped repair/consumer classification. The TASK's
known tuple-base limitation is still retained, not silently strengthened.

Dependency-blocked targets:
- exprSimTuple: tuple_base_read physical/annotation mismatch (m0939).
- exprSimPlaces -> exprSimTuple; known compile_subscript_tuple_sim limitation.
- exprSimMain -> exprSimPlaces.
- bodySimExprCases -> exprSimMain / exprSimPlaces.

All remaining 105 TASK targets pass the filtered whole-target batch m0942
(default limits, proof steps enabled, no forcing). Exact full build remains
blocked by the four-target tuple closure. C2 final contract audit still pending.
Probe cleanup scan m0943 finds no seq1012_ in lowering/*Script.sml.

## Approved helper and unsupported-consumer ledger

Structured LEARNINGS contains the complete changed-helper ledger:
L0003 (Copy/Operands), L0008 (Unwrap and expr_sim_of_vv_sim), L0009 (Hyps/IfExp),
L0011 (Buffer/Hash/AggregateChildren), L0013 Send helpers and L0014 EC local
helpers, L0015 Reason, L0016 Return. Each changed exported helper gains exactly
the permitted post_value_type = expr_type premise. Len adds only local two-type
boundaries and changes local fragment premises; no exported statement changes.
L0012's old Len skip and L0013's old EC skip are superseded by checked repairs.
L0007's old Unwrap stop is superseded by D0002. The known tuple-base limitation
is retained as TASK documentation, not verified falsehood. No new counterexample
probes, cheats, axioms, or source edits were introduced by this inventory pass.
