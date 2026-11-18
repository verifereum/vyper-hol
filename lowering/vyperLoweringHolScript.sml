(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* arbitrary-calldata entry and S1 suppliers *)
  calldataArrayLiveMemory calldataArrayModularSetup calldataArrayRawCallsite
  calldataBulkOperationalCertificate calldataBulkSourceOutcome calldataCoherentOwnedEndpoint
  calldataExactBytesJoint calldataExactMemberValues calldataMembersRawCallsite
  calldataExactScalarAccepted calldataExactScalarRejected calldataNoneFallbackJoint
  calldataNoneMetadata calldataRegistrationRawAddress
  calldataRegistrationTerminalBindings calldataValidHeaderLocalFrontier dispatchedArgsBind
  dispatchedSelectedFacts dispatchedSelectedPrefix dispatchedSelectedRelations
  dispatchedValueEntry dispatchedValueFallback dispatchedValuePrefix
  dispatchedValueSelection dispatchedValueSource fallbackEntryEndpoint
  loweringCalldataCorrect registrationGuardRejectOrigin
  dispatchedEntryValueRevert
  e2eLifecycle
  e2eCodeFrame
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  bodyMemStorageCopyStage
  createCtorTupleExecution dallocaBlueprintArgs
  dallocaCreateCopy dallocaCreateGeometry
  loweringRuntimeAllocationHistory loweringRuntimeRawVariantHistory
  loweringCallBudgetBounds
  moduleLoweringProps entryDispatchProps entryDecodeProps
  abiDecodeStaticProps entryDecodeStaticProps entryDecodePlanProps
  entryChecksProps
  entryStateRel entryLocals ctorEntryLocals ctorSourceInputs
  loweringSlice
  memSafeRun instMemFrontier fragExecMem allocaFootprint
  bodyPtrMakeArrayMemoryFrame
  fragGasOrigin fragGasOriginPtrSafeUpto
  varsExt exprSimNameWord exprSimLiteralWord exprSimEnv
  exprBopLowering
  exprSimOps exprSimOperands exprSimCompare exprSimArith intBits freshWrites
  exprSimBuiltins exprSimExtCallCase bodyIntCallSeams bodySimFullMain bodyFullStructLit externalReturnValuedFull ctorReturnFrame stmtSimZero stmtSimPass stmtSimProps stmtSimSeq stmtSimExpr
  stmtSimBreak stmtSimContinue stmtSimIf stmtSimFor stmtSimReturn stmtSimDecl
  stmtSimReason stmtSimReasonExpr stmtSimReasonStorage stmtSimForRange
  stmtSimDeclMem stmtSimDeclEmpty exprSimStorageCopy stmtSimAssignStore stmtSimAugAssign
  stmtSimAssign stmtSimAssignMem stmtSimAssignTuple stmtSimAssignTupleMem
  stmtSimAssignStorage stmtSimStoreCopy storageCopyLive stmtSimAssignStorageCopy
  stmtSimAssignAttr
  stmtSimAssignAttrStorage stmtSimAugAssignAttr
  valueEncodingProofs
  localPtrsProps
  externalEntryProps constructorGuardProps
  nonreentrantEntryEquiv internalReturnLockProps
  transientLockFrameProps
  selectorCompilerProps checkedSelectorTableProps
  immutableStagingBridge
  immutableCodeLayout
  e2eDeployFrame ctorDeployLoweringEntry
  deployFrameReplay asmDataSuffixProps deployEntryLayout deployUnitProducers
  immutableLocationProps
  loweringShapeDefs
  loweringShapeProps
  ctorShapeProps ctorUnitShape
  intCallStep extCallOracleStep intCallLookup intCallCallee intCallArgs intCallResult intCallReturnMem intCallFrame intCallReturn valueCopy
  structFieldsProps
  (* compiler + correctness *)
  vyperCompiler
  allocaFrontierWitness
  vyperLoweringCorrect
  rawReturnHalt rawReturnValue rawReturnHeader rawReturnMem rawReturnCorrect
  loweringMemCorrect
  asmSymBridge
  asmDataEnv
  asmOptOwnPeephole
  asmOptFinalizerCorrect
  asmOptOwnMergeJumpdests
  asmSymOwnCode
  asmOptOwnMergeIszero
  finalizerContractOwn
  asmOptOwnPruneUnreachable
  asmSpliceOwn
  asmOptOwnInefficientJumps
  asmOptOwnPruneUnused
  asmOptFinalizerOwn
  asmOptOwnPruneJumps
  asmSymSemWithin
  asmSpliceWithin
  (* reached here instead of as holproject.toml roots *)
  targetPtrFacts bodyFullTarget
  extcallReturnCompletedCut extcallReturnCountedReject extcallReturnDecodeSummary
  extcallReturnDecoderOwnership extcallReturnDefaultTypes extcallReturnFrameBridge
  abiEncoderWindowJointPhases externalReturnLiveWindowResources logTopicsRunPtr
  (* providers awaiting their consumers *)
  internalReturnMemoryMem bodyFullIntCallByteFrame
  sourceUnitExitSafe intCallMaterializeFull bodyPtrIfExpAllocationSite
  o1LabelFlowOwnSecondSsa
  assignBasePtrStoragePath assignTuplePtrBytesCopy
  bodyPtrBytestringBuiltinsConcatArmSemantics
  bodyPtrBytestringBuiltinsConcatOperand
  bodyPtrPrecompileBuiltinsArithmeticSource
  bodyPtrPrecompileBuiltinsArithmeticValue bodyPtrSignedConvertSourceFixed
  forPtrAllocationFrame internalReturnImmutableTypes logBytesCodePtr
  logBytesRobustSeqPtr logBytesSeqPtr revertReasonPrefixPtr
  reasonCompilerProps reasonLiteralBufferPtr reasonSourceProps
  reasonTypingProps revertReasonPrefixCodePtr revertReasonSuffixPathPtr
