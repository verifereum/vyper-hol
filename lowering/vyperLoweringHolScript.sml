(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* arbitrary-calldata entry and S1 suppliers *)
  calldataBulkOperationalCertificate calldataBulkSourceOutcome
  calldataExactBytesJoint
  calldataExactScalarAccepted calldataExactScalarRejected calldataNoneFallbackJoint
  calldataNoneMetadata calldataRegistrationRawAddress
  calldataRegistrationTerminalBindings dispatchedArgsBind
  dispatchedSelectedFacts dispatchedSelectedPrefix
  dispatchedValueEntry dispatchedValueFallback dispatchedValuePrefix
  dispatchedValueSelection dispatchedValueSource fallbackEntryEndpoint
  loweringCalldataCorrect registrationGuardRejectOrigin
  dispatchedEntryValueRevert
  e2eLifecycle e2eTransactionWorld
  e2eModsLifecycle
  e2eCodeFrame ownSymSrcUnit
  runtimeSymSrcDynarrayAppend runtimeSymSrcModuleArgPreservation runtimeSymSrcRuntimeBoundary runtimeSymSrcStatements
  (* definitions *)
  moduleLowering compileUnit
  (* property statements and proofs *)
  dallocaBlueprintArgs
  dallocaCreateCopy dallocaCreateGeometry
  createExprSizeExit
  rawCallCalldataPeakMemory
  runtimePeakMemoryBound
  loweringRuntimeAllocationHistory loweringRuntimeRawVariantHistory
  loweringCallBudgetBounds
  moduleLoweringProps entryDispatchProps entryDecodeProps
  abiDecodeStaticProps entryDecodeStaticProps entryDecodePlanProps
  entryChecksProps
  entryStateRel entryLocals ctorSourceInputs
  loweringSlice
  memSafeRun instMemFrontier fragExecMem allocaFootprint
  bodyPtrMakeArrayMemoryFrame
  fragGasOrigin fragGasOriginPtrSafeUpto
  varsExt exprSimNameWord exprSimLiteralWord exprSimEnv
  exprBopLowering
  exprSimOps exprSimOperands exprSimCompare exprSimArith intBits freshWrites
  exprSimBuiltins exprSimExtCallCase bodyIntCallSeams bodySimFullMain bodyFullStructLit externalReturnValuedFull ctorReturnFrame stmtSimZero stmtSimPass stmtSimProps stmtSimExpr
  stmtSimBreak stmtSimContinue stmtSimFor stmtSimReturn stmtSimDecl
  stmtSimReason stmtSimReasonExpr stmtSimReasonStorage stmtSimForRange
  stmtSimDeclMem stmtSimDeclEmpty exprSimStorageCopy stmtSimAssignStore stmtSimAugAssign
  stmtSimAssign stmtSimAssignMem stmtSimAssignTuple
  storageCopyBodyRaisePtr
  stmtSimAssignStorage stmtSimStoreCopy storageCopyLive stmtSimAssignStorageCopy
  stmtSimAssignAttr
  stmtSimAssignAttrStorage
  valueEncodingProofs
  localPtrsProps
  nonreentrantEntryEquiv
  transientLockFrameProps
  selectorCompilerProps checkedSelectorTableProps
  immutableRepSensitivity
  immutableCodeLayout
  e2eDeployFrame ctorDeployLoweringEntry
  deployFrameReplay asmDataSuffixProps deployEntryLayout deployUnitProducers
  immutableLocationProps
  loweringShapeDefs
  loweringShapeProps
  runtimeUnitShapeMods ctorDeployShapeMods
  ctorShapeProps ctorUnitShape
  intCallStep extCallOracleStep intCallLookup intCallCallee intCallResult intCallReturnMem intCallFrame intCallReturn valueCopy
  bodyFullShadowBodyInvLowering
  bodyFullPredsMods
  structFieldsProps
  (* compiler + correctness *)
  vyperCompiler
  vyperLoweringCorrect
  rawReturnHalt rawReturnValue rawReturnHeader rawReturnMem
  loweringMemCorrect
  linkedUnitMemory
  asmSymBridge
  asmSymBridgeOwn
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
  extcallReturnDecoderOwnership extcallReturnDefaultTypes extcallReturnFrameBridge
  abiEncoderWindowJointPhases logTopicsRunPtr
  (* closed-world request-cut guard and producer *)
  e2eOutcomesProducer requestCutSelectedReplay
  (* providers awaiting their consumers *)
  bodyPtrTypeBuiltinsBytesUintSemantics
  internalReturnMemoryMem bodyFullIntCallByteFrame
  bodyFullIntCall bodyFullIntCallCallee[qualified,ignore_grammar]
  bodyFullIntCallArgs[qualified,ignore_grammar] compileExprAllocaFresh
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
  reasonTypingProps revertReasonSuffixPathPtr
  (* and/or chains (BoolChain) *)
  exprSimBoolChain bodyFullBoolChain
