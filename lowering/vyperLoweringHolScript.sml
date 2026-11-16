(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
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
  exprSimMain bodySimMain bodySimFullMain bodyFullStructLit externalReturnValuedFull ctorReturnFrame stmtSimZero stmtSimPass stmtSimProps stmtSimSeq stmtSimExpr
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
  asmSymOwnCode
  asmOptOwnMergeIszero
  finalizerContractOwn
  asmSpliceOwn
  asmOptOwnInefficientJumps
  asmOptOwnPruneUnused
  asmOptOwnPruneJumps
  (* reached here instead of as holproject.toml roots *)
  targetPtrFacts bodyFullTarget
  extcallReturnCompletedCut extcallReturnCountedReject extcallReturnDecodeSummary
  extcallReturnDecoderOwnership extcallReturnDefaultTypes extcallReturnFrameBridge
  abiEncoderWindowJointPhases externalReturnLiveWindowResources logTopicsRunPtr
  (* providers awaiting their consumers *)
  sourceUnitExitSafe intCallMaterializeFull bodyPtrIfExpAllocationSite
