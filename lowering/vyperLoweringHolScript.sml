(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps entryDispatchProps entryDecodeProps
  abiDecodeStaticProps entryDecodeStaticProps entryDecodePlanProps
  entryChecksProps
  entryStateRel entryLocals ctorEntryLocals ctorSourceInputs
  loweringSlice
  memSafeRun instMemFrontier fragExecMem allocaFootprint
  fragGasOrigin fragGasOriginPtrSafeUpto
  varsExt exprSimNameWord exprSimLiteralWord exprSimEnv
  exprBopLowering
  exprSimOps exprSimOperands exprSimCompare exprSimArith intBits freshWrites
  exprSimMain bodySimMain bodySimFullMain ctorReturnFrame stmtSimZero stmtSimPass stmtSimProps stmtSimSeq stmtSimExpr
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
  e2eDeployFrame ctorDeployLoweringEntry ctorDeployLoweringArms
  deployFrameReplay asmDataSuffixProps deployEntryLayout deployUnitProducers
  immutableLocationProps
  loweringShapeDefs
  loweringShapeProps
  ctorShapeProps ctorUnitShape
  intCallStep extCallOracleStep intCallLookup intCallCallee intCallArgs intCallResult intCallReturnMem intCallFrame intCallReturn valueCopy
  structFieldsProps
  (* compiler + correctness *)
  vyperCompiler
  allocaBudgetChecks
  vyperLoweringCorrect
  rawReturnHalt rawReturnValue rawReturnHeader rawReturnMem rawReturnCorrect
  loweringMemCorrect
  (* S3 pointer leaves kept in the build until their owner rules on them *)
  bodyStmtsSimPtr extEntryReachesBodyPtr extEntryValueRevertPtr
  extFrameRetOkPtr
  (* S3 memory-run leaves loweringMemCorrect no longer imports, kept in the
     build like the pointer leaves above *)
  loweringMemEntryRevert loweringMemBodyRun
  asmSymBridge
  asmDataEnv
  asmOptFinalizerCorrect
