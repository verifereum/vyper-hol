(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps entryDispatchProps entryDecodeProps
  abiDecodeStaticProps entryDecodeStaticProps entryDecodePlanProps
  entryChecksProps
  entryStateRel entryLocals
  loweringSlice
  memSafeRun instMemFrontier fragExecMem allocaFootprint
  varsExt exprSim
  exprBopLowering
  exprSimOps exprSimOperands exprSimCompare exprSimArith intBits freshWrites
  exprSimMain bodySimMain stmtSim stmtSimIf stmtSimFor stmtSimReturn stmtSimDecl
  stmtSimReason stmtSimReasonExpr stmtSimReasonStorage stmtSimForRange
  stmtSimDeclMem stmtSimDeclEmpty exprSimStorageCopy stmtSimAssignStore stmtSimAugAssign
  stmtSimAssign stmtSimAssignMem stmtSimAssignTuple stmtSimAssignTupleMem
  stmtSimAssignStorage stmtSimStoreCopy stmtSimAssignAttr
  stmtSimAssignAttrStorage stmtSimAugAssignAttr
  valueEncodingProofs
  localPtrsProps
  externalEntryProps constructorGuardProps
  nonreentrantEntryEquiv internalReturnLockProps
  transientLockFrameProps
  selectorCompilerProps checkedSelectorTableProps
  immutableStagingBridge
  immutableCodeLayout
  immutableLocationProps
  loweringShapeDefs loweringShapeProps
  intCallStep extCallOracleStep intCallLookup intCallCallee intCallArgs intCallResult intCallReturnMem intCallFrame intCallReturn valueCopy
  structFieldsProps
  (* compiler + correctness *)
  vyperCompiler
  allocaBudgetChecks
  vyperLoweringCorrect
  configuredE2ECorrectness
  finalizerContract asmSymBridge asmOptPruneJumps asmOptMergeIszero
  asmOptPeephole
  asmOptPruneUnused asmOptMergeJumpdests
  asmOptInefficientJumps
  evalCompilerInternalImmutables
  evalAssignmentOrder
  (* focused internal-frame allocation, cleanup and whitelist regressions *)
  calleeMemoryWitness
  cleanupPromiseWitness
  internalFrameWhitelistDiagnostic
