(*
 * Results rollup: the semantics, analysis, pass, lowering and compiler
 * proofs. Tests and concrete checks have rollups of their own; the build roots
 * in holproject.toml list them all.
 *
 * STATUS: This is not a claim that end-to-end compiler correctness is closed.
 * Some imported correctness theories still contain cheats/open obligations.
 * See docs/compiler-proof-status.md and docs/compiler-proof-roadmap.md.
 *)
Theory vyperHol
Ancestors
  (* semantics properties *)
  vyperSemanticsHol
  (* frontend and test runner *)
  vyperTestRunner
  (* compiler passes *)
  venomPassesHol
  (* analysis roll-up *)
  venomAnalysisHol
  (* lowering, pipeline, codegen and e2e *)
  vyperLoweringHol
  (* gas: origins of each charge, the shadow lowering, gas bridges *)
  msgGasOriginPost generatedGasOrigin gasShadowRawDeploy gasShadowRawRuntime
  bodyGasAdmissible exprSimConvertGas exprSimAbiDecodeGas exprSimAbiGasBridge
  gasIntCallArgs gasIntCallBody typeBuiltinGasPrefix
  (* calldata and ABI: decoding, encoding windows, buffer execution *)
  abiProofs abiEncoderWindowSourceRun abiBytesFrameExecution
  abiWordTupleExecution bufferAllocationExecution
  ctorAbiActualBytesRun placeTypingE2EProps
  (* statements: bodies' memory, returns, nonreentrancy, conversions, copies,
     CREATE dispatch *)
  bodyDeclMemory bodyStmtClosureMemory bodyFieldMemory bodyFieldValueMemory
  bodyFieldForceMemory bodyEnvMemory nonreentrantEntry
  stmtSimReturnTuple stmtSimReturnWiden stmtSimReturnWord selectedBodyCode
  builtinTypeConvert2 slotCopyExecution createDispatchExecution
  createRequestCorrespondence
  (* pointer safety of the lowering *)
  batchCopyRobustPtr entryHaltPtr liveArrayTransportPtr normalizationAllocPtr
  ptrSafetyTransport returnMetadataPtr staticTypeFitsPtr structChildPtr
  typedCopyArrayExecutionPtr wordCopyRobustPtr loweringPolicyOk
  (* deployment: the constructor frame and deploy correctness *)
  e2eDeployCorrectness
  ctorDeployLoweringFrameCallFree ctorDeployLoweringFrameCandidate
  ctorDeployLoweringFrameCfgNorm ctorDeployLoweringFrameContracts
  ctorDeployLoweringFrameJump ctorDeployLoweringFrameLowerDload
  ctorDeployLoweringFrameO1Pruning ctorDeployLoweringFramePipeline
  ctorDeployLoweringFrameSourceEntry ctorDeployLoweringFrameWidth
  ctorDeployLoweringFrameWitness
  (* Venom execution: oracle-aware core simulations, jump independence *)
  coreOracleSim coreOracleUpdates jumpIndep
  (* passes: oracle projections, FMP lowering, memory merging, SSA *)
  concretizeOracleSim ssaOracleSim passOracleSim remainingOracleSim
  remainingOracleTransport remainingOracleUpdates fmpLowerSequenceExec
  mmBlockSimProofs mmSupplySsaProofs mmSupplyWfProofs
  makeSsaCurrentNonDegCertificate
  (* codegen: stack planning *)
  stackPlanGenCompute
