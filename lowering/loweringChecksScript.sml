(* Concrete checks of the lowering and the compiler, as one build root:
   interface contracts on concrete inputs, compiled creation code, and
   regressions of the compiler's allocation and evaluation order. Raw-system
   and creation manifests have kernel-checked Python bytecode parity here;
   other parity suites use the native runner (bytecode/native/). *)
Theory loweringChecks
Ancestors
  constSubstCV
  constSubstModsCorrect[qualified]
  (* allocation limits, conversions, concat buffers, shared callee memory *)
  compilerLoweringTest
  (* dynamic peak-memory statement type and constant bindings *)
  peakMemoryHeaders deployPeakMemoryHeaders
  (* fixed-program regressions: ranges, allocation budget, immutables,
     assignment order, the O1 source-stage unit shape, the pop() subscript
     rejection, a name declared at two types in sibling scopes *)
  evalCompilerRange evalCompilerAllocationBudget evalCompilerInternalImmutables
  evalAssignmentOrderChecks evalCompilerSourceShape evalCompilerPopSubscriptOverlap
  evalCompilerSiblingScopeTypes
  (* Linked runtime dispatch and entry proofs. *)
  defaultDispatchMods dispatchedCallAssemblyMods
  entryCreateNativeCut entryCreateReject loweringCreateSize
  (* exact Python parity for every retained raw-system and creation fixture *)
  evalCompilerRawSystem evalCompilerCreateBuiltins
  (* branch_opt's output checker on a sample of the parity fixtures'
     compiled functions *)
  branchOptCheckCorpus
  evalCompilerGettersConstantsParity evalCompilerGettersConstantsRegression
  (* contracts of the lowering's interfaces on concrete inputs *)
  targetPlaceTest
  abiEncodeSnapshotTest
  (* compiled creation code *)
  vyperCtorAliasTest createImmutableBytecodeTest createCompletionProbe
  ctorImmutableAppendTest
  e2eWitnessCompute e2eWitness e2eNonreentrantWitness e2eCompose e2eERC20Witness
  e2eModsWitness linkedBodyWitness linkedBodyWitnessContext linkedBodyDeadImportWitness
  linkedStructFields
  (* tests of the bytecode evaluation library the native runner shares *)
  evalCompilerBytecodeLibTest
  (* operand-stack checker: pinned internal-call bytecode and deep call chains *)
  stackBoundWitnesses
  (* the supported subset: per-construct contracts, membership matrix *)
  supportedExprFormProps supportedExprProps supportedProgramProps
  vyperMembershipParityTest vyperMembershipMatrixTest
  (* more interface contracts on concrete inputs; raw RETURN's copy *)
  e2eBoundaryTest groupedDispatchProps rawReturnCopy
  (* compiled creation code and events *)
  vyperCreateMemoryTest vyperEventForwardStruct vyperEventArgumentLifetime
  abiEmptyLogPath bodyFullLog
  (* ABI encode/decode edge cases and size boundaries *)
  abiDecodeBoundsTest abiDecodeAliasTest abiDecoderBytesEdges
  createSizeBoundaryTest
  (* Standalone ABI execution checks. *)
  abiScratchBuiltinOpenSource exprSimAbiEncodeRegion
  (* S1 request-prefix companion cases. *)
  s1PrefixLiteralWord s1PrefixWordWei s1PrefixRawCall
  s1PrefixNames s1PrefixBuiltinLeaves s1PrefixPrecompile s1PrefixStmtZero
  (* Composite request-prefix simulation and its standalone cases. *)
  bodyFullRangeProjection[qualified]
  s1PrefixAssignLocalSource[qualified]
  s1PrefixAssignToplevelSource[qualified]
  s1PrefixBlueprintScalars[qualified]
  s1PrefixBodySimFullMain[qualified] s1RequestPrefix[qualified]
  s1PrefixBoolChainChangedContext[qualified]
  s1PrefixBoolChainCompareStep[qualified]
  s1PrefixBoolChainDefaultChildConcat[qualified]
  s1PrefixBoolChainDefaultStagedReplay[qualified]
  s1PrefixBoolChainIndexedCut[qualified]
  s1PrefixBoolChainListSequence[qualified]
  s1PrefixBoolChainLiteralExtCall[qualified]
  s1PrefixBoolChainLoopRounds[qualified]
  s1PrefixBoolChainMinimalTip[qualified]
  s1PrefixBoolChainOriginalSingleton[qualified]
  s1PrefixBoolChainProperHeadJointDomain[qualified]
  s1PrefixBoolChainProperHeadSourceAlignment[qualified]
  s1PrefixBoolChainSelectedFieldScalarAssign[qualified]
  s1PrefixBoolChainSelectedIntCallHead[qualified]
  s1PrefixBoolChainSelectedRange[qualified]
  s1PrefixBoolChainSelectedRight[qualified]
  s1PrefixBoolChainTwoTestLayout[qualified]
  s1PrefixBopWordOperands[qualified]
  s1PrefixBuiltinSliceOperands[qualified]
  s1PrefixConvertScalarSuffix[qualified]
  s1PrefixCtorDeployBodySimulation[qualified]
  s1PrefixRawCallCalldataWords[qualified]
  s1PrefixStructLitBind[qualified]
  s1PrefixSubscriptCopiedBind[qualified]
  s1PrefixSubscriptNoCopyBind[qualified]
  s1PrefixTargetArraySuffix[qualified]
  s1PrefixTargetMappingOutcome[qualified]
  s1PrefixUnaryValueCompose[qualified]
