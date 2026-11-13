(* Concrete checks of the lowering and the compiler, as one build root:
   interface contracts on concrete inputs, compiled creation code, and
   regressions of the compiler's allocation and evaluation order. Bytecode
   parity with the pinned Python compiler is the native runner's job
   (bytecode/native/). *)
Theory loweringChecks
Ancestors
  (* allocation limits, conversions, concat buffers, shared callee memory *)
  compilerLoweringTest
  (* fixed-program regressions: ranges, allocation budget, immutables,
     assignment order, the O1 source-stage unit shape, the pop() subscript
     rejection, a name declared at two types in sibling scopes *)
  evalCompilerRange evalCompilerAllocationBudget evalCompilerInternalImmutables
  evalAssignmentOrder evalCompilerSourceShape evalCompilerPopSubscriptOverlap
  evalCompilerSiblingScopeTypes
  (* branch_opt's output checker on a sample of the parity fixtures'
     compiled functions *)
  branchOptCheckCorpus
  evalCompilerGettersConstantsParity evalCompilerGettersConstantsRegression
  (* contracts of the lowering's interfaces on concrete inputs *)
  targetPlaceTest
  abiEncodeSnapshotTest
  (* compiled creation code *)
  vyperCtorAliasTest createImmutableBytecodeTest createCompletionProbe
  (* tests of the bytecode evaluation library the native runner shares *)
  evalCompilerBytecodeLibTest
  (* the supported subset: per-construct contracts, membership matrix *)
  supportedExprFormProps supportedExprProps supportedProgramProps
  vyperMembershipMatrixTest
  (* more interface contracts on concrete inputs; raw RETURN's copy *)
  e2eBoundaryTest groupedDispatchProps rawReturnCopy
  (* compiled creation code and events, the event endpoints' admission audit *)
  vyperCreateMemoryTest vyperEventForwardStruct vyperEventArgumentLifetime
  eventEndpointAudit
  (* ABI encode/decode edge cases and size boundaries *)
  abiDecodeBoundsTest abiDecodeAliasTest abiDecoderBytesEdges
  createSizeBoundaryTest
  (* a closed deploy-then-call run meeting every premise of both top theorems *)
  e2eWitness
