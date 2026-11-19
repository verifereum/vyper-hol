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
  codegenStaticAbort staticAbortAsmOptHol
  runtimeLabelReadiness
  o1LabelReadiness
  runtimeLabelEntry
  o1LabelStages
  (* semantics properties *)
  vyperSemanticsHol
  (* frontend, its cv translation, and the test runner *)
  vyperTestRunner jsonToVyperCV
  (* compiler passes *)
  venomPassesHol
  (* analysis roll-up *)
  venomAnalysisHol
  (* lowering, pipeline, codegen and e2e *)
  vyperLoweringHol
  constSubstStmts constSubstStmtsPreserve
  (* Venom execution: alloca size caching, jump independence *)
  allocaCacheProps jumpIndep
  staticShadowRun staticShadowEvent staticShadowReachable staticShadowMemory
  dftStaticAbort dftStaticEventAbort dftStaticShadowObservation dftStaticMemoryObservation dftStaticMemoryInv dftStaticContextSim dftStaticRequestSim dftStaticGasContract
  (* passes: FMP lowering composition, memory merging *)
  fmpLowerSequenceExec mmTransform memzeroFrame
  mmBlockSimProofs mmSupplyWfProofs mmSupplySsaProofs
  (* O1: lifting per-function pass facts to the stage contract *)
  o1PassLift
  (* O1: the pipeline's request companion at an abort *)
  o1PipelineRequests
  (* O1: joint simulation, abort requests and memory for static frames *)
  o1StaticPipelineCorrect
  o1PipelineMemoryLoweredAbort
  (* codegen and compiler units: frame simulation, stack planning, unit checks,
     codegen request prefix *)
  genFrameSim stackPlanGenCompute o1SourceUnitCheck unitMemInv
  codegenRequestPrefix callTraceFrame guardPushProjections
  gasFocusPrefixDriver gasFocusStaticPrefixDriver focusFrontierBudget
  gasFocusConcretizeGhostCutHistory gasFocusConcretizeCutFrameSupport
  fnStaticAbortSim
  contextStaticAbortRel
  staticAbortMemDefs
  (* lowering: ABI correctness, target/place steps, typed copies and hashing,
     place typing *)
  abiProofs targetPlaceSimCases typedCopyAgreement bytestringHashProps
  placeTypingE2EProps
  (* lowering: entry decoding, allocation frames and registration, constructor
     arguments, nonreentrancy, byte-builtin and concat memory, conversion from
     bytes, widened returns *)
  actualDecoderPackaging actualRegistrationCode actualEntryAllocationFrame
  allocaHistoryFragment ctorRegisterArgs
  nonreentrantEntry nonreentrantSource nonreentrantExit
  builtinBytesMemory concatMemory exprSimConvertFromBytes
  stmtSimReturnWiden
  (* body memory pieces kept for the builtin and raw_call lanes, and the S1
     statement reason theories *)
  bodyMemArrayLayout bodyMemTupleLayout bodyMemBiMethodIdEndpoint
  bodyMemEcArithAssemble bodyMemEcArithSafe bodyMemRawCallFinish
  stmtReasonKindsMemory stmtSimAugAssignPlaceStorage
  stmtSimIfCounted stmtSimRaise stmtSimSeqMem
  (* assignment-to-place pieces the deleted stmtSimAssignPlace imported *)
  immutableAssignMetadata immutableAssignRepresentation immutableAssignStore
  immutableDeployAssignRestore immutableAssignCode immutableAssignEmpty
  immutableAssignCompose immutableAssignOpen
  assignPlacePureFacts assignPlacePureCode assignPlaceEmpty
  assignPlaceEmptyCompose assignPlaceContinuation assignPlaceCallerFacts
  assignPlaceGasCompose assignPlaceStoreReady
  assignEffectfulIndexNonempty assignEffectfulIndexUnifiedStore
  assignEffectfulIndexEmptyCase assignEffectfulIndexNonmutating
  (* whitelist: retained raw-call and CREATE compiler shape proofs *)
  whitelistS2CreateShape whitelistS2Shape
  (* pointer safety of the lowering *)
  batchCopyRobustPtr liveArrayTransportPtr normalizationAllocPtr
  ptrSafetyTransport returnMetadataPtr staticTypeFitsPtr structChildPtr
  wordCopyRobustPtr
  (* end-to-end runtime correctness *)
  e2eCorrectness guardRequestAlignment
  (* sufficient gas, the companions to the call and deploy theorems *)
  e2eGasSufficient e2eGasSufficientTop
  (* deployment: the constructor frame and deploy correctness *)
  e2eDeployCorrectness
  (* body induction: custom-error raise and assert pieces *)
  bodyCustomErrorRaise bodyCustomErrorAssert stmtSimCustomErrorPath
  bodyCustomErrorMemRaise bodyCustomErrorMemAssert stmtSimCustomErrorMemPath
  (* codegen: its assembly is label-disciplined (the asm optimizer's premise) *)
  codegenLabelDisciplined
  codegenSymOwnRel
  (* bytecode: a passing operand-stack checker excludes frame overflow *)
  stackBoundSoundness
  asmFinalizerPrefix
