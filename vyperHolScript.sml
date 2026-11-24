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
  codegenStaticAbort codegenStaticAbortAsmOpt staticAbortFrameException
  staticAbortAsmOptCorrect
  runtimeLabelReadiness
  o1LabelReadiness
  runtimeLabelEntry
  o1LabelStages
  (* semantics properties *)
  vyperSemanticsHol
  (* frontend, its cv translation, and the test runner *)
  vyperTestRunner jsonToVyperCV jsonToVyperExprProps
  (* compiler passes *)
  venomPassesHol
  (* analysis roll-up *)
  venomAnalysisHol
  (* lowering, pipeline, codegen and e2e *)
  vyperLoweringHol
  constSubstStmts constSubstStmtsPreserve
  (* Venom execution: alloca size caching, jump independence *)
  allocaCacheProps jumpIndep
  staticShadowRun staticShadowEvent staticShadowReachable
  dftStaticAbort dftStaticEventAbort dftStaticShadowObservation dftStaticContextSim dftStaticRequestSim
  (* passes: FMP lowering composition, memory merging *)
  fmpLowerSequenceExec mmTransform memzeroFrame
  mmBlockSimProofs mmSupplyWfProofs mmSupplySsaProofs
  (* O1: lifting per-function pass facts to the stage contract *)
  o1PassLift
  (* O1: DFT's request companion at an abort *)
  dftRequestsGas
  (* O1: joint simulation, abort requests and memory for static frames *)
  o1StaticPipelineCorrect
  o1PipelineMemoryLoweredAbort
  (* codegen and compiler units: frame simulation, stack planning, unit checks,
     codegen request prefix *)
  genFrameSim o1SourceUnitCheck unitMemInv
  codegenRequestPrefix callTraceFrame guardPushProjections
  gasFocusParentProofs gasFocusStaticPrefixDriver
  gasFocusConcretizeGhostCutHistory gasFocusConcretizeCutFrameSupport
  fnStaticAbortSim
  contextStaticAbortRel
  (* lowering: ABI correctness, target/place steps, typed copies and hashing,
     place typing *)
  abiEncoderObserverCode
  abiProofs targetPlaceSimCases typedCopyAgreement bytestringHashProps
  (* lowering: entry decoding, allocation frames and registration, constructor
     arguments, nonreentrancy, byte-builtin and concat memory, conversion from
     bytes, widened returns *)
  actualDecoderPackaging actualRegistrationCode actualEntryAllocationFrame
  allocaHistoryFragment ctorRegisterArgs
  entryPtrSeamRegisterMods[qualified,ignore_grammar]
  ctorDeployMemoryRunPtrPrefixEntrySemanticMods[qualified,ignore_grammar]
  nonreentrantEntry nonreentrantSource nonreentrantExit
  builtinBytesMemory concatMemory exprSimConvertFromBytes
  stmtSimReturnWiden
  (* body memory pieces kept for the builtin and raw_call lanes, and the S1
     statement reason theories *)
  bodyMemArrayLayout bodyMemTupleLayout bodyMemBiMethodIdEndpoint
  bodyMemEcArithAssemble bodyMemEcArithSafe bodyMemRawCallFinish
  stmtSimAugAssignPlaceStorage
  (* assignment-to-place pieces the deleted stmtSimAssignPlace imported *)
  immutableAssignMetadata immutableAssignRepresentation immutableAssignStore
  immutableDeployAssignRestore immutableAssignCode immutableAssignEmpty
  immutableAssignCompose immutableAssignOpen
  assignPlacePureCode assignPlaceEmpty
  assignPlaceEmptyCompose
  assignPlaceGasCompose assignPlaceBytesStore
  (* Linked checker support for the compiler invariant. *)
  whitelistLinkedHeaderProps[qualified,ignore_grammar]
  whitelistLinkedConstProps[qualified,ignore_grammar]
  whitelistLinkedBodyProps[qualified,ignore_grammar]
  (* pointer safety of the lowering *)
  normalizationAllocPtr
  ptrSafetyTransport staticTypeFitsPtr
  (* end-to-end runtime correctness *)
  e2eCorrectness
  (* sufficient gas, the companions to the call and deploy theorems *)
  e2eGasSufficient e2eGasSufficientTop
  (* deployment: the constructor frame and deploy correctness *)
  e2eDeployCorrectness
  (* linked-module boundaries for runtime and deployment *)
  e2eModsDefs[qualified,ignore_grammar] e2eDeployModsDefs[qualified,ignore_grammar]
  (* body induction: custom-error raise and assert pieces *)
  stmtSimCustomErrorRevert
  (* codegen: its assembly is label-disciplined (the asm optimizer's premise) *)
  codegenLabelDisciplined
  codegenSymOwnRel
  symS7OwnHol
  (* bytecode: a passing operand-stack checker excludes frame overflow *)
  stackBoundSoundness
  asmFinalizerPrefix
