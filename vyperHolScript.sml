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
  (* frontend, its cv translation, and the test runner *)
  vyperTestRunner jsonToVyperCV
  (* compiler passes *)
  venomPassesHol
  (* analysis roll-up *)
  venomAnalysisHol
  (* lowering, pipeline, codegen and e2e *)
  vyperLoweringHol
  (* Venom execution: alloca size caching, jump independence *)
  allocaCacheProps jumpIndep
  (* passes: FMP lowering composition, memory merging, the concretize
     simulation's oracle projection *)
  fmpLowerSequenceExec mmTransform memzeroFrame concretizeOracleSim
  mmBlockSimProofs mmSupplyWfProofs mmSupplySsaProofs
  (* O1: lifting per-function pass facts to the stage contract *)
  o1PassLift
  (* codegen and compiler units: frame simulation, stack planning, unit checks *)
  genFrameSim stackPlanGenCompute o1SourceUnitCheck unitMemInv
  (* lowering: ABI correctness, target/place steps, typed copies and hashing,
     place typing *)
  abiProofs targetPlaceSimCases typedCopyAgreement bytestringHashProps
  placeTypingE2EProps
  (* lowering: entry decoding, allocation frames and registration, constructor
     arguments, nonreentrancy, byte-builtin and concat memory, conversion from
     bytes, widened returns, body memory *)
  actualDecoderPackaging actualRegistrationCode actualEntryAllocationFrame
  allocaHistoryFragment ctorRegisterArgs
  nonreentrantEntry nonreentrantSource nonreentrantExit
  builtinBytesMemory concatMemory exprSimConvertFromBytes
  stmtSimReturnWiden bodyMemory
  (* pointer safety of the lowering *)
  batchCopyRobustPtr entryHaltPtr liveArrayTransportPtr normalizationAllocPtr
  ptrSafetyTransport returnMetadataPtr staticTypeFitsPtr structChildPtr
  typedCopyArrayExecutionPtr wordCopyRobustPtr
  (* deployment: the constructor frame and deploy correctness *)
  e2eDeployCorrectness
