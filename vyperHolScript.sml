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
  (* calldata and ABI *)
  abiProofs
  placeTypingE2EProps
  (* statements: nonreentrancy *)
  nonreentrantEntry
  (* pointer safety of the lowering *)
  batchCopyRobustPtr entryHaltPtr liveArrayTransportPtr normalizationAllocPtr
  ptrSafetyTransport returnMetadataPtr staticTypeFitsPtr structChildPtr
  typedCopyArrayExecutionPtr wordCopyRobustPtr
  (* end-to-end runtime correctness *)
  e2eCorrectness
  (* deployment: the constructor frame and deploy correctness *)
  e2eDeployCorrectness
  (* Venom execution: jump independence *)
  jumpIndep
  (* passes: oracle projections, FMP lowering, memory merging, SSA *)
  concretizeOracleSim
  fmpLowerSequenceExec
  mmBlockSimProofs mmSupplySsaProofs mmSupplyWfProofs
  (* codegen: stack planning *)
  stackPlanGenCompute
