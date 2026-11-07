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
  (* Venom execution: oracle-aware core simulations, alloca size caching *)
  coreOracleSim coreOracleUpdates allocaCacheProps
  (* passes: FMP lowering composition, memory merging, oracle projections of
     the concretize and SSA simulations *)
  fmpLowerSequenceExec mmTransform memzeroFrame concretizeOracleSim ssaOracleSim
  (* lowering: ABI correctness, target/place steps, typed copies and hashing *)
  abiProofs targetPlaceSimCases typedCopyAgreement bytestringHashProps
  (* codegen and compiler units: frame simulation, stack planning, unit checks *)
  genFrameSim stackPlanGenCompute o1SourceUnitCheck unitMemInv
