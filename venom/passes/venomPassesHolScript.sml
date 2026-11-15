(* Roll-up theory for all venom compiler passes *)
Theory venomPassesHol
Ancestors
  venomPassDispatcherProps
  (* phi elimination *)
  phiElim
  (* revert-to-assert *)
  rta
  (* simple rewrite passes *)
  assertElim
  overflowElim
  literalsCodesize
  removeUnused
  concretizeMemLoc
  (* lower dload/dloadbytes *)
  lowerDload
  (* branch optimization *)
  branchOpt
  (* single use expansion *)
  singleUseExpansion
  (* assert combiner *)
  assertCombiner
  (* affine folding *)
  affineFolding
  (* algebraic optimization *)
  algebraicOpt
  (* mem2var promotion *)
  mem2var
  (* CFG structural passes *)
  tailMerge
  simplifyCfg
  o1SimplifyCfgGasEvents
  cfgNorm
  o1ContractCfgNormGas
  o1ContractCfgNormCursorBlocks
  o1ContractCfgNormCursorReturns
  o1ContractCfgNormCursorProjection
  (* memory passes *)
  loadElim
  deadStoreElim
  memoryCopyElision
  (* dataflow-driven passes *)
  assignElim
  cse
  sccp
  (* interprocedural *)
  functionInliner
  (* configured pipeline runner structural guarantees *)
  venomPipelineRunnerProps venomPipelineData
  (* dead function traversal *)
  dftCorrectnessFinal
  dftGasMaskRequests dftGasPrefixProvider
  (* invoke copy forwarding *)
  internalReturnCopyFwdProofs
  readonlyInvokeCopyFwdProofs
  (* SSA insertion for variables absent from liveness *)
  o1LabelFlowPhiPruning
  (* symbolic layout and label flow through the O1 pipeline *)
  o1CodeEndOffset o1LabelFlowCompose o1SymStaticPipeline o1SymStaticData
  (* symbolic assembly finalizers and their codegen correctness bridge *)
  asmOptNonemptyFinalizer codegenAsmOpt
