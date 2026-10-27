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
  cfgNorm
  makeSsa
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
  venomPipelineRunnerProps
  (* dead function traversal *)
  venomDft
  (* invoke copy forwarding *)
  internalReturnCopyFwdProofs
  readonlyInvokeCopyFwdProofs
