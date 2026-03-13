(* Roll-up theory for all venom compiler passes *)
Theory venomPassesHol
Ancestors
  (* shared pass infrastructure *)
  passSharedDefs passSharedProps
  (* phi elimination *)
  phiElim
  (* revert-to-assert *)
  rta
  (* lower dload/dloadbytes *)
  lowerDload
  (* float allocas to entry *)
  floatAllocas
  (* fix free var space memory locations *)
  fixMemLocations
  (* branch optimization *)
  branchOpt
  (* single use expansion *)
  singleUseExpansion
  (* assert combiner *)
  assertCombiner
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
