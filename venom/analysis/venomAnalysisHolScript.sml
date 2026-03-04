(* Roll-up theory for all venom analysis infrastructure *)
Theory venomAnalysisHol
Ancestors
  (* shared — can be removed once used by other analysis theories *)
  venomEffects
  memLocDefs
  (* cfg *)
  cfgAnalysis
  (* fcg *)
  fcgAnalysis
  (* dataflow *)
  dfIterateProps
  latticeProps
  worklistProps
  dfHelperProps
  (* liveness *)
  livenessAnalysis
  (* dfg *)
  dfgAnalysis
