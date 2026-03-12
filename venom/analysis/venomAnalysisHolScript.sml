(* Roll-up theory for all venom analysis infrastructure *)
Theory venomAnalysisHol
Ancestors
  (* shared *)
  venomWf
  venomEffects
  venomInstProps
  memLocDefs
  memLocProps
  (* cfg *)
  cfgAnalysis
  (* fcg *)
  fcgAnalysis
  (* dataflow *)
  dfIterateProps
  latticeProps
  worklistProps
  dfHelperProps
  dfAnalyzeProps
  dfAnalyzeWidenProps
  (* liveness *)
  livenessAnalysis
  livenessGenericDefs
  (* dfg *)
  dfgAnalysis
  (* dominators *)
  dominatorAnalysis
  (* base pointer analysis *)
  basePtrProps
  (* available expression *)
  availExprAnalysis
  (* stack order *)
  stackOrderProps
  (* memory alias *)
  memAliasProps
  (* memory SSA *)
  memSSAProps
  (* variable definition *)
  varDefAnalysis
  (* variable range *)
  variableRangeAnalysis
  (* analysis-driven simulation bridge *)
  analysisSimProps
