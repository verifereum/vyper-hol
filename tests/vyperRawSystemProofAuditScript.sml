(* Check exported task theorem hypotheses and retained oracle tags.
   Axioms imported from disk need same-session checks in their defining theories;
   unrelated admitted compiler simulation cases are outside this audit. *)
Theory vyperRawSystemProofAudit
Ancestors
  vyperTypeSoundness vyperTypeSelectedEntrySoundness
  vyperTypeDeploymentSoundness vyperTypeExternalCallMachine
  vyperTypeDeploymentMachine vyperTypeEvalSoundness
  vyperTypeEvalStoragePreservation vyperSystemControl
  vyperSystemHaltTest rawReturnCopy
  vyperExtCallCpsCVTest vyperSendCpsCVTest asmOracleRegression
  vyperOracleIntegrationTest evmStepSim prefixSim prefixExec strongPrefixSim spillSim
  venomCallActivationRegression asmCallActivationRegression unitTransformChecks
  e2eDefs e2eComposition e2eBoundaryTest execEquivParamDefs oracleExecProps callTrace
Libs
  proofAuditLib

val () = List.app proofAuditLib.check_theory
  ["vyperTypeSoundness", "vyperTypeSelectedEntrySoundness",
   "vyperTypeDeploymentSoundness", "vyperTypeExternalCallMachine",
   "vyperTypeDeploymentMachine", "vyperTypeEvalSoundness",
   "vyperTypeEvalStoragePreservation", "vyperSystemControl",
   "vyperSystemHaltTest",
   "rawReturnCopy", "e2eComposition", "e2eBoundaryTest", "execEquivParamDefs", "oracleExecProps",
   "vyperExtCallCpsCVTest", "vyperSendCpsCVTest", "asmOracleRegression",
   "vyperOracleIntegrationTest", "evmStepSim", "prefixSim", "prefixExec",
   "strongPrefixSim", "spillSim", "venomCallActivationRegression",
   "asmCallActivationRegression", "unitTransformChecks"];

val () = proofAuditLib.check_all
  [("source supply entry non-vacuity",
     DB.fetch "vyperTypeInitialState" "type_soundness_preconditions_satisfiable"),
   ("observed deletion prefix", outcome_of_added_deletions),
   ("source typing domain", source_typing_outcomes_supply),
   ("raw event values", log_entry_equiv_raw_event),
   ("raw event correspondence", log_entry_corresponds_raw_event)];
