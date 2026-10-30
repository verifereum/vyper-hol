(* Task boundaries must be closed kernel theorems, including their dependencies.
   Unrelated admitted compiler simulation cases are outside this audit. *)
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

fun audit (name, th) =
  if null (Thm.hyp th) andalso
     List.all (fn tag => tag = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) andalso
     null (#2 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("Unchecked task proof: " ^ name);

val () = List.app (List.app audit o DB.thms)
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

val () = List.app audit
  [("source supply entry non-vacuity",
     DB.fetch "vyperTypeInitialState" "type_soundness_preconditions_satisfiable"),
   ("observed deletion prefix", outcome_of_added_deletions),
   ("source typing domain", source_typing_outcomes_supply),
   ("raw event values", log_entry_equiv_raw_event),
   ("raw event correspondence", log_entry_corresponds_raw_event)];
