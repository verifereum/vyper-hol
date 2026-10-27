(* Phase-1 integrity audit: does not execute bytecode parity fixtures. *)
Theory livenessProofIntegrity
Ancestors livenessAnalysisProps removeUnusedSsaProofs

val audited_theories =
  ["livenessDefs", "livenessTransferProofs", "livenessBlockProofs",
   "livenessInvariantProofs", "livenessRankProofs", "livenessWorklistProofs",
   "livenessTerminationProofs", "livenessConvergenceProofs",
   "livenessSoundProofs", "livenessLocalProofs", "livenessProofs",
   "livenessAnalysisProps", "removeUnusedSsaProofs"];
val _ = List.app (fn thy => List.app (fn (name, th) =>
  if null (Thm.hyp th) andalso
     List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("Incomplete liveness theorem: " ^ thy ^ "." ^ name))
  (DB.thms thy)) audited_theories;
