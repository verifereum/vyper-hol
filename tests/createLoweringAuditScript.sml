(* Rebuild the creation-specific proof boundaries together and reject any
   theorem whose proof depends on an oracle admission. *)
Theory createLoweringAudit
Ancestors
  bufferAllocationExecution abiWordTupleExecution abiBytesValueEncoding
  abiBytesExecution abiBytesStepExecution
  abiBytesFinalExecution abiBytesFrameExecution
  createDispatchExecution
  slotCopyExecution createRequestCorrespondence exprCallbackContracts

val checked_theories =
  ["bufferAllocationExecution", "abiValueEncoding",
    "abiBytesValueEncoding", "abiBytesExecution",
    "abiBytesStepExecution", "abiBytesFinalExecution",
    "abiBytesFrameExecution",
   "abiTupleValueEncoding", "abiCopyExecution",
   "abiWordTupleExecution", "createDispatchExecution",
   "createMemoryInterface", "copyExecution", "slotCopyExecution",
   "createSourceCallback", "createFrameInterface", "createRequestCorrespondence",
   "createOracleExecution", "exprCallbackContracts"];

val _ = app (fn thy => app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ thy ^ "." ^ name))
  (DB.thms thy)) checked_theories;
