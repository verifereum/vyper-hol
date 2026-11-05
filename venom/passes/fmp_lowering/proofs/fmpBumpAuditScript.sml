(* Task proof-integrity audit. *)
Theory fmpBumpAudit
Ancestors
  fmpLowerExec fmpLowerSequenceExec fmpLowerProps emitSim genBlockSim fmpWfProps
  venomExecProofs venomMemProofs mem2varBlockSimHelpers dftBlockSim
  allocaRemapProofs

fun check_closed thy (name,th) =
  if null (Thm.hyp th) andalso
     List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then print ("Kernel-closed: " ^ thy ^ "." ^ name ^ "\n")
  else raise Fail ("Incomplete task theorem: " ^ thy ^ "." ^ name);

val _ = List.app (fn thy =>
  List.app (check_closed thy) (DB.thms thy))
  ["fmpLowerExec", "fmpLowerRestoreExec", "fmpLowerSequenceExec",
   "fmpLowerIndexedProps", "fmpRestoreProps", "fmpLedgerProps",
   "fmpProvenanceProps", "fmpReclaimProps", "fmpAliasProps",
   "fmpLowerProps", "emitSim", "fmpWfProps",
   "venomExecProofs", "venomMemProofs", "mem2varBlockSimHelpers", "dftBlockSim",
   "allocaRemapProofs"];

val _ = List.app (check_closed "genBlockSim") (DB.thms "genBlockSim");
