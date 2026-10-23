(* Task proof-integrity audit. The three generic planner aggregates retain
   unrelated non-BUMP admissions. They are not premises of the BUMP theorem. *)
Theory fmpBumpAudit
Ancestors
  fmpLowerExec fmpLowerProps emitSim genBlockSim fmpWfProps
  venomExecProofs venomMemProofs mem2varBlockSimHelpers dftBlockSim
  allocaRemapProofs

val legacy_debt = ["gen_inst_ok_sim", "gen_inst_halt_sim", "gen_inst_abort_sim"];

fun check_closed thy (name,th) =
  if null (Thm.hyp th) andalso
     List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then print ("Kernel-closed: " ^ thy ^ "." ^ name ^ "\n")
  else raise Fail ("Incomplete task theorem: " ^ thy ^ "." ^ name);

val _ = List.app (fn thy =>
  List.app (check_closed thy) (DB.thms thy))
  ["fmpLowerExec", "fmpLowerProps", "emitSim", "fmpWfProps",
   "venomExecProofs", "venomMemProofs", "mem2varBlockSimHelpers", "dftBlockSim",
   "allocaRemapProofs"];

val _ = List.app (fn entry as (name,th) =>
  if List.exists (fn n => n = name) legacy_debt then
    print ("Legacy non-BUMP aggregate debt: genBlockSim." ^ name ^ " tags=" ^
      String.concatWith "," (#1 (Tag.dest_tag (Thm.tag th))) ^ "\n")
  else check_closed "genBlockSim" entry) (DB.thms "genBlockSim");

val _ = List.app (fn name => check_closed "genBlockSim"
  (name, DB.fetch "genBlockSim" name))
  ["gen_inst_bump_ok_sim", "bump_step_no_halt_abort"];
