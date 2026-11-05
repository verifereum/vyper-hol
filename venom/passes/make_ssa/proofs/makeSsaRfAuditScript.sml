Theory makeSsaRfAudit
Ancestors
  makeSsaCurrentDefs makeSsaCurrentProps makeSsaCurrentInduct
  contextCodegenRel venomWf cfgWf venomInst irSupply
  unitShapeDefs o1PassContract makeSsaCurrentRevertForward

(* Import probe: the existing, permitted base of the RF proof. *)
Theorem rf_same_after_assigns_empty:
  same_after_assigns [] a b <=> a = b
Proof
  simp[same_after_assigns_def]
QED

fun rf_check_theorem thy (name, th) =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail (thy ^ "." ^ name ^ ": admitted proof dependency; oracles=" ^
      String.concatWith "," oracles ^ "; axioms=" ^ Int.toString (length axioms))
  end;

val _ = List.app (fn thy =>
  if List.exists (fn bad => thy = bad)
    ["makeSsaCurrentWfSsa", "makeSsaCurrentSim", "makeSsaCurrentInputOk",
     "makeSsaCurrentNonDegenerate", "makeSsaCurrentFrameRf"] then
    raise Fail ("Forbidden ancestor: " ^ thy)
  else (List.app (rf_check_theorem thy) (DB.thms thy);
        print ("RF_BASE_AUDIT " ^ thy ^ " OK\n")))
  (Theory.ancestry "-");
