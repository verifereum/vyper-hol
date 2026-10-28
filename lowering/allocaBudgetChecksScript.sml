(* Check saved proof dependencies, including the frontier witness.
   Loaded tags preserve oracle dependencies but not upstream axioms. *)
Theory allocaBudgetChecks
Ancestors
  allocaBudgetProps allocaFrontierWitness

fun check_alloca_theorem thy (name, th) =
  let
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print ("ALLOCA_AUDIT " ^ thy ^ "." ^ name ^ " OK\n")
    else raise Fail (thy ^ "." ^ name ^ ": admitted proof dependency")
  end;

val () = List.app
  (fn thy => List.app (check_alloca_theorem thy) (DB.thms thy))
  ["allocaBudgetProps", "allocaFrontierWitness"];
