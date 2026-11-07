(* Source integration diagnostic: no new logical claims. *)
Theory concretizeAnalysisInterfaceAudit
Ancestors venomWf

val _ = print ("AVAILABILITY EXPORT: " ^
  thm_to_string venomWfTheory.fn_defs_reach_uses_def ^ "\n");
val _ = print ("PATH EXPORT: " ^
  thm_to_string venomWfTheory.def_on_all_paths_def ^ "\n");
