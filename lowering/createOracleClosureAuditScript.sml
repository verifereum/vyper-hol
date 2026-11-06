Theory createOracleClosureAudit
Ancestors
  createOracleExecution createFrameInterface
  passSharedFrame passSharedVarFrame dftCommutation execEquivProofs
  execEquivParamBase execEquivParamHelpers execEquivParamProps
  deadStoreElimProofs mem2varBlockSimHelpers allocaRemapProofs
  prevBbIndep concretizeMemLocProofs ssaRenamedSim tailMergeStep

(* This is a production-boundary audit, not whole-task validation.  Check the
   persisted theorem tags as well as rebuilding the strict consumers. *)
val audited_create_boundary_theories =
  ["createOracleExecution", "createFrameInterface",
   "venomCallOracleDefs", "venomExecSemantics",
   "passSharedFrame", "passSharedVarFrame", "dftCommutation",
   "execEquivProofs", "execEquivParamBase", "execEquivParamHelpers",
   "execEquivParamHelpers2", "execEquivParamProofs", "execEquivParamProps",
   "deadStoreElimProofs", "mem2varBlockSimHelpers", "allocaRemapProofs",
   "oracleExecProps", "venomInstProofs1", "venomInstProofs", "instIdxIndep",
   "execEquivParamDefs", "prevBbIndep", "concretizeMemLocProofs",
   "ssaRenamedSim", "tailMergeStep"];

val _ = app (fn thy =>
  let val thms = DB.thms thy
  in
    if null thms then raise Fail ("Empty audited theory: " ^ thy) else ();
    app (fn (name, th) =>
      if null (List.filter (fn s => s <> "DISK_THM")
                 (#1 (Tag.dest_tag (Thm.tag th)))) then ()
      else if thy = "deadStoreElimProofs" andalso
              List.exists (fn n => n = name)
                ["dse_function_space_correct", "dse_function_correct"] then
        (* Unchanged pre-existing whole-pass admissions.  Neither is used by
           the CREATE boundary or the repaired effects classification. *)
        print ("UNCHANGED ORACLE DEBT: " ^ thy ^ "." ^ name ^ "\n")
      else raise Fail ("Oracle dependency in " ^ thy ^ "." ^ name)) thms;
    print ("CREATE boundary audit: inspected " ^ thy ^ "\n")
  end) audited_create_boundary_theories;
