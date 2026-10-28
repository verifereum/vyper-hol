(* Reopen and audit the unchanged legacy sourceMeaning exports. Run in a
   project where these theories have already been built; this is a tag audit,
   not a claim to force-rebuild their backend dependency closure. The new six
   location theories are force-built/audited by their own test roots. *)
val theories =
  ["sourceMeaningConst","sourceMeaningValue","sourceMeaningDefs","sourceMeaningCode",
   "sourceMeaningElaborate","sourceMeaningEffects","sourceMeaningRuntime","sourceMeaningEnv",
   "sourceMeaningStmtDefs","sourceMeaningStmt","sourceMeaningProgramDefs","sourceMeaningProgram",
   "sourceMeaningExampleDefs","sourceMeaningExample","sourceMeaningProgramTest","sourceMeaningTest",
   "sourceMeaningCallDefs","sourceMeaningCallExampleDefs","sourceMeaningDecl","sourceMeaningDispatch",
   "sourceMeaningCall","sourceMeaningCompile","sourceMeaningCallTest","sourceMeaningCheckedTest",
   "sourceMeaningAggregateExample","sourceMeaningAggregateTest","sourceMeaningPolicy",
   "sourceMeaningPolicyDecl","sourceMeaningModules","sourceMeaningExportTest","sourceMeaningWitnessTest"];
val () = List.app (fn thy => load(thy ^ "Theory")) theories;
val total = ref 0;
val () = List.app (fn thy => let val exports = DB.thms thy
  val () = if null exports then raise Fail("empty source audit: " ^ thy) else ()
  in List.app (fn (name,th) => let val (oracles,axioms) = Tag.dest_tag(Thm.tag th)
    in if null(Thm.hyp th) andalso null axioms andalso List.all (fn s => s = "DISK_THM") oracles
      then () else raise Fail("source meaning kernel audit: " ^ thy ^ "." ^ name) end) exports;
    total := !total + List.length exports;
    print("SOURCE_MEANING_LEGACY_KERNEL_CLOSED " ^ thy ^ " exports=" ^
      Int.toString(List.length exports) ^ "\n") end) theories;
val () = print("SOURCE_MEANING_LEGACY_AUDIT theories=31 exports=" ^ Int.toString(!total) ^ "\n");
