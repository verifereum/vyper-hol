Theory evalCompilerEventParity
Ancestors
  evalCompilerEventBytes20 evalCompilerEventStorageBytes20
  evalCompilerEventWidenDynarray evalCompilerEventWidenNestedString
  evalCompilerEventWidenTuple evalCompilerEventWidenFixedDynamic
  evalCompilerEventForwardStruct vyperEventForwardStruct
  vyperEventRegression vyperImportedEventRegression vyperEventArgumentLifetime

(* Audit certificates and final byte equalities together.  Imported proof
   admissions must not enter a fixture claim through an evaluation rewrite. *)
fun audit_event_theory theory =
  List.app (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles
      then () else raise Fail ("unclosed event theorem: " ^ theory ^ "." ^ name)
    end) (DB.thms theory)

val () = List.app audit_event_theory
  ["eventFixturePrograms", "evalCompilerEventBytes20",
   "evalCompilerEventStorageBytes20", "evalCompilerEventWidenDynarray",
   "evalCompilerEventWidenNestedString", "evalCompilerEventWidenTuple",
   "evalCompilerEventWidenFixedDynamic", "evalCompilerEventForwardStruct",
   "vyperEventForwardStruct", "vyperEventRegression",
   "vyperImportedEventRegression", "vyperEventArgumentLifetime"]
