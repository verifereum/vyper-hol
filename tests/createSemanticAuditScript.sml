Theory createSemanticAudit
Ancestors
  vyperCreate vyperEvalOutcomeSuffix vyperLogPreservation
  vyperTypeExtCallSoundness vyperEvalPreservesScopes
  vyperEvalExprPreservesScopesDom vyperEvalPreservesImmutablesDom
  vyperExprNoControl vyperTypeEvalStoragePreservation vyperSmallStep

val audited_theories =
  ["vyperCreate", "vyperEvalOutcomeSuffix", "vyperLogPreservation",
   "vyperTypeExtCallSoundness", "vyperEvalPreservesScopes",
   "vyperEvalExprPreservesScopesDom", "vyperEvalPreservesImmutablesDom",
   "vyperExprNoControl", "vyperTypeEvalStoragePreservation", "vyperSmallStep"];
val _ = List.app (fn thy =>
  let val entries = DB.thms thy
      val bad = List.filter (fn (_,th) =>
        List.exists (fn s => s <> "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))) entries
  in
    if null bad then print ("CREATE SEMANTIC AUDIT: " ^ thy ^ " clean (" ^
      Int.toString (length entries) ^ " theorems)\n")
    else raise Fail ("Oracle dependencies in " ^ thy ^ ": " ^
      String.concatWith ", " (map #1 bad))
  end) audited_theories;
