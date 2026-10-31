(* Kernel tag audit of task-scoped results, including cached theories. *)
Theory vyperMembershipAuditTest
Ancestors vyperMembershipMatrixTest vyperMembershipSemanticsTest
  vyperSmallStep vyperTypeBuiltins bytestringHashProps exprLoweringProps

fun check_tag theory (name,th) = let
  val oracles = #1 (Tag.dest_tag (Thm.tag th))
in
  if List.all (fn x => x = "DISK_THM") oracles then ()
  else raise Fail ("task proof has oracle tags: " ^ theory ^ "." ^ name)
end
val () = List.app (fn theory => List.app (check_tag theory) (DB.thms theory))
  ["vyperMembershipParityTest","vyperMembershipMatrixTest",
   "vyperMembershipSemanticsTest","vyperSmallStep","vyperTypeBuiltins",
   "bytestringHashProps"]
val () = List.app (fn name => check_tag "exprLoweringProps"
  (name,DB.fetch "exprLoweringProps" name))
  ["list_membership_small_traces","array_membership_entry_traces"]
