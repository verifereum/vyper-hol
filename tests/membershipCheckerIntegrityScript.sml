Theory membershipCheckerIntegrity
Ancestors vyperMembershipSemanticsTest vyperTypeSoundness

val _ = List.app (fn thy => List.app (fn (name, th) =>
  if null (Thm.hyp th) andalso
     List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) andalso
     null (#2 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("Incomplete membership dependency: " ^ thy ^ "." ^ name))
  (DB.thms thy))
  ["vyperTypeSystem", "vyperTypeBuiltins", "vyperTypeExprSoundness",
   "vyperTypeSoundness", "vyperMembershipSemanticsTest"];
