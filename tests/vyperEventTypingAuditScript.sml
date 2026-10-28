Theory vyperEventTypingAudit
Ancestors
  vyperTypeSystem vyperTypeContract vyperTypeEnvExtension
  vyperTypeEvalSoundness vyperTypeEvalStoragePreservation
  vyperTypeInitialState vyperTypeContractStaticMaps
  vyperTypeContractContext vyperTypeContractFunction
  vyperTypeSoundness vyperCheckContractLibTest

val _ = List.app (fn thy => List.app (fn (name,th) =>
  if List.exists (fn s => s <> "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then raise Fail ("oracle: " ^ thy ^ "." ^ name) else ()) (DB.thms thy))
  ["vyperTypeSystem", "vyperTypeContract", "vyperTypeEnvExtension",
   "vyperTypeEvalSoundness", "vyperTypeEvalStoragePreservation",
   "vyperTypeInitialState", "vyperTypeContractStaticMaps",
   "vyperTypeContractContext", "vyperTypeContractFunction",
   "vyperTypeSoundness", "vyperCheckContractLibTest"];
