Theory sourceOrdinaryAcceptanceTest
Ancestors
  sourceOrdinaryAcceptanceBase sourceOrdinaryCoreTest sourceOrdinaryExprTest
  sourceOrdinaryModulesTest sourceOrdinaryDaddyTest
Libs
  sourceOrdinaryAcceptanceLib

(* All rows, not a green prefix: independently exported, kernel-closed phase,
   source-retention, linkage and both checker certificates must exist. *)
val groups = [("sourceOrdinaryCoreTest",List.take (sourceOrdinaryAcceptanceLib.rows,6)),
  ("sourceOrdinaryExprTest",List.take (List.drop (sourceOrdinaryAcceptanceLib.rows,6),6)),
  ("sourceOrdinaryModulesTest",List.take (List.drop (sourceOrdinaryAcceptanceLib.rows,12),13)),
  ("sourceOrdinaryDaddyTest",List.drop (sourceOrdinaryAcceptanceLib.rows,25))];
val () = List.app (fn (theory,rows) => List.app (fn (name,_) =>
  List.app (fn suffix => sourceOrdinaryAcceptanceLib.audit
    (DB.fetch theory (name ^ suffix)))
    ["_phase","_original","_link","_check","_legacy_check"]) rows) groups;
val () = print "ORDINARY_ALL_26_KERNEL_CLOSED\n";
