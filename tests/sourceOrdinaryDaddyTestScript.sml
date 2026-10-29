Theory sourceOrdinaryDaddyTest
Ancestors
  sourceOrdinaryAcceptanceBase sourceModuleElaborate vyperTypeContract
Libs
  sourceOrdinaryAcceptanceLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract"];
val () = sourceOrdinaryAcceptanceLib.run_cases
  (List.drop (sourceOrdinaryAcceptanceLib.rows,25));
