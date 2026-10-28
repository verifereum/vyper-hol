Theory sourceOrdinaryProgramResidualTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract"];
val () = app sourceOrdinaryProgramTestLib.ordinary
  (List.filter (fn (name,_) => List.exists (fn n => n = name)
    ["in_static_array","nested_pop","decimal_folding","unreachable"])
    sourceOrdinaryAcceptanceLib.rows);
