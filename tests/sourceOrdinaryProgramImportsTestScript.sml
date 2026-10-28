Theory sourceOrdinaryProgramImportsTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract"];
(* Pairing/context regression in isolation from the separate builtin witnesses.
   All file and record calls retain the actual pre-erasure qualifier roots. *)
val names = ["duplicate_interface","imported_interface","interface_struct_return","imported_flag",
  "scoped_locals","imported_struct","imported_deploy","multimodule_storage"];
val () = app (fn name => sourceOrdinaryProgramTestLib.ordinary
  (valOf (List.find (fn (n,_) => name = n) sourceOrdinaryAcceptanceLib.rows))) names;
