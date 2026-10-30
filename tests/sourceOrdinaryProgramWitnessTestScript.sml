Theory sourceOrdinaryProgramWitnessTest
Ancestors
  sourceOrdinaryProgram sourceModuleContext sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib sourceBytecodeFixtureLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract/source_syntax",
  "../lowering/defs/bytecode/folded-value-oracle"];
val names = List.filter (fn name => name <> "method_id_var") sourceBytecodeFixtureLib.names;
val () = if length names = 36 then () else raise Fail "whole program inventory";
val outcomes = map (fn name => (sourceOrdinaryProgramTestLib.witness name; true)
  handle e => (print ("BRIDGE_WITNESS_FAIL " ^ name ^ ": " ^ General.exnMessage e ^ "\n");false)) names;
val () = if List.all I outcomes then () else raise Fail "ordinary witness failures";
