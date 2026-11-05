(* Checked JSON/AST inputs, separate from the compiler evaluator. *)
structure evalCompilerEntryFixtureLib = struct
open HolKernel Parse boolLib bossLib

fun checked_entry_fixture name = let
  val path = "../external-entries/ast/" ^ name ^ ".json"
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  val checked = vyperCheckContractLib.check_contract input
  val _ = optionSyntax.dest_some (rhs (concl checked))
  val (modules,_) = listSyntax.dest_list (#modules input)
  val tops = case modules of [m] => snd (pairSyntax.dest_pair m)
    | _ => raise Fail "external fixture has imported modules"
in tops end
end
