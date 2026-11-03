(* check_contract, in runtime and deploy mode, on each annotated-AST JSON file
   listed (one path per line) in the file named by $CHECK_LIST, as
   memoryStoreWitnessLib.program checks a witness before compiling it.
   Prints "CHECKED <path>" or "CHECKER-REJECT <path>: <reason>" per file.
   tools/bytecode_fuzz.py runs it with `holbuild run`. *)
load "vyperCheckContractFrontendLib";

fun check path = let
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  val _ = vyperCheckContractLib.check_contract input
  val _ = vyperCheckContractLib.check_contract
    {in_deploy = true, address = #address input,
     modules = #modules input, layouts = #layouts input}
in "CHECKED " ^ path end
handle e => "CHECKER-REJECT " ^ path ^ ": " ^
  String.translate (fn #"\n" => " " | c => str c) (General.exnMessage e)

val paths = String.tokens (fn c => c = #"\n")
  (TextIO.inputAll (TextIO.openIn (valOf (OS.Process.getEnv "CHECK_LIST"))))
val () = List.app (fn p => (print (check p ^ "\n"); TextIO.flushOut TextIO.stdOut)) paths
val () = OS.Process.exit OS.Process.success
