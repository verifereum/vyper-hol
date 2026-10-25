(* Frontend inputs and independent compiler outputs supplied by G0006.
   Compiler certificates are kernel-derived and independent of expected bytes;
   expected bytes appear only in the final named comparison theorems. *)
structure membershipParityLib = struct
open HolKernel Parse boolSyntax
fun root () =
  case List.find (fn p => OS.FileSys.access
      (OS.Path.concat(p,"report.json"),[OS.FileSys.A_READ]))
    ["fixtures/membership","tests/fixtures/membership",
     "../tests/fixtures/membership","../../tests/fixtures/membership",
     "../../../tests/fixtures/membership","../../../../tests/fixtures/membership"] of
    SOME p => p
  | NONE => raise Fail "missing G0006 independent compiler artifacts"
fun input name = let
  val path = OS.Path.concat(root(),"inputs/" ^ name ^ ".json")
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy=false,address=``0w : address``,
     annotated_ast=JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout=JSONDecode.decodeFile jsonASTLib.storage_layout path}
in input end
fun program name = let
  val input = input name
  val _ = vyperCheckContractLib.check_contract input
  val _ = vyperCheckContractLib.check_contract
    {in_deploy=true,address= #address input,modules= #modules input,layouts= #layouts input}
in case #1 (listSyntax.dest_list (#modules input)) of
     [entry] => #2 (pairSyntax.dest_pair entry)
   | _ => raise Fail "expected single module"
end
val prepared = ref ([] : term list)
fun prepare_compile name = let
  val tops = program name
  val tm = ``compile_vyper (K SOME) (o1_policy all_capabilities) ^tops``
in
  if List.exists (aconv tm) (!prepared) then () else let
    val cert = computeLib.EVAL_CONV tm
    val _ = if null (hyp cert) andalso aconv (lhs (concl cert)) tm
            then () else raise Fail "invalid compiler evaluation certificate"
    val result = rhs (concl cert)
    val _ = if optionSyntax.is_some result orelse optionSyntax.is_none result
            then () else raise Fail "compiler evaluation did not normalize"
    val _ = print ("Compiler normalized: " ^ name ^ "\n")
    val _ = evalCompilerBytecodeLib.add_compile_eval cert
  in prepared := tm :: !prepared end
end
fun oracle name = let
  val path = OS.Path.concat(root(),"compiler/" ^ name ^ ".hex")
  val entries = List.mapPartial evalCompilerBytecodeLib.fixture_line
    (String.tokens (fn c => c = #"\n" orelse c = #"\r")
      (evalCompilerBytecodeLib.read_all path))
  fun bytes key = evalCompilerBytecodeLib.hex_bytes_tm
    (evalCompilerBytecodeLib.bytecode_fixture_value name entries key)
in pairSyntax.mk_pair(bytes "deploy",bytes "runtime") end
end
