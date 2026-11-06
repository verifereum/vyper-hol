(* C7.2: checked frontend acceptance and supported_program membership. *)
Theory evalCompilerAbiTupleString
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../abi-codegen/sources", "../abi-codegen/oracle",
   "../abi-codegen/parity-fixtures.txt"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../abi-codegen/oracle"

(* program checks the frontend contract in both deployment and runtime modes. *)
val tup_string_arg_program =
  memoryStoreWitnessLib.program fixture_root "tup_string_arg"
val () = print "C7_2_CHECKER_ACCEPT deployment runtime\n"

val tup_string_arg_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^tup_string_arg_program``)
Theorem tup_string_arg_supported:
  supported_program ^tup_string_arg_program
Proof
  ACCEPT_TAC tup_string_arg_supported_eval
QED
