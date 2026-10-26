(* C7.2: checked frontend and exact independent pinned-Python bytecode parity. *)
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

Theorem tup_string_arg_supported:
  supported_program ^tup_string_arg_program
Proof
  EVAL_TAC
QED

val tup_string_arg_term = memoryStoreWitnessLib.compile_term tup_string_arg_program
val tup_string_arg_evaluation = EVAL tup_string_arg_term

Theorem tup_string_arg_matches_python_oracle:
  ^tup_string_arg_term =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "tup_string_arg")
Proof
  CONV_TAC (LAND_CONV (K tup_string_arg_evaluation)) >> EVAL_TAC
QED

val () = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then
      print ("C7_2_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
    else raise Fail ("admitted C7.2 theorem: " ^ name)
  end)
  [("tup_string_arg_supported", tup_string_arg_supported),
   ("tup_string_arg_matches_python_oracle", tup_string_arg_matches_python_oracle)]
