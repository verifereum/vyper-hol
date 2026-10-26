(* Exact pinned-Python parity for the remaining required issue #551 fixtures.
   Checker acceptance and supported_program are recorded separately. *)
Theory evalCompilerAbiCodegen
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

fun kernel_closed name th =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then
      print ("ABI_CODEGEN_KERNEL_CLOSED " ^ name ^ "\n")
    else raise Fail ("admitted ABI codegen theorem: " ^ name)
  end

fun check_fixture name = let
  val root = "../abi-codegen/oracle"
  val tops = memoryStoreWitnessLib.program root name
  val () = print ("ABI_CODEGEN_CHECKER_ACCEPT " ^ name ^ " deployment runtime\n")
  val supported = EVAL ``supported_program ^tops``
  val () = kernel_closed (name ^ "_supported_status") supported
  val _ = save_thm (name ^ "_supported_status", supported)
  val term = memoryStoreWitnessLib.compile_term tops
  val evaluation = EVAL term
  val expected = memoryStoreWitnessLib.oracle root name
  val parity = prove (``^term = SOME ^expected``,
    CONV_TAC (LAND_CONV (K evaluation)) >> EVAL_TAC)
  val () = kernel_closed (name ^ "_matches_python_oracle") parity
  val _ = save_thm (name ^ "_matches_python_oracle", parity)
in () end

val () = List.app check_fixture
  ["arr_string_arg", "st_string_field_arg", "arr_dyn_of_fixed",
   "arr_struct_noclamp", "arr_string_ret", "enc_multi", "enc_ensT_bytes",
   "dec_bytes_unwrapT", "dec_uint_unwrapT", "flag256_arg", "flag256_array_arg"]
