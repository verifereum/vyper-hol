(* Checker acceptance and supported_program for the required issue #551
   fixtures, and exact pinned-Python parity for those whose bytes still match. *)
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

fun check_supported name = let
  val root = "../abi-codegen/oracle"
  val tops = memoryStoreWitnessLib.program root name
  val () = print ("ABI_CODEGEN_CHECKER_ACCEPT " ^ name ^ " deployment runtime\n")
  val supported = EVAL ``supported_program ^tops``
  val _ = save_thm (name ^ "_supported_status", supported)
in tops end

fun check_parity name tops = let
  val root = "../abi-codegen/oracle"
  val term = memoryStoreWitnessLib.compile_term tops
  val evaluation = EVAL term
  val expected = memoryStoreWitnessLib.oracle root name
  val parity = prove (``^term = SOME ^expected``,
    CONV_TAC (LAND_CONV (K evaluation)) >> EVAL_TAC)
  val _ = save_thm (name ^ "_matches_python_oracle", parity)
in () end

(* These fixtures' Python bytecode changed at the v0.5.0b1 pin
   (vyperlang/vyper#5127); their exact-bytes comparison returns with the ports
   listed in ../pending-5127-port.md. *)
val () = List.app (ignore o check_supported)
  ["enc_multi", "enc_ensT_bytes"]

val () = List.app (fn name => check_parity name (check_supported name))
  ["arr_string_arg", "st_string_field_arg", "arr_dyn_of_fixed",
   "arr_struct_noclamp", "arr_string_ret", "dec_bytes_unwrapT",
   "dec_uint_unwrapT", "flag256_arg", "flag256_array_arg"]
