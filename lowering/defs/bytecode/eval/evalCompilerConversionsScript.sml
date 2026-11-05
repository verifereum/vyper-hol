(* Independent conversion parity and checker-domain witnesses (#548). *)
Theory evalCompilerConversions
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../conversions"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../conversions/oracle"

val bool_to_i8 = memoryStoreWitnessLib.evaluate fixture_root "bool_to_i8"
Theorem bool_to_i8_matches_python_oracle:
  ^(#term bool_to_i8) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "bool_to_i8")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation bool_to_i8))) >> EVAL_TAC
QED

val lit_int_to_addr = memoryStoreWitnessLib.evaluate fixture_root "lit_int_to_addr"
Theorem lit_int_to_addr_matches_python_oracle:
  ^(#term lit_int_to_addr) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "lit_int_to_addr")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation lit_int_to_addr))) >> EVAL_TAC
QED

val flag_to_b32 = memoryStoreWitnessLib.evaluate fixture_root "flag_to_b32"
Theorem flag_to_b32_matches_python_oracle:
  ^(#term flag_to_b32) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "flag_to_b32")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation flag_to_b32))) >> EVAL_TAC
QED

val u256_to_flag = memoryStoreWitnessLib.evaluate fixture_root "u256_to_flag"
Theorem u256_to_flag_matches_python_oracle:
  ^(#term u256_to_flag) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "u256_to_flag")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation u256_to_flag))) >> EVAL_TAC
QED

val u160_to_b20 = memoryStoreWitnessLib.evaluate fixture_root "u160_to_b20"
Theorem u160_to_b20_matches_python_oracle:
  ^(#term u160_to_b20) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "u160_to_b20")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation u160_to_b20))) >> EVAL_TAC
QED

val b4_to_i256 = memoryStoreWitnessLib.evaluate fixture_root "b4_to_i256"
Theorem b4_to_i256_matches_python_oracle:
  ^(#term b4_to_i256) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "b4_to_i256")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation b4_to_i256))) >> EVAL_TAC
QED

(* Check the actual exported ASTs, including Vyper-invalid conversions whose
   HOL lowering and source semantics agree and therefore stay in the domain. *)
fun check_conversion_in dir expected name = let
  val path = "../conversions/" ^ dir ^ "/" ^ name ^ ".json"
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  fun check in_deploy = let
    val term = vyperCheckContractLib.mk_check_contract
      {in_deploy = in_deploy, address = #address input,
       modules = #modules input, layouts = #layouts input}
    val result = rhs (concl (vyperCheckContractLib.check_contract_conv term))
    val matches = if expected then optionSyntax.is_some result
                  else optionSyntax.is_none result
  in if matches then ()
     else raise Fail (name ^ ": unexpected checker result in deployment mode " ^
                      Bool.toString in_deploy ^ ": " ^ term_to_string result)
  end
in List.app check [false, true] end

val () = List.app (check_conversion_in "checker-oracle" true)
  ["lit_300_to_u8", "lit_neg_to_u256", "lit_bys_narrow"]
(* The pinned Vyper's type checker rejects these; their ASTs come from the
   last pin that accepted them (see ../conversions/README.md). *)
val () = List.app (check_conversion_in "typecheck-rejected" false)
  ["u256_to_b4", "bys33_to_bool", "bys64_to_u256", "bys8_to_b4",
   "str8_to_b4", "u256_to_bys16", "b4_to_bys2",
   "b4_to_bys", "b4_to_str", "u256_to_bys"]
val () = List.app (check_conversion_in "typecheck-rejected" true)
  ["i8_to_addr", "i256_to_addr"]
