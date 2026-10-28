(* Strict regression for the side-effecting nested-key witness. *)
Theory nestedPlaceS20
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  byte option alist integer_word
Libs
  vyperCheckContractFrontendLib jsonASTLib finite_mapLib wordsLib
  evalCompilerBytecodeLib memoryStoreWitnessLib

fun holbuild_extra_deps (_ : string list) = ();
fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_deps
  ["../../../VYPER_PIN", "../../../tests/sanitize_check_contract_json.py",
   "memory_store_witnesses.py", "nested_place_driver.py", "nested_place_cases.py",
   "nested-places/sources"];
val () = holbuild_extra_outputs
  ["nested-places/s20_nested_map_read_key_order-validation.tar.gz"];
val python = case OS.Process.getEnv "NESTED_PLACE_PYTHON" of
  SOME path => path | NONE => "/home/lukasz/.local/share/uv/tools/vyper/bin/python3";
fun command args = if OS.Process.isSuccess
  (OS.Process.system ("'" ^ python ^ "' nested_place_driver.py " ^ args)) then ()
  else raise Fail ("nested place witness command failed: " ^ args);
val () = command "matrix-prepare";
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);
val () = memoryStoreWitnessLib.require_match "nested-places/oracle"
  "nested-places/actual" "s20_nested_map_read_key_order";
val () = command "witness-archive --case s20_nested_map_read_key_order";
