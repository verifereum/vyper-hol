(* Focused rerun of the two residual mismatches and corrected TASK sources.
   This target retains checker failures and parity verdicts as observations. *)
Theory nestedPlaceDiagnostic
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
val () = holbuild_extra_outputs ["nested-places/diagnostic.tar.gz"];
val python = case OS.Process.getEnv "NESTED_PLACE_PYTHON" of
  SOME path => path | NONE => "/home/lukasz/.local/share/uv/tools/vyper/bin/python3";
fun command mode = if OS.Process.isSuccess
  (OS.Process.system ("'" ^ python ^ "' nested_place_driver.py " ^ mode)) then ()
  else raise Fail ("nested place diagnostic command failed: " ^ mode);
val () = command "matrix-prepare";
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);
val names = ["arr_struct_subscript_attr_b", "s20_nested_map_read_key_order",
  "g5_hm_nested_aug", "s23_nested_map_read_call_inner_key",
  "s24_nested_map_read_call_outer_key", "g7_aug_transient_arr",
  "b05_nested_2d_elem", "b06_struct_arr_field_elem", "g5_hm_val_array"];
fun probe name = let
  val status =
    (memoryStoreWitnessLib.probe "nested-places/oracle" "nested-places/actual" name;
     "PROBE_RETURNED\n")
    handle exn => "PROBE_ERROR " ^ General.exnMessage exn ^ "\n"
  val () = memoryStoreWitnessLib.write ("nested-places/actual/" ^ name ^ ".status") status
in print (name ^ " " ^ status) end;
val () = List.app probe names;
val () = memoryStoreWitnessLib.write "nested-places/diagnostic.txt"
  (String.concat (map (fn name => name ^ "\n") names));
val () = command "diagnostic-archive";
