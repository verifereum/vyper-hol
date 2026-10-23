(* Explicitly impure, opt-in validation. No oracle equalities enter HOL proofs. *)
Theory nestedPlaceValidation
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
   "memory_store_witnesses.py", "nested_place_driver.py",
   "nested-places/sources", "nested-places/parity-fixtures.txt",
   "eval/memoryStoreWitnessLib.sml"];
val () = holbuild_extra_outputs ["nested-places/validation.tar.gz"];

fun checked_command command =
  if OS.Process.isSuccess (OS.Process.system command) then ()
  else raise Fail ("nested places validation command failed: " ^ command);
val () = checked_command "python3 nested_place_driver.py prepare";
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);

(* C7.1 is a single-fixture interface probe, not the full C7.2 matrix. *)
val validation_status =
  (memoryStoreWitnessLib.probe "nested-places/oracle" "nested-places/actual"
     "storage_struct_second_field";
   "PROBE_RETURNED: consult per-stage status; no parity claim follows\n")
  handle exn => "PROBE_ERROR " ^ General.exnMessage exn ^ "\n";
val () = memoryStoreWitnessLib.write "nested-places/actual/driver-status.txt"
  validation_status;
val () = print validation_status;
val () = checked_command "python3 nested_place_driver.py archive";
