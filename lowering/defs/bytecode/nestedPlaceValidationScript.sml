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
(* Operator-verified existing environment; no installation is performed. *)
val validation_python =
  case OS.Process.getEnv "NESTED_PLACE_PYTHON" of
    SOME path => path
  | NONE => "/home/lukasz/.local/share/uv/tools/vyper/bin/python3";
fun python_command mode = checked_command
  ("'" ^ validation_python ^ "' nested_place_driver.py " ^ mode);
val () = python_command "prepare";
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);

val witnesses = List.filter
  (fn s => s <> "" andalso not (String.isPrefix "#" s))
  (String.tokens (fn c => c = #"\n")
    (memoryStoreWitnessLib.read "nested-places/parity-fixtures.txt"));
fun probe name = let
  val status =
    (memoryStoreWitnessLib.probe "nested-places/oracle" "nested-places/actual" name;
     "PROBE_RETURNED: inspect checker and bytecode statuses\n")
    handle exn => "PROBE_ERROR " ^ General.exnMessage exn ^ "\n"
  val () = memoryStoreWitnessLib.write
    ("nested-places/actual/" ^ name ^ ".status") status
in print (name ^ " " ^ status) end;
val () = List.app probe witnesses;
val () = python_command "archive";
