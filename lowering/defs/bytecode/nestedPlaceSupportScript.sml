(* Check the actual TASK sources at the supported_program boundary. Each
   verdict is a kernel theorem; unrelated feature guards remain explicit. *)
Theory nestedPlaceSupport
Ancestors supportedProgram
Libs memoryStoreWitnessLib

fun holbuild_extra_deps (_ : string list) = ();
fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_deps
  ["../../../VYPER_PIN", "../../../tests/sanitize_check_contract_json.py",
   "memory_store_witnesses.py", "nested_place_driver.py", "nested_place_cases.py",
   "nested-places/sources"];
val () = holbuild_extra_outputs ["nested-places/support.tsv"];
val python = case OS.Process.getEnv "NESTED_PLACE_PYTHON" of
  SOME path => path | NONE => "/home/lukasz/.local/share/uv/tools/vyper/bin/python3";
val () = if OS.Process.isSuccess
  (OS.Process.system ("'" ^ python ^ "' nested_place_driver.py matrix-prepare"))
  then () else raise Fail "nested-place support preparation failed";

val exclusions =
  [("f32_for_storage_struct_field_arr", "#559: aggregate iteration"),
   ("f38_for_storage_struct_field_arr_set", "#559: aggregate iteration"),
   ("g2_a_dyn_nested", "#559/#560: nested Append and copy"),
   ("g2_a_dyn_struct", "#559: aggregate Append"),
   ("g3_st_dyn_field", "#559: attribute Append"),
   ("s16_storage_map_of_dynarray_elem", "#559: subscript Append"),
   ("g3_st_string_field", "storage bytelike values"),
   ("g7_struct_bytes_field_read", "storage bytelike values"),
   ("g3_st_subword", "storage subword decoding"),
   ("g4_t_u8", "transient subword decoding"),
   ("g5_hm_val_u8", "map subword decoding"),
   ("m10_imm_nested_array", "#563: immutable aggregates"),
   ("p57_int_struct_local_return", "#545: internal struct returns"),
   ("tup_nested_subscript", "#571: nested tuple construction")];
val names = String.tokens (fn ch => ch = #"\n")
  (memoryStoreWitnessLib.read "nested-places/matrix.txt");
fun check name = let
  val () = print ("SUPPORT_CHECK " ^ name ^ "\n")
  val tops = memoryStoreWitnessLib.program "nested-places/oracle" name
  val equation = EVAL ``supported_program ^tops``
  val exclusion = List.find (fn (stem,_) => stem = name) exclusions
  val () = if (isSome exclusion) = aconv (rhs(concl equation)) F then ()
    else print ("SUPPORT_UNEXPECTED " ^ name ^ " SOURCE " ^ term_to_string tops ^ "\n")
  val (fact,verdict) = case exclusion of
      NONE => (EQT_ELIM equation,"SUPPORTED")
    | SOME (_,reason) => (EQF_ELIM equation,"DEFERRED " ^ reason)
  val (oracles,axioms) = Tag.dest_tag (Thm.tag fact)
  val () = if null (Thm.hyp fact) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("admitted support verdict: " ^ name)
  val _ = save_thm ("support_" ^ name,fact)
  val row = name ^ "\t" ^ verdict ^ "\n"
  val () = print row
in row end;
val rows = map check names;
val () = memoryStoreWitnessLib.write "nested-places/support.tsv" (String.concat rows);
