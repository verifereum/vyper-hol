Theory eventFixturePrograms
Ancestors compileVyper vyperTypeContract jsonToVyper
Libs vyperCheckContractFrontendLib jsonASTLib

(* Decode the independent pinned-Python ASTs, then certify both checker modes.
   The compiler parity theories consume these exact frontend-produced programs. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract/events"]

fun event_fixture stem = let
  val path = "fixtures/check_contract/events/" ^ stem ^ ".json"
  val ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path
  val layout = JSONDecode.decodeFile jsonASTLib.storage_layout path
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = ast, storage_layout = layout}
  fun check deploy = let
    val th = vyperCheckContractLib.check_contract
      {in_deploy = deploy, address = #address input,
       modules = #modules input, layouts = #layouts input}
  in save_thm (stem ^ (if deploy then "_deploy_checked" else "_runtime_checked"), th)
  end
  val _ = check false
  val _ = check true
  val modules = #modules input
  val tops = optionSyntax.dest_some (rhs (concl (EVAL ``ALOOKUP ^modules NONE``)))
in
  new_definition (stem ^ "_program_def", mk_eq (mk_var (stem ^ "_program", type_of tops), tops))
end

val event_bytes20_indexed_program_def = event_fixture "event_bytes20_indexed"
val event_storage_bytes20_indexed_program_def = event_fixture "event_storage_bytes20_indexed"
val event_widen_dynarray_program_def = event_fixture "event_widen_dynarray"
val event_widen_nested_string_program_def = event_fixture "event_widen_nested_string"
val event_widen_tuple_program_def = event_fixture "event_widen_tuple"
val event_widen_fixed_dynamic_program_def = event_fixture "event_widen_fixed_dynamic"
val event_forward_struct_program_def = event_fixture "event_forward_struct"
