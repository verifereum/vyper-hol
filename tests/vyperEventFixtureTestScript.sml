Theory vyperEventFixtureTest
Ancestors jsonToVyper vyperTypeContract alist
Libs vyperCheckContractFrontendLib jsonASTLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract/events"]

(* Real pinned-compiler event ASTs, resolved through the frontend. *)
fun fixture_input stem = let
  val path = "fixtures/check_contract/events/" ^ stem ^ ".json"
in
  vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
end

fun mode_name deploy = if deploy then "_deploy" else "_runtime"

(* The whole program, with its imported modules, checks in both modes. *)
fun fixture_accepted stem = let
  val input = fixture_input stem
  fun check deploy = save_thm (stem ^ mode_name deploy ^ "_checked",
    vyperCheckContractLib.check_contract
      {in_deploy = deploy, address = #address input,
       modules = #modules input, layouts = #layouts input})
in
  (check false; check true; ())
end

(* An imported event is declared only in its module, so the main module
   alone, [(NONE,tops)], must be rejected. *)
fun imported_event_needs_module stem = let
  val input = fixture_input stem
  val modules = #modules input
  val tops = optionSyntax.dest_some (rhs (concl (EVAL ``ALOOKUP ^modules NONE``)))
  fun check deploy = let
    val dep = if deploy then ``T`` else ``F``
    val layouts = #layouts input
    val th = vyperCheckContractLib.check_contract_conv
      ``check_contract ^dep ^layouts 0w [(NONE,^tops)]``
    val _ = if optionSyntax.is_none (rhs (concl th)) then ()
      else raise Fail (stem ^ ": imported event accepted on single-module input")
  in save_thm (stem ^ mode_name deploy ^ "_single_module_rejected", th)
  end
in
  (check false; check true; ())
end

val imported = ["event_import_ierc20", "event_import_user_module", "event_import_approval"]

val () = List.app fixture_accepted
  (imported @
   ["event_bytes20_indexed", "event_storage_bytes20_indexed",
    "event_forward_struct", "event_widen_dynarray", "event_widen_nested_string",
    "event_widen_tuple", "event_widen_fixed_dynamic"])

val () = List.app imported_event_needs_module imported
