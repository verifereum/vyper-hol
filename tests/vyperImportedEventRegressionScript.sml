Theory vyperImportedEventRegression
Ancestors jsonToVyper vyperTypeContract alist
Libs vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract/events"]

(* The endpoint checks [(NONE,tops)]. Resolve each real imported-event AST
   through the frontend, then check exactly that single-module projection. *)
fun imported_event_regression stem = let
  val path = "fixtures/check_contract/events/" ^ stem ^ ".json"
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  val modules = #modules input
  val tops = optionSyntax.dest_some (rhs (concl (EVAL ``ALOOKUP ^modules NONE``)))
  fun check deploy = let
    val dep = if deploy then ``T`` else ``F``
    val layouts = #layouts input
    val th = vyperCheckContractLib.check_contract_conv
      ``check_contract ^dep ^layouts 0w [(NONE,^tops)]``
    val _ = if optionSyntax.is_none (rhs (concl th)) then ()
      else raise Fail (stem ^ ": imported event accepted on single-module input")
  in save_thm (stem ^ (if deploy then "_deploy_rejected" else "_runtime_rejected"), th)
  end
in
  (check false; check true; ())
end

val () = List.app imported_event_regression
  ["event_import_ierc20", "event_import_user_module", "event_import_approval"]
