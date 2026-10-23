(* Source-derived programs and execution contexts for issue #550 witnesses. *)
Theory evalAssignmentOrderFrontend
Ancestors
  vyperInterpreter vyperTypeSystem jsonToVyper jsonConstEval
Libs
  vyperCheckContractFrontendLib finite_mapLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../assignment-order/oracle", "../assignment-order/sources",
   "../assignment-order/fixtures.txt"]
val () = computeLib.upd_compset add_finite_map_compset

fun define_source_fixture name = let
  val path = "../assignment-order/oracle/" ^ name ^ ".json"
  val ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path
  val layout = JSONDecode.decodeFile jsonASTLib.storage_layout path
  val checked = vyperCheckContractFrontendLib.check_contract_result
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = ast, storage_layout = layout}
  val deploy = vyperCheckContractFrontendLib.check_contract_result
    {in_deploy = true, address = ``0w : address``,
     annotated_ast = ast, storage_layout = layout}
  val input = #input checked
  val modules = #modules input
  val layouts = #layouts input
  val lookup = EVAL ``ALOOKUP ^modules NONE``
  val program = optionSyntax.dest_some (rhs (concl lookup))
  val _ = optionSyntax.dest_some (rhs (concl (EVAL
    ``lookup_function NONE "f" External ^program``)))
  fun define suffix tm = let
    val def = new_definition (name ^ suffix ^ "_def",
      mk_eq (mk_var (name ^ suffix, type_of tm), tm))
    val () = computeLib.add_persistent_funs [name ^ suffix ^ "_def"]
    val () = cv_auto_trans def
  in def end
  val _ = define "_source_program" program
  val _ = define "_source_context"
    ``empty_evaluation_context with
      <|sources := [(0w, ^modules)]; layouts := ^layouts|>``
  val _ = save_thm (name ^ "_frontend_checked", #theorem checked)
  val _ = save_thm (name ^ "_frontend_checked_deploy", #theorem deploy)
in () end;

val () = List.app define_source_fixture
  ["c08_storage_arr_assign_computed_rhs",
   "c09_storage_map_assign_computed_rhs", "g6_write_order_side",
   "x04_assign_sideeffect_order", "g19_aug_rhs_modifies_target",
   "x03_assign_elem_from_pop", "s11_storage_map_assign_extcall_rhs",
   "assign_delayed_storage_read", "assign_delayed_popped_read",
   "assign_nested_popped_read", "aug_storage_shrink",
   "aug_memory_shrink", "aug_memory_shrink_append"];

Definition assignment_entry_body_def:
  assignment_entry_body program =
    case lookup_function NONE "f" External program of
    | SOME (_,_,_,_,_,ss) => ss
    | NONE => []
End
val () = cv_auto_trans assignment_entry_body_def;

Definition assignment_empty_state_def:
  assignment_empty_state = empty_state with scopes := [FEMPTY]
End
val () = cv_auto_trans assignment_empty_state_def;
