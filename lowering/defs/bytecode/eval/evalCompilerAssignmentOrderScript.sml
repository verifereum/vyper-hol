(* Exact independent Vyper bytecode checks for assignment evaluation order. *)
Theory evalCompilerAssignmentOrder
Ancestors
  evalAssignmentOrderInputs compileVyper concretizeMemLocDefs
  alist byte integer_word option
Libs
  evalCompilerBytecodeLib vyperCheckContractFrontendLib
  finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../assignment-order/oracle", "../assignment-order/sources",
   "../assignment-order/fixtures.txt"]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

(* Tie each hand-written compiler input to the exported source AST/layout,
   and run the contract checker on that independent frontend input. *)
fun check_assignment_source name program = let
  val path = "../assignment-order/oracle/" ^ name ^ ".json"
  val annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path
  val storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path
  val checked = vyperCheckContractFrontendLib.check_contract_result
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = annotated_ast, storage_layout = storage_layout}
  val deploy = vyperCheckContractFrontendLib.check_contract_result
    {in_deploy = true, address = ``0w : address``,
     annotated_ast = annotated_ast, storage_layout = storage_layout}
  val modules = #modules (#input checked)
  val translated = EVAL ``ALOOKUP ^modules NONE = SOME ^program``
  val _ = save_thm (name ^ "_source_checked_runtime", #theorem checked)
  val _ = save_thm (name ^ "_source_checked_deploy", #theorem deploy)
in
  save_thm (name ^ "_source_translation", EQT_ELIM translated)
end;

val _ = check_assignment_source "c08_storage_arr_assign_computed_rhs"
  ``c08_storage_arr_assign_computed_rhs_program``;
val _ = check_assignment_source "c09_storage_map_assign_computed_rhs"
  ``c09_storage_map_assign_computed_rhs_program``;
val _ = check_assignment_source "g6_write_order_side"
  ``g6_write_order_side_program``;

Theorem c08_storage_arr_assign_computed_rhs_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    c08_storage_arr_assign_computed_rhs_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../assignment-order/oracle/c08_storage_arr_assign_computed_rhs.hex")
Proof
  EVAL_TAC
QED

Theorem c09_storage_map_assign_computed_rhs_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    c09_storage_map_assign_computed_rhs_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../assignment-order/oracle/c09_storage_map_assign_computed_rhs.hex")
Proof
  EVAL_TAC
QED

Theorem g6_write_order_side_matches_python:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    g6_write_order_side_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes_from
      "../assignment-order/oracle/g6_write_order_side.hex")
Proof
  EVAL_TAC
QED
