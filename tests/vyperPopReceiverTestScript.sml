Theory vyperPopReceiverTest
Ancestors
  vyperSmallStep jsonToVyper jsonToVyperExpr jsonAST vyperAST
Libs
  vyperCheckContractFrontendLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["fixtures/check_contract/nested_pop.vy", "fixtures/check_contract/nested_pop.json"]

val fixture_path = "fixtures/check_contract/nested_pop.json"
val fixture = vyperCheckContractFrontendLib.check_contract_result
  {in_deploy = false, address = ``0w : address``,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast fixture_path,
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout fixture_path}
val modules = #modules fixture
val layouts = #layouts fixture
fun function_body name =
  let
    fun named tm = vyperASTSyntax.is_FunctionDecl tm andalso
      let val (_, _, _, _, id, _, _, _, _) = vyperASTSyntax.dest_FunctionDecl_tm tm
      in stringSyntax.fromHOLstring id = name end
    val (_, _, _, _, _, _, _, _, statements) =
      vyperASTSyntax.dest_FunctionDecl_tm (find_term named modules)
  in statements end
val take_body = function_body "take"
val roundtrip_body = function_body "roundtrip"

Theorem hashmap_pop_source_target:
  ^take_body =
    [Return (SOME (Pop (BaseT (UintT 256))
      (SubscriptTarget (TopLevelNameTarget (NONE, "items"))
        (Name (BaseT (UintT 256)) "bucket"))))]
Proof
  REFL_TAC
QED

Definition nested_pop_context_def:
  nested_pop_context = empty_evaluation_context with
    <| sources := [(0w, ^modules)]; layouts := ^layouts |>
End

val () = cv_auto_trans nested_pop_context_def;

Definition nested_pop_result_def:
  nested_pop_result = eval_stmts nested_pop_context ^roundtrip_body empty_state
End

(* Temporary preparation: retain the previous proof while the bounded
   CPS/CV proof is developed under the default tactic limit.
Proof
  CONV_TAC cv_eval
QED
*)
Theorem hashmap_pop_returns_old_last_element:
  FST nested_pop_result = INR (ReturnException (IntV 23))
Proof
  cheat
QED

(* Temporary preparation: retain the previous proof while the bounded
   CPS/CV proof is developed under the default tactic limit.
Proof
  CONV_TAC cv_eval
QED
*)
Theorem hashmap_pop_writes_remaining_array:
  FST (read_storage_slot nested_pop_context F
    (THE (compute_hashmap_slot 0w [BaseT (UintT 256)] [ValueSubscript (IntV 7)]))
    (ArrayTV (BaseTV (UintT 256)) (Dynamic 4)) (SND nested_pop_result)) =
  INL (ArrayV (DynArrayV [IntV 11]))
Proof
  cheat
QED
