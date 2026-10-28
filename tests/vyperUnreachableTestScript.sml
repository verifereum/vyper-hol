Theory vyperUnreachableTest
Ancestors
  jsonToVyper jsonToVyperExpr jsonAST vyperAST vyperTypeContract
Libs
  vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract/unreachable.json"];

Theorem is_unreachable_test:
  is_unreachable (JE_Name "UNREACHABLE" tc src ty) /\
  ~is_unreachable (JE_Name "reason" tc src ty) /\
  ~is_unreachable (JE_Str n "UNREACHABLE")
Proof
  simp[is_unreachable_def]
QED

(* The checker accepts both statements, and the translation carries the
   unreachable reasons rather than a name "UNREACHABLE". *)
val fixture = vyperCheckContractFrontendLib.check_contract_result_legacy
  {in_deploy = false, address = ``0w : address``,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     "fixtures/check_contract/unreachable.json",
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     "fixtures/check_contract/unreachable.json"};
fun occurs tm = not (null (find_terms (aconv tm) (#modules fixture)));
val () = app (fn (label, tm) =>
  if occurs tm then () else raise Fail ("unreachable fixture: missing " ^ label))
  [("assert", ``AssertUnreachable``), ("raise", ``Raise RaiseUnreachable``)];
val () = if null (find_terms (fn tm => can stringSyntax.fromHOLstring tm andalso
                                       stringSyntax.fromHOLstring tm = "UNREACHABLE")
                             (#modules fixture)) then ()
  else raise Fail "unreachable fixture: the name UNREACHABLE survived translation";
