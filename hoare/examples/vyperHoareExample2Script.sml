Theory vyperHoareExample2

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup

Libs
  jsonASTLib intLib

val example_2_json_path = "example_2.json"

val example_2_jsonast_tm = JSONDecode.decodeFile (JSONDecode.field "ast" json_module) example_2_json_path

val example_2_vyperast_tm = let
  val translate_module_tm = prim_mk_const{Thy="jsonToVyper",Name="translate_module"}
  val app = mk_comb(translate_module_tm, example_2_jsonast_tm)
  val thm = EVAL app
in
  rhs (concl thm)
end

Definition example_2_module_def:
  example_2_module = ^example_2_vyperast_tm
End


Theorem example_2_has_1_toplevel:
  LENGTH example_2_module = 1
Proof
  EVAL_TAC
QED

Definition example_2_decl_def:
  example_2_decl = EL 0 example_2_module
End

Definition example_2_body_def:
  example_2_body = case example_2_decl of
    | FunctionDecl _ _ _ _ _ body => body
    | _ => []
End

Theorem example_2_body_length:
  LENGTH example_2_body = 3
Proof
  EVAL_TAC
QED

(* Proof sketch:

x := x_arg
{ 0 ≤ x }
x := x + 10
{ 10 ≤ x }
if x > 100 then
  { x > 100 ∧ 10 ≤ x }
  { T }
  x := 100
  { x = 100 }
  { 20 ≤ x ∧ x ≤ 110 }
else
  { x ≤ 100 ∧ 10 ≤ x }
  x := x + 10
  { 20 ≤ x ∧ x ≤ 110 }
{ 20 ≤ x ∧ x ≤ 110 }

*)
