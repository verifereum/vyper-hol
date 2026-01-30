Theory vyperHoareExample3

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup

Libs
  jsonASTLib intLib

(* Load the JSON and parse to vyperAST *)
val example_3_json_path = "example_3.json"

(* The decoder for single contract ast output: {"contract_name": ..., "ast": ...} *)
val example_3_jsonast_tm = JSONDecode.decodeFile (JSONDecode.field "ast" json_module) example_3_json_path

val example_3_vyperast_tm = let
  val translate_module_tm = prim_mk_const{Thy="jsonToVyper",Name="translate_module"}
  val app = mk_comb(translate_module_tm, example_3_jsonast_tm)
  val thm = EVAL app
in
  rhs (concl thm)
end

Definition example_3_module_def:
  example_3_module = ^example_3_vyperast_tm
End


Theorem example_3_has_1_toplevel:
  LENGTH example_3_module = 1
Proof
  EVAL_TAC
QED

Definition example_3_decl_def:
  example_3_decl = EL 0 example_3_module
End

Definition example_3_body_def:
  example_3_body = case example_3_decl of
    | FunctionDecl _ _ _ _ _ body => body
    | _ => []
End

Theorem example_3_body_length:
  LENGTH example_3_body = 6
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
if x > 20 then
  { x > 20 ∧ 20 ≤ x ∧ x ≤ 110 }
  { x > 20 ∧ x ≤ 110 }
  return x
  { F | λv. v > 20 ∧ v ≤ 110 }
  { x = 20 | λv. v > 20 ∧ v ≤ 110 }
else
  { x ≤ 20 ∧ 20 ≤ x }
  pass
  { x = 20 | λv. v > 20 ∧ v ≤ 110 }
{ x = 20 | λv. v > 20 ∧ v ≤ 110 }
y := x + 20
{ y = 40 | λv. v > 20 ∧ v ≤ 110 }
return y
{ F | λv. v > 20 ∧ v ≤ 110 }

*)
