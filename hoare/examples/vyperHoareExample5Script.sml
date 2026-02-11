Theory vyperHoareExample5

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup

Libs
  jsonASTLib intLib

val example_5_json_path = "example_5.json"

val example_5_jsonast_tm = JSONDecode.decodeFile (JSONDecode.field "ast" json_module) example_5_json_path

val example_5_vyperast_tm = let
  val translate_module_tm = prim_mk_const{Thy="jsonToVyper",Name="translate_module"}
  val app = mk_comb(translate_module_tm, example_5_jsonast_tm)
  val thm = EVAL app
in
  rhs (concl thm)
end

Definition example_5_module_def:
  example_5_module = ^example_5_vyperast_tm
End


Theorem example_5_has_1_toplevel:
  LENGTH example_5_module = 1
Proof
  EVAL_TAC
QED

Definition example_5_decl_def:
  example_5_decl = EL 0 example_5_module
End

Definition example_5_body_def:
  example_5_body = case example_5_decl of
    | FunctionDecl _ _ _ _ _ body => body
    | _ => []
End

Theorem example_5_body_length:
  LENGTH example_5_body = 3
Proof
  EVAL_TAC
QED

Theorem example_5_thm:
  ∀cx n. n ≤ 1000000 ⇒
    ⟦cx⟧
    ⦃λst.
      valid_lookups cx st ∧
      lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
      lookup_name cx st "s" = NONE⦄
    example_5_body
    ⦃λ_. F ∥ λv st. v = IntV (Unsigned 256) (n * (n - 1) / 2)⦄
Proof
  cheat
QED
