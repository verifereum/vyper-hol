Theory vyperHoareExample4

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup

Libs
  jsonASTLib intLib

val example_4_json_path = "example_4.json"

val example_4_jsonast_tm = JSONDecode.decodeFile (JSONDecode.field "ast" json_module) example_4_json_path

val example_4_vyperast_tm = let
  val translate_module_tm = prim_mk_const{Thy="jsonToVyper",Name="translate_module"}
  val app = mk_comb(translate_module_tm, example_4_jsonast_tm)
  val thm = EVAL app
in
  rhs (concl thm)
end

Definition example_4_module_def:
  example_4_module = ^example_4_vyperast_tm
End


Theorem example_4_has_1_toplevel:
  LENGTH example_4_module = 1
Proof
  EVAL_TAC
QED

Definition example_4_decl_def:
  example_4_decl = EL 0 example_4_module
End

Definition example_4_body_def:
  example_4_body = case example_4_decl of
    | FunctionDecl _ _ _ _ _ _ body => body
    | _ => []
End

Theorem example_4_body_length:
  LENGTH example_4_body = 4
Proof
  EVAL_TAC
QED

Theorem example_4_thm:
  ∀cx x.
    within_int_bound (Unsigned 256) x ∧
    IS_SOME (get_self_code cx) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧
          valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧
          lookup_name cx st "y" = NONE⦄
    example_4_body
    ⦃λst. F ∥ λv st. ∃n. v = IntV (Signed 128) n ∧ 17 ≤ n ∧ n ≤ 19⦄
Proof
  cheat
QED
