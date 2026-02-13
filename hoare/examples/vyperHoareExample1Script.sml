Theory vyperHoareExample1

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup

Libs
  jsonASTLib intLib

(* Load the JSON and parse to vyperAST *)
val example_1_json_path = "example_1.json"

(* The decoder for single contract ast output: {"contract_name": ..., "ast": ...} *)
val example_1_jsonast_tm = JSONDecode.decodeFile (JSONDecode.field "ast" json_module) example_1_json_path

val example_1_vyperast_tm = let
  val translate_module_tm = prim_mk_const{Thy="jsonToVyper",Name="translate_module"}
  val app = mk_comb(translate_module_tm, example_1_jsonast_tm)
  val thm = EVAL app
in
  rhs (concl thm)
end

Definition example_1_module_def:
  example_1_module = ^example_1_vyperast_tm
End


Theorem example_1_has_1_toplevel:
  LENGTH example_1_module = 1
Proof
  EVAL_TAC
QED

Definition example_1_decl_def:
  example_1_decl = EL 0 example_1_module
End

Definition example_1_body_def:
  example_1_body = case example_1_decl of
    | FunctionDecl _ _ _ _ _ _ body => body
    | _ => []
End

Theorem example_1_body_length:
  LENGTH example_1_body = 2
Proof
  EVAL_TAC
QED

Definition sum_scoped_vars_def:
  sum_scoped_vars [] st = 0 ∧
  sum_scoped_vars (id::ids) st =
    let rest = sum_scoped_vars ids st in
    case lookup_scoped_var st id of
      NONE => rest
    | SOME v =>
        case dest_NumV v of
          NONE => rest
        | SOME n => n + rest
End

Theorem sum_scoped_vars_xy_20:
  ∀st. lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
       lookup_scoped_var st "y" = SOME (IntV (Signed 128) 10) ⇒
       sum_scoped_vars ["x"; "y"] st = 20
Proof
  rw[sum_scoped_vars_def, lookup_scoped_var_def, LET_THM] >>
  simp[dest_NumV_def]
QED

Theorem example_1_sum_20:
  ∀cx. ⟦cx⟧ ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE⦄
       example_1_body
       ⦃(λst. sum_scoped_vars ["x"; "y"] st = 20) ∥ (λv st. F)⦄
Proof
  rpt strip_tac >>
  simp[example_1_body_def, example_1_decl_def, example_1_module_def] >>
  (* Define intermediate invariant P1 after first assignment *)
  qabbrev_tac `P1 = λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                         lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
                         lookup_name cx st "y" = NONE` >>
  (* Sequence rule *)
  irule stmts_spec_cons >>
  qexists_tac `P1` >>
  conj_tac
  (* ===== First statement: AnnAssign "x" _ (Literal 10) ===== *)
  >- (irule stmts_spec_ann_assign >>
      irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE`,
        `λtv st. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                 lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE ∧
                 tv = Value (IntV (Signed 128) 10)`
      ] >>
      rpt conj_tac >> simp[Abbr `P1`]
      (* Goal 1: postcondition implication - 5 subgoals after rpt strip_tac *)
      >- (rpt strip_tac >|
          [metis_tac[lookup_name_none_to_lookup_scoped_var],
           metis_tac[scopes_nonempty_after_update],
           metis_tac[valid_lookups_preserved_after_update_no_name],
           simp[lookup_after_update],
           `"x" ≠ "y"` by EVAL_TAC >> simp[lookup_name_preserved_after_update]])
      (* Goal 2: expr_spec for Literal *)
      >- (irule expr_spec_consequence >>
          qexistsl_tac [
            `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                  lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE`,
            `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
                      lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE) ∧
                     tv = Value (evaluate_literal (IntL (Signed 128) 10))`
          ] >>
          simp[expr_spec_literal, evaluate_literal_def]))
  (* ===== Second statement: AnnAssign "y" _ (Name "x") ===== *)
  >- (irule stmts_spec_ann_assign >>
      irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. (st.scopes ≠ [] ∧ lookup_name cx st "y" = NONE) ∧
              valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10)`,
        `λtv st. (st.scopes ≠ [] ∧ lookup_name cx st "y" = NONE) ∧
                 valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
                 tv = Value (IntV (Signed 128) 10)`
      ] >>
      rpt conj_tac >> simp[Abbr `P1`]
      (* Goal 1: postcondition implication - 2 subgoals after rpt strip_tac *)
      >- (rpt strip_tac >|
          [metis_tac[lookup_name_none_to_lookup_scoped_var],
           irule sum_scoped_vars_xy_20 >>
           simp[lookup_after_update] >>
           `"y" ≠ "x"` by EVAL_TAC >>
           drule_all lookup_scoped_var_preserved_after_update >> simp[]])
      (* Goal 2: expr_spec for Name "x" *)
      >- (ACCEPT_TAC (SIMP_RULE std_ss []
            (Q.SPECL [`λst. st.scopes ≠ [] ∧ lookup_name cx st "y" = NONE`,
                      `cx`, `"x"`, `IntV (Signed 128) 10`] expr_spec_scoped_var_eq))))
QED
