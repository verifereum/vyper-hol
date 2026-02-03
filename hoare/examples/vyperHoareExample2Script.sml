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

Theorem example_2_thm:
  ∀cx xarg.
    within_int_bound (Unsigned 256) xarg ∧
    within_int_bound (Unsigned 256) (xarg + 20) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧
          valid_lookups cx st ∧
          lookup_immutable cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
          lookup_name cx st "x" = NONE⦄
    example_2_body
    ⦃λst. ∃x. lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) x) ∧ 20 ≤ x ∧ x ≤ 110 ∥ λ_ _. F⦄
Proof
(* Proof sketch using Hoare logic rules:

Assumptions (outside Hoare triple):
  within_int_bound (Unsigned 256) xarg
  within_int_bound (Unsigned 256) (xarg + 20)

Program:
  x := x_arg              -- AnnAssign "x" (Name "x_arg")
  x += 10                 -- AugAssign (NameTarget "x") Add (Literal 10)
  if x > 100 then         -- If (Builtin (Bop Gt) [Name "x"; Literal 100])
    x := 100              --   [Assign (BaseTarget (NameTarget "x")) (Literal 100)]
  else
    x += 10               --   [AugAssign (NameTarget "x") Add (Literal 10)]

Proof outline:

{ st.scopes ≠ [] ∧ valid_lookups cx st ∧
  lookup_immutable cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
  lookup_name cx st "x" = NONE }

1. AnnAssign "x" (Name "x_arg"):
   - Use stmts_spec_ann_assign
   - Evaluate "x_arg" using expr_spec_name with lookup_immutable_implies_lookup_name
   - Creates new variable x with value xarg

{ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
  valid_lookups cx st }

2. AugAssign (NameTarget "x") Add (Literal 10):
   - Use stmts_spec_aug_assign_scoped_var
   - evaluate_binop Add (IntV (Unsigned 256) xarg) (IntV (Unsigned 256) 10)
     = INL (IntV (Unsigned 256) (xarg + 10))   [by within_int_bound assumption]

{ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
  valid_lookups cx st }

3. If (Builtin (Bop Gt) [Name "x"; Literal 100]) then ... else ...:
   - Use stmts_spec_if
   - Evaluate condition using expr_spec_builtin_bop + expr_spec_scoped_var + expr_spec_literal
   - Result is BoolV (xarg + 10 > 100)

   Then branch (xarg + 10 > 100, i.e., condition = BoolV T):
   { lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧ xarg + 10 > 100 }
     x := 100
   { lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 100) }
   - Use stmts_spec_assign_scoped_var with expr_spec_literal
   - 20 ≤ 100 ∧ 100 ≤ 110 holds trivially

   Else branch (xarg + 10 ≤ 100, i.e., condition = BoolV F):
   { lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧ xarg + 10 ≤ 100 }
     x += 10
   { lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 20)) }
   - Use stmts_spec_aug_assign_scoped_var
   - evaluate_binop Add (IntV _ (xarg+10)) (IntV _ 10) = INL (IntV _ (xarg+20))
     [by within_int_bound (xarg + 20) assumption]
   - From xarg + 10 ≤ 100: xarg + 20 ≤ 110
   - From within_int_bound xarg: 0 ≤ xarg, so 20 ≤ xarg + 20

{ ∃x. lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) x) ∧ 20 ≤ x ∧ x ≤ 110 }

*)
  rpt strip_tac >>
  simp[example_2_body_def, example_2_decl_def, example_2_module_def] >>
  (* Statement 1: x := x_arg (AnnAssign) *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)` >>
  conj_tac >-
  ((* AnnAssign proof *)
   irule stmts_spec_ann_assign >> qexists_tac `IntV (Unsigned 256) xarg` >>
   irule expr_spec_consequence >>
   qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
                        lookup_name cx st "x" = NONE`,
                 `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
                        lookup_name cx st "x" = NONE`] >>
   conj_tac >- (simp[] >> rpt strip_tac >> drule_all lookup_immutable_implies_lookup_name >> simp[]) >>
   conj_tac >-
     (simp[] >> rpt strip_tac >-
        metis_tac[lookup_name_none_to_lookup_scoped_var] >-
        metis_tac[scopes_nonempty_after_update] >-
        metis_tac[valid_lookups_preserved_after_update_no_name] >>
        simp[lookup_after_update]) >>
   irule expr_spec_consequence >>
   qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "x" = NONE) ∧
                        lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg)`,
                 `λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "x" = NONE) ∧
                        lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg)`] >>
   simp[] >>
   ACCEPT_TAC (BETA_RULE (ISPECL [
     ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                             lookup_name cx st "x" = NONE``,
     ``cx:evaluation_context``, ``"x_arg":string``, ``IntV (Unsigned 256) xarg``] expr_spec_name))) >>
  (* Statement 2: x += 10 (AugAssign) *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))` >>
  conj_tac >-
  ((* AugAssign proof for x += 10 *)
   irule stmts_spec_consequence >>
   qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)) ∧
                       (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st "x"`,
                 `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))`,
                 `λ_0 _1. F`] >>
   conj_tac >- (simp[] >> metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
   conj_tac >- simp[] >>
   conj_tac >- simp[] >>
   MATCH_MP_TAC (BETA_RULE (ISPECL [
     ``λst:evaluation_state. (st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg))``,
     ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))``,
     ``cx:evaluation_context``, ``"x":string``, ``Add:binop``,
     ``Literal (IntL (Unsigned 256) 10):expr``,
     ``IntV (Unsigned 256) xarg``, ``IntV (Unsigned 256) 10``,
     ``IntV (Unsigned 256) (xarg + 10)``] stmts_spec_aug_assign_scoped_var)) >>
   conj_tac >-
     (simp[evaluate_binop_def, bounded_int_op_def] >>
      gvs[vyperTypeValueTheory.within_int_bound_def] >>
      intLib.ARITH_TAC) >>
   irule expr_spec_consequence >>
   qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)`,
                 `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)`] >>
   conj_tac >- simp[] >>
   conj_tac >-
      (simp[scopes_nonempty_after_update, lookup_after_update] >>
       metis_tac[valid_lookups_preserved_after_update_var_in_scope, lookup_scoped_var_implies_var_in_scope]) >>
   ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 10)``]
     (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                                       lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)``,
              ``ARB:'a``, ``cx:evaluation_context``,
              ``IntL (Unsigned 256) 10``] expr_spec_literal))) >>
  (* Statement 3: if x > 100 then x := 100 else x += 10 *)
  irule stmts_spec_if >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))` >>
  qexists_tac `BoolV (xarg + 10 > 100)` >>
  (* v1 = BoolV T ∨ v1 = BoolV F *)
  conj_tac >- (Cases_on `xarg + 10 > 100` >> simp[]) >>
  (* Condition evaluation: x > 100 *)
  conj_tac >- (
    irule expr_spec_builtin_bop >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))`,
                  `IntV (Unsigned 256) (xarg + 10)`,
                  `IntV (Unsigned 256) 100`] >>
    simp[evaluate_binop_def] >>
    conj_tac >- (
      irule expr_spec_consequence >>
      qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st) ∧ valid_lookups cx st ∧
                          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))`,
                    `λst. (st.scopes ≠ [] ∧ valid_lookups cx st) ∧ valid_lookups cx st ∧
                          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))`] >>
      simp[] >>
      ACCEPT_TAC (BETA_RULE (ISPECL [
        ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st``,
        ``cx:evaluation_context``, ``"x":string``,
        ``IntV (Unsigned 256) (xarg + 10)``] expr_spec_scoped_var))) >>
    ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 100)``]
      (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))``,
               ``ARB:'a``, ``cx:evaluation_context``,
               ``IntL (Unsigned 256) 100``] expr_spec_literal))) >>
  simp[] >>
  (* Else branch: x += 10 (when xarg + 10 ≤ 100) *)
  conj_tac >- (
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
            valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
            ¬(xarg + 10 > 100)`,
      `λst. HD st.scopes = FEMPTY ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 20)) ∧
            ¬(xarg + 10 > 100)`,
      `λv st. F`] >>
    simp[] >>
    conj_tac >- (rpt strip_tac >> gvs[lookup_in_current_scope_hd, lookup_in_tl_scopes]) >>
    conj_tac >- (
      rpt strip_tac >> qexists_tac `xarg + 20` >>
      simp[lookup_in_current_scope_hd, lookup_in_tl_scopes] >>
      gvs[vyperTypeValueTheory.within_int_bound_def] >> intLib.ARITH_TAC) >>
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
             valid_lookups cx (tl_scopes st) ∧
             lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
             ¬(xarg + 10 > 100)) ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧
            var_in_scope st "x"`,
      `λst. HD st.scopes = FEMPTY ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 20)) ∧
            ¬(xarg + 10 > 100)`,
      `λv st. F`] >>
    simp[] >>
    conj_tac >- (
      rpt strip_tac >-
      (irule valid_lookups_tl_scopes_rev >> simp[]) >>
      metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
    MATCH_MP_TAC (BETA_RULE (ISPECL [
      ``λst:evaluation_state. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
                              (tl_scopes st).scopes ≠ [] ∧
                              valid_lookups (cx:evaluation_context) (tl_scopes st) ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                              ¬(xarg + 10 > 100)``,
      ``λst:evaluation_state. HD st.scopes = FEMPTY ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 20)) ∧
                              ¬(xarg + 10 > 100)``,
      ``cx:evaluation_context``, ``"x":string``, ``Add:binop``,
      ``Literal (IntL (Unsigned 256) 10):expr``,
      ``IntV (Unsigned 256) (xarg + 10)``, ``IntV (Unsigned 256) 10``,
      ``IntV (Unsigned 256) (xarg + 20)``] stmts_spec_aug_assign_scoped_var)) >>
    conj_tac >- (
      simp[evaluate_binop_def, bounded_int_op_def] >>
      gvs[vyperTypeValueTheory.within_int_bound_def] >> intLib.ARITH_TAC) >>
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
            valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
            ¬(xarg + 10 > 100)`,
      `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
            valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
            ¬(xarg + 10 > 100)`] >>
    simp[] >>
    conj_tac >- (
      rpt strip_tac >- (
        irule hd_scopes_preserved_after_update_in_tl_scopes >> simp[] >>
        simp[lookup_in_current_scope_hd] >>
        simp[var_in_tl_scopes, lookup_in_current_scope_hd] >>
        metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
      simp[lookup_after_update]) >>
    ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 10)``]
      (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
                  (tl_scopes st).scopes ≠ [] ∧
                  valid_lookups (cx:evaluation_context) (tl_scopes st) ∧
                  lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                  ¬(xarg + 10 > 100)``,
               ``ARB:'a``, ``cx:evaluation_context``,
               ``IntL (Unsigned 256) 10``] expr_spec_literal))) >>
  (* Then branch: x := 100 (when xarg + 10 > 100) *)
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
          valid_lookups cx (tl_scopes st) ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
          xarg + 10 > 100`,
    `λst. HD st.scopes = FEMPTY ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 100)`,
    `λv st. F`] >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[lookup_in_current_scope_hd, lookup_in_tl_scopes]) >>
  conj_tac >- (
    rpt strip_tac >> qexists_tac `100` >>
    simp[lookup_in_current_scope_hd, lookup_in_tl_scopes]) >>
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
           valid_lookups cx (tl_scopes st) ∧
           lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
           xarg + 10 > 100) ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧
          var_in_scope st "x"`,
    `λst. HD st.scopes = FEMPTY ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 100)`,
    `λv st. F`] >>
  simp[] >>
  conj_tac >- (
    rpt strip_tac >-
    (irule valid_lookups_tl_scopes_rev >> simp[]) >>
    metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
  MATCH_MP_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
                            (tl_scopes st).scopes ≠ [] ∧
                            valid_lookups (cx:evaluation_context) (tl_scopes st) ∧
                            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                            xarg + 10 > 100``,
    ``λst:evaluation_state. HD st.scopes = FEMPTY ∧
                            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 100)``,
    ``cx:evaluation_context``, ``"x":string``,
    ``Literal (IntL (Unsigned 256) 100):expr``,
    ``IntV (Unsigned 256) 100``] stmts_spec_assign_scoped_var)) >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
           valid_lookups cx (tl_scopes st) ∧
           lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
           xarg + 10 > 100) ∧ var_in_scope st "x"`,
    `λst. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
           valid_lookups cx (tl_scopes st) ∧
           lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
           xarg + 10 > 100) ∧ var_in_scope st "x"`] >>
  simp[] >>
  conj_tac >- (
    rpt strip_tac >- (
      irule hd_scopes_preserved_after_update_in_tl_scopes >> simp[] >>
      simp[lookup_in_current_scope_hd] >>
      simp[var_in_tl_scopes, lookup_in_current_scope_hd] >>
      metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
    simp[lookup_after_update]) >>
  ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 100)``]
    (ISPECL [``λst:evaluation_state. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
                (tl_scopes st).scopes ≠ [] ∧
                valid_lookups (cx:evaluation_context) (tl_scopes st) ∧
                lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                xarg + 10 > 100) ∧ var_in_scope st "x"``,
             ``ARB:'a``, ``cx:evaluation_context``,
             ``IntL (Unsigned 256) 100``] expr_spec_literal))
QED
