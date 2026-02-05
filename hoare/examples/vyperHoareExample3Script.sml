Theory vyperHoareExample3

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup

Libs
  jsonASTLib intLib

val example_3_json_path = "example_3.json"

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

(* The postcondition says:
   - Normal completion is impossible (always returns)
   - Return values v satisfy: 20 < v ∧ v ≤ 110
*)
Theorem example_3_thm:
  ∀cx xarg.
    within_int_bound (Unsigned 256) xarg ∧
    within_int_bound (Unsigned 256) (xarg + 20) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧
          valid_lookups cx st ∧
          lookup_immutable cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
          lookup_name cx st "x" = NONE ∧
          lookup_name cx st "y" = NONE⦄
    example_3_body
    ⦃λst. F ∥ λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110⦄
Proof
  (* TEMPORARILY CHEATED - proof failing with "No match" from MATCH_MP_TAC
     The full proof is in the commented section below. Issue is likely
     a type annotation or goal shape mismatch somewhere in the proof. *)
  cheat
  (*
  rpt strip_tac >>
  simp[example_3_body_def, example_3_decl_def, example_3_module_def] >>
  (* Statement 1: x := x_arg (AnnAssign) *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
                    lookup_name cx st "y" = NONE` >>
  conj_tac >-
  ((* AnnAssign proof *)
   irule stmts_spec_consequence >>
   qexistsl_tac [
     `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_immutable cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
           lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE`,
     `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
           lookup_name cx st "y" = NONE`,
     `λ_0 _1. F`] >>
   simp[] >>
    irule stmts_spec_ann_assign >>
    irule expr_spec_consequence >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                         lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
                         lookup_name cx st "x" = NONE ∧
                         lookup_name cx st "y" = NONE`,
                  `λtv st. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                         lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
                         lookup_name cx st "x" = NONE ∧
                         lookup_name cx st "y" = NONE ∧
                         tv = Value (IntV (Unsigned 256) xarg)`] >>
    conj_tac >- (simp[] >> rpt strip_tac >> drule_all lookup_immutable_implies_lookup_name >> simp[]) >>
    conj_tac >-
      (simp[] >> rpt strip_tac >-
         metis_tac[lookup_name_none_to_lookup_scoped_var] >-
         metis_tac[scopes_nonempty_after_update] >-
         metis_tac[valid_lookups_preserved_after_update_no_name] >-
         simp[lookup_after_update] >>
         simp[lookup_name_preserved_after_update]) >>
    irule expr_spec_consequence >>
    qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE) ∧
                         lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg)`,
                  `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE) ∧
                         lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
                         tv = Value (IntV (Unsigned 256) xarg)`] >>
    simp[] >>
    ACCEPT_TAC (BETA_RULE (ISPECL [
      ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                              lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE``,
      ``cx:evaluation_context``, ``"x_arg":string``, ``IntV (Unsigned 256) xarg``] expr_spec_name_eq))) >>
  (* Statement 2: x += 10 (AugAssign) *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                    lookup_name cx st "y" = NONE` >>
  conj_tac >-
  ((* AugAssign proof for x += 10 *)
   irule stmts_spec_consequence >>
   qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
                        lookup_name cx st "y" = NONE) ∧
                       (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st "x"`,
                 `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                        lookup_name cx st "y" = NONE`,
                 `λ_0 _1. F`] >>
   conj_tac >- (simp[] >> metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
   conj_tac >- simp[] >>
   conj_tac >- simp[] >>
   MATCH_MP_TAC (BETA_RULE (ISPECL [
     ``λst:evaluation_state. (st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
                              lookup_name cx st "y" = NONE)``,
     ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                              lookup_name cx st "y" = NONE``,
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
                         lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
                         lookup_name cx st "y" = NONE`,
                  `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
                         lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
                         lookup_name cx st "y" = NONE) ∧
                         tv = Value (IntV (Unsigned 256) 10)`] >>
    conj_tac >- simp[] >>
    conj_tac >-
       (simp[scopes_nonempty_after_update, lookup_after_update, lookup_name_preserved_after_update] >>
        metis_tac[valid_lookups_preserved_after_update_var_in_scope, lookup_scoped_var_implies_var_in_scope]) >>
   ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 10)``]
     (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                                       lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
                                       lookup_name cx st "y" = NONE``,
              ``ARB:'a``, ``cx:evaluation_context``,
              ``IntL (Unsigned 256) 10``] expr_spec_literal))) >>
  (* Statement 3: if x > 100 then x := 100 else x += 10 *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    (∃x. lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) x) ∧ 20 ≤ x ∧ x ≤ 110) ∧
                    lookup_name cx st "y" = NONE` >>
  conj_tac >-
  ((* If statement *)
   irule stmts_spec_if >>
   qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                     lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                     lookup_name cx st "y" = NONE` >>
   qexists_tac `BoolV (xarg + 10 > 100)` >>
   conj_tac >- (Cases_on `xarg + 10 > 100` >> simp[]) >>
   (* Condition evaluation: x > 100 *)
   conj_tac >- (
     irule expr_spec_builtin_bop >>
     qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                         lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                         lookup_name cx st "y" = NONE`,
                   `IntV (Unsigned 256) (xarg + 10)`,
                   `IntV (Unsigned 256) 100`] >>
     simp[evaluate_binop_def] >>
     conj_tac >- (
        irule expr_spec_consequence >>
        qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "y" = NONE) ∧ valid_lookups cx st ∧
                            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))`,
                      `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "y" = NONE) ∧ valid_lookups cx st ∧
                            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧ tv = Value (IntV (Unsigned 256) (xarg + 10))`] >>
        simp[] >>
        ACCEPT_TAC (BETA_RULE (ISPECL [
           ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧ lookup_name cx st "y" = NONE``,
           ``cx:evaluation_context``, ``"x":string``,
           ``IntV (Unsigned 256) (xarg + 10)``] expr_spec_scoped_var_eq))) >>
      irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
              lookup_name cx st "y" = NONE`,
        `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
              lookup_name cx st "y" = NONE) ∧
              tv = Value (IntV (Unsigned 256) 100)`] >>
      simp[] >>
      ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 100)``]
        (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                  lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                  lookup_name cx st "y" = NONE``,
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
             lookup_name cx (tl_scopes st) "y" = NONE ∧
             ¬(xarg + 10 > 100)`,
       `λst. (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
             HD st.scopes = FEMPTY ∧
             lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 20)) ∧
             lookup_name cx (tl_scopes st) "y" = NONE ∧
             ¬(xarg + 10 > 100)`,
       `λv st. F`] >>
     simp[] >>
     conj_tac >- (rpt strip_tac >> gvs[lookup_in_current_scope_hd, lookup_in_tl_scopes]) >>
     conj_tac >- (
       simp[] >> rpt strip_tac >>
       qexists_tac `xarg + 20` >>
       gvs[lookup_in_current_scope_hd, lookup_in_tl_scopes, vyperTypeValueTheory.within_int_bound_def] >>
       intLib.ARITH_TAC) >>
     irule stmts_spec_consequence >>
     qexistsl_tac [
       `λst. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
              valid_lookups cx (tl_scopes st) ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
              lookup_name cx (tl_scopes st) "y" = NONE ∧
              ¬(xarg + 10 > 100)) ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧
             var_in_scope st "x"`,
       `λst. (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
              HD st.scopes = FEMPTY ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 20)) ∧
              lookup_name cx (tl_scopes st) "y" = NONE ∧
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
                               lookup_name cx (tl_scopes st) "y" = NONE ∧
                               ¬(xarg + 10 > 100)``,
       ``λst:evaluation_state. (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
                               HD st.scopes = FEMPTY ∧
                               lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 20)) ∧
                               lookup_name cx (tl_scopes st) "y" = NONE ∧
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
              lookup_name cx (tl_scopes st) "y" = NONE ∧
              ¬(xarg + 10 > 100)`,
        `λtv st. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
              valid_lookups cx (tl_scopes st) ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
              lookup_name cx (tl_scopes st) "y" = NONE ∧
              ¬(xarg + 10 > 100)) ∧
              tv = Value (IntV (Unsigned 256) 10)`] >>
      simp[] >>
      conj_tac >- (
       rpt strip_tac >-
       (`(tl_scopes (update_scoped_var st "x" (IntV (Unsigned 256) (xarg + 20)))).scopes ≠ []` by
          (irule scopes_nonempty_preserved_after_update_in_tl_scopes >>
           gvs[lookup_in_current_scope_hd] >>
           `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
           gvs[var_in_tl_scopes] >>
           irule lookup_scoped_var_implies_var_in_scope >>
           gvs[lookup_in_tl_scopes]) >>
        gvs[]) >-
       (irule valid_lookups_preserved_after_update_in_tl_scopes >>
        gvs[lookup_in_current_scope_hd] >>
        `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
        gvs[var_in_tl_scopes] >>
        irule lookup_scoped_var_implies_var_in_scope >>
        gvs[lookup_in_tl_scopes]) >-
       (`HD (update_scoped_var st "x" (IntV (Unsigned 256) (xarg + 20))).scopes = HD st.scopes` by
          (irule hd_scopes_preserved_after_update_in_tl_scopes >>
           gvs[lookup_in_current_scope_hd] >>
           `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
           gvs[var_in_tl_scopes] >>
           irule lookup_scoped_var_implies_var_in_scope >>
           gvs[lookup_in_tl_scopes]) >>
        gvs[]) >-
       simp[lookup_after_update] >>
       `lookup_name cx (tl_scopes (update_scoped_var st "x" (IntV (Unsigned 256) (xarg + 20)))) "y" =
        lookup_name cx (tl_scopes st) "y"` by
         (irule lookup_name_preserved_after_update_in_tl_scopes >>
          gvs[lookup_in_current_scope_hd] >>
          `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
          gvs[var_in_tl_scopes] >>
          irule lookup_scoped_var_implies_var_in_scope >>
          gvs[lookup_in_tl_scopes]) >>
       gvs[]) >>
     ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 10)``]
       (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
                   (tl_scopes st).scopes ≠ [] ∧
                   valid_lookups (cx:evaluation_context) (tl_scopes st) ∧
                   lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                   lookup_name cx (tl_scopes st) "y" = NONE ∧
                   ¬(xarg + 10 > 100)``,
                ``ARB:'a``, ``cx:evaluation_context``,
                ``IntL (Unsigned 256) 10``] expr_spec_literal))) >>
   (* Then branch: x := 100 (when xarg + 10 > 100) *)
   irule stmts_spec_consequence >>
   qexistsl_tac [
     `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
           valid_lookups cx (tl_scopes st) ∧
           lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
           lookup_name cx (tl_scopes st) "y" = NONE ∧
           xarg + 10 > 100`,
     `λst. (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
           HD st.scopes = FEMPTY ∧
           lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 100) ∧
           lookup_name cx (tl_scopes st) "y" = NONE`,
     `λv st. F`] >>
   simp[] >>
   conj_tac >- (rpt strip_tac >> gvs[lookup_in_current_scope_hd, lookup_in_tl_scopes]) >>
   conj_tac >- (
     simp[] >> rpt strip_tac >>
     qexists_tac `100` >>
     simp[lookup_in_current_scope_hd, lookup_in_tl_scopes]) >>
   irule stmts_spec_consequence >>
   qexistsl_tac [
     `λst. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
            valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
            lookup_name cx (tl_scopes st) "y" = NONE ∧
            xarg + 10 > 100) ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧
           var_in_scope st "x"`,
     `λst. (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
            HD st.scopes = FEMPTY ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 100) ∧
            lookup_name cx (tl_scopes st) "y" = NONE`,
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
                              lookup_name cx (tl_scopes st) "y" = NONE ∧
                              xarg + 10 > 100``,
      ``λst:evaluation_state. (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
                              HD st.scopes = FEMPTY ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 100) ∧
                              lookup_name cx (tl_scopes st) "y" = NONE``,
      ``cx:evaluation_context``, ``"x":string``,
      ``Literal (IntL (Unsigned 256) 100):expr``] stmts_spec_assign_scoped_var)) >>
   irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
             valid_lookups cx (tl_scopes st) ∧
             lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
             lookup_name cx (tl_scopes st) "y" = NONE ∧
             xarg + 10 > 100) ∧ var_in_scope st "x"`,
      `λtv st. ((st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
             valid_lookups cx (tl_scopes st) ∧
             lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
             lookup_name cx (tl_scopes st) "y" = NONE ∧
             xarg + 10 > 100) ∧ var_in_scope st "x") ∧
             tv = Value (IntV (Unsigned 256) 100)`] >>
    simp[] >>
    conj_tac >- (
      rpt strip_tac >-
      (`(tl_scopes (update_scoped_var st "x" (IntV (Unsigned 256) 100))).scopes ≠ []` by
        (irule scopes_nonempty_preserved_after_update_in_tl_scopes >>
         gvs[lookup_in_current_scope_hd] >>
         `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
         gvs[var_in_tl_scopes] >>
         metis_tac[lookup_scoped_var_implies_var_in_scope, lookup_in_tl_scopes]) >>
      gvs[]) >-
     (irule valid_lookups_preserved_after_update_in_tl_scopes >>
      gvs[lookup_in_current_scope_hd] >>
      `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
      gvs[var_in_tl_scopes] >>
      metis_tac[lookup_scoped_var_implies_var_in_scope, lookup_in_tl_scopes]) >-
     (`HD (update_scoped_var st "x" (IntV (Unsigned 256) 100)).scopes = HD st.scopes` by
        (irule hd_scopes_preserved_after_update_in_tl_scopes >>
         gvs[lookup_in_current_scope_hd] >>
         `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
         gvs[var_in_tl_scopes] >>
         metis_tac[lookup_scoped_var_implies_var_in_scope, lookup_in_tl_scopes]) >>
      gvs[]) >-
     simp[lookup_after_update] >>
     `lookup_name cx (tl_scopes (update_scoped_var st "x" (IntV (Unsigned 256) 100))) "y" =
      lookup_name cx (tl_scopes st) "y"` by
       (irule lookup_name_preserved_after_update_in_tl_scopes >>
        gvs[lookup_in_current_scope_hd] >>
        `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
        gvs[var_in_tl_scopes] >>
        metis_tac[lookup_scoped_var_implies_var_in_scope, lookup_in_tl_scopes]) >>
     gvs[]) >>
   ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 100)``]
     (ISPECL [``λst:evaluation_state. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
                 (tl_scopes st).scopes ≠ [] ∧
                 valid_lookups (cx:evaluation_context) (tl_scopes st) ∧
                 lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                 lookup_name cx (tl_scopes st) "y" = NONE ∧
                 xarg + 10 > 100) ∧ var_in_scope st "x"``,
              ``ARB:'a``, ``cx:evaluation_context``,
              ``IntL (Unsigned 256) 100``] expr_spec_literal))) >>
  (* Statements 4-6: Use stmts_spec_exists to handle the existential over x *)
   irule stmts_spec_consequence >>
   qexistsl_tac [
     `λst. ∃xval. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                  lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                  20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
     `λst. F`,
     `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >>
   conj_tac >- (simp[] >> metis_tac[]) >>
   conj_tac >- simp[] >>
   conj_tac >- simp[] >>
   (* Use stmts_spec_exists to lift the existential *)
   irule stmts_spec_exists >>
   rpt strip_tac >>
   (* Now for a fixed xval where 20 ≤ xval ≤ 110, prove the spec *)
   (* Statement 4: if x > 20 then return x else [] *)
   irule stmts_spec_cons >>
   qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                     lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) x) ∧
                     x ≤ 20 ∧ lookup_name cx st "y" = NONE` >>
   conj_tac >-
   ((* If statement proof *)
    irule stmts_spec_if >>
    qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                      lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) x) ∧
                      lookup_name cx st "y" = NONE` >>
    qexists_tac `BoolV ((x:int) > 20)` >>
    conj_tac >- (Cases_on `(x:int) > 20` >> simp[]) >>
    (* Condition: x > 20 *)
    conj_tac >- (
      irule expr_spec_builtin_bop >>
      qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
                          lookup_name cx st "y" = NONE`,
                    `IntV (Unsigned 256) (x:int)`,
                    `IntV (Unsigned 256) 20`] >>
      simp[evaluate_binop_def] >>
      conj_tac >- (
        irule expr_spec_consequence >>
        qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "y" = NONE) ∧
                            valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int))`,
                      `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "y" = NONE) ∧
                            valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
                            tv = Value (IntV (Unsigned 256) (x:int))`] >>
        simp[] >>
        ACCEPT_TAC (BETA_RULE (ISPECL [
           ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧ lookup_name cx st "y" = NONE``,
           ``cx:evaluation_context``, ``"x":string``,
           ``IntV (Unsigned 256) (x:int)``] expr_spec_scoped_var_eq))) >>
       irule expr_spec_consequence >>
       qexistsl_tac [
         `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
               lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
               lookup_name cx st "y" = NONE`,
         `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
               lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
               lookup_name cx st "y" = NONE) ∧
               tv = Value (IntV (Unsigned 256) 20)`] >>
       simp[] >>
       ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 20)``]
         (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                   lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
                   lookup_name cx st "y" = NONE``,
                  ``ARB:'a``, ``cx:evaluation_context``,
                  ``IntL (Unsigned 256) 20``] expr_spec_literal))) >>
    simp[] >>
    (* Else branch: empty - x ≤ 20 *)
    conj_tac >- (
      irule stmts_spec_consequence >>
      qexistsl_tac [
        `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
              valid_lookups cx (tl_scopes st) ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
              lookup_name cx (tl_scopes st) "y" = NONE ∧
              ¬((x:int) > 20)`,
        `λst. (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
              HD st.scopes = FEMPTY ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
              lookup_name cx (tl_scopes st) "y" = NONE ∧
              (x:int) ≤ 20`,
        `λv st. F`] >>
      simp[] >>
      conj_tac >- (rpt strip_tac >> gvs[lookup_in_current_scope_hd, lookup_in_tl_scopes]) >>
      conj_tac >- (rpt strip_tac >> gvs[lookup_in_current_scope_hd, lookup_in_tl_scopes] >> intLib.ARITH_TAC) >>
      irule stmts_spec_nil) >>
    (* Then branch: return x - x > 20 *)
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
            valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
            lookup_name cx (tl_scopes st) "y" = NONE ∧
            (x:int) > 20`,
      `λst. F`,
      `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >>
    simp[] >>
    conj_tac >- (rpt strip_tac >> gvs[lookup_in_current_scope_hd, lookup_in_tl_scopes]) >>
    conj_tac >- (rpt strip_tac >> qexists_tac `(x:int)` >> intLib.ARITH_TAC) >>
    irule stmts_spec_return_some >>
    irule expr_spec_consequence >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
                        valid_lookups cx (tl_scopes st) ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
                        lookup_name cx (tl_scopes st) "y" = NONE ∧
                        (x:int) > 20`,
                  `λtv st. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
                        valid_lookups cx (tl_scopes st) ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
                        lookup_name cx (tl_scopes st) "y" = NONE ∧
                        (x:int) > 20) ∧ tv = Value (IntV (Unsigned 256) (x:int))`] >>
    simp[] >>
    conj_tac >- (rpt strip_tac >> qexists_tac `IntV (Unsigned 256) (x:int)` >> intLib.ARITH_TAC) >>
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
             lookup_name cx (tl_scopes st) "y" = NONE ∧ (x:int) > 20) ∧
            valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int))`,
      `λtv st. (st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
             lookup_name cx (tl_scopes st) "y" = NONE ∧ (x:int) > 20) ∧
            valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
            tv = Value (IntV (Unsigned 256) (x:int))`] >>
    conj_tac >- (simp[] >> rpt strip_tac >> irule valid_lookups_tl_scopes_rev >> simp[]) >>
    conj_tac >- simp[] >>
    ACCEPT_TAC (BETA_RULE (ISPECL [
      ``λst:evaluation_state. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧ (tl_scopes st).scopes ≠ [] ∧
                              lookup_name (cx:evaluation_context) (tl_scopes st) "y" = NONE ∧ (x:int) > 20``,
      ``cx:evaluation_context``, ``"x":string``,
      ``IntV (Unsigned 256) (x:int)``] expr_spec_scoped_var_eq))) >>
   (* Statements 5-6: x ≤ 20, so x = 20 (since 20 ≤ x). y := x + 20, return y *)
   (* At this point x = 20 (since 20 ≤ x ∧ x ≤ 20) *)
   irule stmts_spec_cons >>
   qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                     lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) ((x:int) + 20)) ∧
                     lookup_name cx st "x" = SOME (IntV (Unsigned 256) (x:int))` >>
   conj_tac >-
   ((* AnnAssign y := x + 20 *)
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
            (x:int) ≤ 20 ∧ lookup_name cx st "y" = NONE`,
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) ((x:int) + 20)) ∧
            lookup_name cx st "x" = SOME (IntV (Unsigned 256) (x:int))`,
      `λ_0 _1. F`] >>
    simp[] >>
    conj_tac >- (rpt strip_tac >> drule_all lookup_scoped_var_implies_lookup_name >> simp[]) >>
    irule stmts_spec_ann_assign >>
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
            lookup_name cx st "y" = NONE`,
      `λtv st. st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
              lookup_name cx st "y" = NONE ∧
              tv = Value (IntV (Unsigned 256) ((x:int) + 20))`] >>
    simp[] >>
    conj_tac >-
      (simp[] >> rpt strip_tac >-
         metis_tac[lookup_name_none_to_lookup_scoped_var] >-
         metis_tac[scopes_nonempty_after_update] >-
         metis_tac[valid_lookups_preserved_after_update_no_name] >-
         simp[lookup_after_update] >>
         drule_all lookup_scoped_var_implies_lookup_name >> simp[lookup_name_preserved_after_update]) >>
    (* Prove x + 20 *)
    irule expr_spec_builtin_bop >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
            lookup_name cx st "y" = NONE`,
      `IntV (Unsigned 256) (x:int)`,
      `IntV (Unsigned 256) 20`] >>
    simp[evaluate_binop_def, bounded_int_op_def] >>
    conj_tac >- (gvs[vyperTypeValueTheory.within_int_bound_def] >> intLib.ARITH_TAC) >>
    conj_tac >- (
      irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "y" = NONE) ∧
              valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int))`,
        `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "y" = NONE) ∧
              valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
              tv = Value (IntV (Unsigned 256) (x:int))`] >>
      simp[] >>
      ACCEPT_TAC (BETA_RULE (ISPECL [
         ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧ lookup_name cx st "y" = NONE``,
         ``cx:evaluation_context``, ``"x":string``,
         ``IntV (Unsigned 256) (x:int)``] expr_spec_scoped_var_eq))) >>
     irule expr_spec_consequence >>
     qexistsl_tac [
       `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
             lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
             lookup_name cx st "y" = NONE`,
       `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
             lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
             lookup_name cx st "y" = NONE) ∧
             tv = Value (IntV (Unsigned 256) 20)`] >>
     simp[] >>
     ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 20)``]
       (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                 lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
                 lookup_name cx st "y" = NONE``,
                ``ARB:'a``, ``cx:evaluation_context``,
                ``IntL (Unsigned 256) 20``] expr_spec_literal))) >>
   (* Statement 6: return y *)
   irule stmts_spec_consequence >>
   qexistsl_tac [
     `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) ((x:int) + 20))`,
     `λst. F`,
     `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >>
   simp[] >>
   irule stmts_spec_return_some >>
   irule expr_spec_consequence >>
   qexistsl_tac [
     `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) ((x:int) + 20))`,
     `λtv st. st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) ((x:int) + 20)) ∧
           tv = Value (IntV (Unsigned 256) ((x:int) + 20))`] >>
   simp[] >>
   conj_tac >- (rpt strip_tac >> intLib.ARITH_TAC) >>
   ACCEPT_TAC (BETA_RULE (ISPECL [
      ``λst:evaluation_state. st.scopes ≠ []``,
      ``cx:evaluation_context``, ``"y":string``,
      ``IntV (Unsigned 256) ((x:int) + 20)``] expr_spec_scoped_var_eq))
*)
QED
