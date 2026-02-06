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

(* ===== Helper Lemmas for Statements 4-6 ===== *)

(* Statement 4: if x > 20 then return x else []
   When xval > 20: returns xval (satisfies 20 < n ∧ n ≤ 110)
   When xval ≤ 20: continues with ¬(xval > 20) added to precondition *)
Theorem stmt4_lemma:
  ∀cx xval.
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE⦄
    [If (Builtin (Bop Gt) [Name "x"; Literal (IntL (Unsigned 256) 20)])
       [Return (SOME (Name "x"))] []]
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          20 ≤ xval ∧ xval ≤ 110 ∧ ¬(xval > 20) ∧ lookup_name cx st "y" = NONE
     ∥ λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_if >>
  qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                      lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                      20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
                `BoolV (xval > 20)`] >>
  conj_tac >- (Cases_on `xval > 20` >> simp[]) >>
  (* Condition: x > 20 evaluates to BoolV (xval > 20) *)
  conj_tac >- (
    irule expr_spec_builtin_bop >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                        20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
                 `IntV (Unsigned 256) xval`,
                 `IntV (Unsigned 256) 20`] >>
    simp[evaluate_binop_def] >>
    conj_tac >- (
      irule expr_spec_consequence >>
      qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
                     20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE) ∧
                    valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval)`,
                   `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
                     20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE) ∧
                    valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                    tv = Value (IntV (Unsigned 256) xval)`] >>
      simp[] >>
      ACCEPT_TAC (BETA_RULE (ISPECL [
        ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                                (20:int) ≤ (xval:int) ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE``,
        ``cx:evaluation_context``, ``"x":string``, ``IntV (Unsigned 256) (xval:int)``] expr_spec_scoped_var_eq))) >>
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
            20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
      `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
            20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE) ∧
            tv = Value (IntV (Unsigned 256) 20)`] >>
    simp[] >>
    ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 20)``]
      (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                 lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xval:int)) ∧
                 (20:int) ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE``,
               ``ARB:'a``, ``cx:evaluation_context``,
               ``IntL (Unsigned 256) 20``] expr_spec_literal))) >>
  simp[] >>
  (* Else branch: empty list *)
  conj_tac >- (
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
            (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
            20 ≤ xval ∧ xval ≤ 110 ∧ ¬(xval > 20) ∧
            lookup_name cx (tl_scopes st) "y" = NONE`,
      `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
            (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
            20 ≤ xval ∧ xval ≤ 110 ∧ ¬(xval > 20) ∧
            lookup_name cx (tl_scopes st) "y" = NONE`,
      `λv st. F`] >>
    simp[lookup_in_tl_scopes] >>
    conj_tac >- (rpt strip_tac >> `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >> gvs[GSYM lookup_in_tl_scopes]) >>
    conj_tac >- (rpt strip_tac >> `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >> gvs[lookup_in_tl_scopes]) >>
    irule stmts_spec_nil) >>
  (* Then branch: return x when xval > 20 *)
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
          (tl_scopes st).scopes ≠ [] ∧ valid_lookups cx (tl_scopes st) ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          20 ≤ xval ∧ xval ≤ 110 ∧ xval > 20 ∧
          lookup_name cx (tl_scopes st) "y" = NONE`,
    `λst. F`,
    `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >>
  simp[lookup_in_tl_scopes] >>
  conj_tac >- (rpt strip_tac >> `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >> gvs[GSYM lookup_in_tl_scopes]) >>
  irule stmts_spec_return_some >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. (valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval)) ∧
          20 ≤ xval ∧ xval ≤ 110 ∧ xval > 20`,
    `λtv st. (20 ≤ xval ∧ xval ≤ 110 ∧ xval > 20) ∧ tv = Value (IntV (Unsigned 256) xval)`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule valid_lookups_tl_scopes_rev >> simp[]) >>
  conj_tac >- intLib.ARITH_TAC >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. ((20 ≤ xval ∧ xval ≤ 110 ∧ xval > 20) ∧ valid_lookups cx st) ∧
          valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval)`,
    `λtv st. ((20 ≤ xval ∧ xval ≤ 110 ∧ xval > 20) ∧ valid_lookups cx st) ∧
          valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          tv = Value (IntV (Unsigned 256) xval)`] >>
  simp[] >>
  ACCEPT_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state. ((20:int) ≤ (xval:int) ∧ xval ≤ 110 ∧ xval > 20) ∧ valid_lookups (cx:evaluation_context) st``,
    ``cx:evaluation_context``, ``"x":string``, ``IntV (Unsigned 256) (xval:int)``] expr_spec_scoped_var_eq))
QED

(* Statement 5: y := x + 20
   Precondition: xval = 20 (from 20 ≤ xval ∧ ¬(xval > 20))
   Postcondition: y = xval + 20 = 40
   NOTE: Hoare predicates don't contain ¬(xval > 20) to avoid simplification issues *)
Theorem stmt5_lemma:
  ∀cx xval.
    20 ≤ xval ∧ xval ≤ 110 ∧ ¬(xval > 20) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE⦄
    [AnnAssign "y" (BaseT (UintT 256))
       (Builtin (Bop Add) [Name "x"; Literal (IntL (Unsigned 256) 20)])]
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (xval + 20)) ∧
          20 ≤ xval ∧ xval ≤ 110
     ∥ λv st. F⦄
Proof
  rpt strip_tac >>
  (* xval = 20 from constraints *)
  `xval = 20` by intLib.ARITH_TAC >> gvs[] >>
  irule stmts_spec_ann_assign >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 20) ∧
          lookup_name cx st "y" = NONE`,
    `λtv st. tv = Value (IntV (Unsigned 256) 40) ∧
          st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 20) ∧
          lookup_name cx st "y" = NONE`] >>
  simp[] >>
  conj_tac >- (
    rpt strip_tac >-
    metis_tac[lookup_name_none_to_lookup_scoped_var] >-
    metis_tac[scopes_nonempty_after_update] >-
    metis_tac[valid_lookups_preserved_after_update_no_name] >-
    simp[lookup_scoped_var_preserved_after_update] >>
    simp[lookup_after_update]) >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 20) ∧
          lookup_name cx st "y" = NONE`,
    `λtv st. tv = Value (IntV (Unsigned 256) 40) ∧
             (st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 20) ∧
              lookup_name cx st "y" = NONE)`] >>
  simp[] >>
  MATCH_MP_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (20:int)) ∧
          lookup_name cx st "y" = NONE``,
    ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (20:int)) ∧
          lookup_name cx st "y" = NONE``,
    ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (20:int)) ∧
          lookup_name cx st "y" = NONE``,
    ``cx:evaluation_context``,
    ``Name "x"``,
    ``Literal (IntL (Unsigned 256) 20)``,
    ``IntV (Unsigned 256) (20:int)``,
    ``IntV (Unsigned 256) (20:int)``,
    ``Add:binop``,
    ``IntV (Unsigned 256) (40:int)``
  ] expr_spec_builtin_bop)) >>
  simp[evaluate_binop_def, bounded_int_op_def, vyperTypeValueTheory.within_int_bound_def] >>
  (* Name "x" expression *)
  conj_tac >- (
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. (st.scopes ≠ [] ∧ lookup_name cx st "y" = NONE) ∧
            valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 20)`,
      `λtv st. (st.scopes ≠ [] ∧ lookup_name cx st "y" = NONE) ∧
            valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 20) ∧
            tv = Value (IntV (Unsigned 256) 20)`] >>
    simp[] >>
    ACCEPT_TAC (BETA_RULE (ISPECL [
      ``λst:evaluation_state. st.scopes ≠ [] ∧ lookup_name (cx:evaluation_context) st "y" = NONE``,
      ``cx:evaluation_context``, ``"x":string``, ``IntV (Unsigned 256) (20:int)``] expr_spec_scoped_var_eq))) >>
  (* Literal 20 expression *)
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 20) ∧
          lookup_name cx st "y" = NONE`,
    `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 20) ∧
              lookup_name cx st "y" = NONE) ∧
             tv = Value (IntV (Unsigned 256) 20)`] >>
  simp[] >>
  ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 20)``]
    (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                                      lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (20:int)) ∧
                                      lookup_name cx st "y" = NONE``,
             ``ARB:'a``, ``cx:evaluation_context``,
             ``IntL (Unsigned 256) 20``] expr_spec_literal))
QED

(* Statement 6: return y
   Returns y = 40, which satisfies 20 < 40 ∧ 40 ≤ 110
   NOTE: Hoare predicates don't contain ¬(xval > 20) to avoid simplification issues *)
Theorem stmt6_lemma:
  ∀cx xval.
    20 ≤ xval ∧ xval ≤ 110 ∧ ¬(xval > 20) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (xval + 20)) ∧
          20 ≤ xval ∧ xval ≤ 110⦄
    [Return (SOME (Name "y"))]
    ⦃λst. F ∥ λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110⦄
Proof
  rpt strip_tac >>
  (* xval = 20 from constraints, so y = 40 *)
  `xval = 20` by intLib.ARITH_TAC >> gvs[] >>
  irule stmts_spec_return_some >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. valid_lookups cx st ∧ lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) 40)`,
    `λtv st. tv = Value (IntV (Unsigned 256) 40) ∧ valid_lookups cx st ∧
             lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) 40)`] >>
  simp[] >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. (valid_lookups cx st ∧ valid_lookups cx st) ∧ valid_lookups cx st ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) 40)`,
    `λtv st. (valid_lookups cx st ∧ valid_lookups cx st) ∧ valid_lookups cx st ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) 40) ∧
          tv = Value (IntV (Unsigned 256) 40)`] >>
  simp[] >>
  ACCEPT_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state. valid_lookups (cx:evaluation_context) st``,
    ``cx:evaluation_context``, ``"y":string``, ``IntV (Unsigned 256) (40:int)``] expr_spec_scoped_var_eq))
QED

(* Case 1: xval > 20 - stmt4 returns immediately, stmts 5-6 vacuous *)
Theorem stmts_4_6_xval_gt_20_lemma:
  ∀cx xval.
    xval > 20 ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE⦄
    [If (Builtin (Bop Gt) [Name "x"; Literal (IntL (Unsigned 256) 20)])
       [Return (SOME (Name "x"))] [];
     AnnAssign "y" (BaseT (UintT 256))
       (Builtin (Bop Add) [Name "x"; Literal (IntL (Unsigned 256) 20)]);
     Return (SOME (Name "y"))]
    ⦃λst. F ∥ λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_consequence >>
  qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                      lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                      20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
                `λst. F`,
                `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >> simp[] >>
  irule stmts_spec_cons >> qexists_tac `λst. F` >>
  conj_tac >- (
    irule stmts_spec_consequence >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                        20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
                  `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                        20 ≤ xval ∧ xval ≤ 110 ∧ ¬(xval > 20) ∧ lookup_name cx st "y" = NONE`,
                  `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >>
    conj_tac >- simp[] >> conj_tac >- (simp[] >> intLib.ARITH_TAC) >> conj_tac >- simp[] >>
    irule stmt4_lemma) >>
  irule stmts_spec_false_pre
QED

(* Case 2: xval ≤ 20 - stmt4 doesn't return, proceeds to stmt5 and stmt6 *)
Theorem stmts_4_6_xval_le_20_lemma:
  ∀cx xval.
    20 ≤ xval ∧ xval ≤ 110 ∧ ¬(xval > 20) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE⦄
    [If (Builtin (Bop Gt) [Name "x"; Literal (IntL (Unsigned 256) 20)])
       [Return (SOME (Name "x"))] [];
     AnnAssign "y" (BaseT (UintT 256))
       (Builtin (Bop Add) [Name "x"; Literal (IntL (Unsigned 256) 20)]);
     Return (SOME (Name "y"))]
    ⦃λst. F ∥ λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                    20 ≤ xval ∧ xval ≤ 110 ∧ ¬(xval > 20) ∧ lookup_name cx st "y" = NONE` >>
  conj_tac >- irule stmt4_lemma >>
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                    lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (xval + 20)) ∧
                    20 ≤ xval ∧ xval ≤ 110` >>
  conj_tac >- (
    irule stmts_spec_consequence >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                        20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
                  `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                        lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (xval + 20)) ∧
                        20 ≤ xval ∧ xval ≤ 110`,
                  `λv st. F`] >>
    conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
    irule stmt5_lemma >> simp[]) >>
  irule stmt6_lemma >> simp[]
QED

(* Helper for statements 4-6 combined *)
Theorem stmts_4_6_lemma:
  ∀cx xval.
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
          20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE⦄
    [If (Builtin (Bop Gt) [Name "x"; Literal (IntL (Unsigned 256) 20)])
       [Return (SOME (Name "x"))] [];
     AnnAssign "y" (BaseT (UintT 256))
       (Builtin (Bop Add) [Name "x"; Literal (IntL (Unsigned 256) 20)]);
     Return (SOME (Name "y"))]
    ⦃λst. F ∥ λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110⦄
Proof
  rpt strip_tac >>
  (* Extract 20 ≤ xval ∧ xval ≤ 110 to meta-level using stmts_spec_precond *)
  irule stmts_spec_consequence >>
  qexistsl_tac [`λst. (20 ≤ xval ∧ xval ≤ 110) ∧
                      st.scopes ≠ [] ∧ valid_lookups cx st ∧
                      lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                      lookup_name cx st "y" = NONE`,
                `λst. F`,
                `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >> simp[] >>
  MATCH_MP_TAC (iffLR (BETA_RULE (ISPECL [
    ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xval:int)) ∧
                            lookup_name cx st "y" = NONE``,
    ``λst:evaluation_state. F``,
    ``λ(v:value) (st:evaluation_state). ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110``,
    ``cx:evaluation_context``,
    ``[If (Builtin (Bop Gt) [Name "x"; Literal (IntL (Unsigned 256) 20)])
         [Return (SOME (Name "x"))] [];
       AnnAssign "y" (BaseT (UintT 256))
         (Builtin (Bop Add) [Name "x"; Literal (IntL (Unsigned 256) 20)]);
       Return (SOME (Name "y"))]``,
    ``(20:int) ≤ (xval:int) ∧ xval ≤ 110``] stmts_spec_precond))) >>
  strip_tac >>
  Cases_on `xval > 20` >- (
    (* xval > 20 case *)
    irule stmts_spec_consequence >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                        20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
                  `λst. F`,
                  `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >>
    conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
    irule stmts_4_6_xval_gt_20_lemma >> simp[]) >>
  (* ¬(xval > 20) case *)
  irule stmts_spec_consequence >>
  qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                      lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                      20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
                `λst. F`,
                `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  irule stmts_4_6_xval_le_20_lemma >> simp[]
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
                  `λtv st. tv = Value (IntV (Unsigned 256) xarg) ∧
                         st.scopes ≠ [] ∧ valid_lookups cx st ∧
                         lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
                         lookup_name cx st "x" = NONE ∧
                         lookup_name cx st "y" = NONE`] >> simp[] >>
    conj_tac >- (rpt strip_tac >> drule_all lookup_immutable_implies_lookup_name >> simp[]) >>
    conj_tac >-
      (rpt strip_tac >-
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
      ``Literal (IntL (Unsigned 256) 10):expr``] stmts_spec_aug_assign_scoped_var)) >>
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
      (rpt strip_tac >> gvs[] >>
       qexists_tac `IntV (Unsigned 256) (xarg + 10)` >>
       gvs[evaluate_binop_def, bounded_int_op_def, scopes_nonempty_after_update, lookup_after_update,
           lookup_name_preserved_after_update, vyperTypeValueTheory.within_int_bound_def] >>
       conj_tac >- intLib.ARITH_TAC >>
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
                            lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
                            tv = Value (IntV (Unsigned 256) (xarg + 10))`] >>
        simp[] >>
        ACCEPT_TAC (BETA_RULE (ISPECL [
          ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧ lookup_name cx st "y" = NONE``,
          ``cx:evaluation_context``, ``"x":string``,
          ``IntV (Unsigned 256) (xarg + 10)``] expr_spec_scoped_var_eq))) >>
      irule expr_spec_consequence >>
      qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
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
        ``Literal (IntL (Unsigned 256) 10):expr``] stmts_spec_aug_assign_scoped_var)) >>
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
         rpt strip_tac >> gvs[] >>
         qexists_tac `IntV (Unsigned 256) (xarg + 20)` >>
         gvs[evaluate_binop_def, bounded_int_op_def, vyperTypeValueTheory.within_int_bound_def] >>
         conj_tac >- intLib.ARITH_TAC >>
         conj_tac >-
         (`(tl_scopes (update_scoped_var st "x" (IntV (Unsigned 256) (xarg + 20)))).scopes ≠ []` by
           (irule scopes_nonempty_preserved_after_update_in_tl_scopes >>
            gvs[lookup_in_current_scope_hd] >>
            `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
            gvs[var_in_tl_scopes] >>
            irule lookup_scoped_var_implies_var_in_scope >>
            gvs[lookup_in_tl_scopes]) >>
         gvs[]) >>
         conj_tac >-
        (irule valid_lookups_preserved_after_update_in_tl_scopes >>
         gvs[lookup_in_current_scope_hd] >>
         `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
         gvs[var_in_tl_scopes] >>
         irule lookup_scoped_var_implies_var_in_scope >>
         gvs[lookup_in_tl_scopes]) >>
         conj_tac >-
        (`HD (update_scoped_var st "x" (IntV (Unsigned 256) (xarg + 20))).scopes = HD st.scopes` by
           (irule hd_scopes_preserved_after_update_in_tl_scopes >>
            gvs[lookup_in_current_scope_hd] >>
            `lookup_in_current_scope st "x" = NONE` by gvs[lookup_in_current_scope_hd] >>
            gvs[var_in_tl_scopes] >>
            irule lookup_scoped_var_implies_var_in_scope >>
            gvs[lookup_in_tl_scopes]) >>
         gvs[]) >>
         conj_tac >- simp[lookup_after_update] >>
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
  (* Statements 4-6: Use stmts_4_6_lemma *)
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. ∃xval. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                 lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                 20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE`,
    `λst. F`,
    `λv st. ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110`] >> simp[] >>
  irule (SIMP_RULE std_ss [] (ISPECL [
    ``λ(xval:int) st. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                      lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xval) ∧
                      20 ≤ xval ∧ xval ≤ 110 ∧ lookup_name cx st "y" = NONE``,
    ``λ(xval:int) (st:evaluation_state). F``,
    ``λ(xval:int) (v:value) (st:evaluation_state). ∃n. v = IntV (Unsigned 256) n ∧ 20 < n ∧ n ≤ 110``]
    stmts_spec_exists)) >>
  qx_gen_tac `xval` >> rpt strip_tac >>
  irule stmts_4_6_lemma
QED
