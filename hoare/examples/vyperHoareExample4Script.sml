Theory vyperHoareExample4

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup vyperEvalMisc vyperArray

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

(* ===== Step 1: arr := [10, 11, 12] ===== *)

(* Common predicate for stmt1 - avoids repeating in ISPECL calls *)
val stmt1_P = ``λst:evaluation_state. st.scopes ≠ [] ∧
  valid_lookups (cx:evaluation_context) st ∧
  lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
  lookup_name cx st "arr" = NONE ∧ lookup_name cx st "y" = NONE``;

Theorem stmt1_arr_init[local]:
  ∀cx x.
    IS_SOME (get_self_code cx) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧
          lookup_name cx st "y" = NONE⦄
    [AnnAssign "arr" (ArrayT (BaseT (IntT 128)) (Fixed 3))
       (Builtin (MakeArray (SOME (BaseT (IntT 128))) (Fixed 3))
          [Literal (IntL (Signed 128) 10);
           Literal (IntL (Signed 128) 11);
           Literal (IntL (Signed 128) 12)])]
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "y" = NONE
     ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_ann_assign >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧
          lookup_name cx st "y" = NONE`,
    `λtv st. tv = Value (ArrayV (make_array_value (BaseTV (IntT 128)) (Fixed 3)
                  [IntV (Signed 128) 10; IntV (Signed 128) 11;
                   IntV (Signed 128) 12])) ∧
             st.scopes ≠ [] ∧ valid_lookups cx st ∧
             lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
             lookup_name cx st "arr" = NONE ∧
             lookup_name cx st "y" = NONE`] >>
  conj_tac >- simp[] >>
  conj_tac >- (
    simp[arr_init_make_array] >> rpt strip_tac >> gvs[]
    >- metis_tac[lookup_name_none_to_lookup_scoped_var]
    >- gvs[scopes_nonempty_after_update]
    >- (irule valid_lookups_preserved_after_update_no_name >> simp[])
    >- simp[lookup_after_update]
    >- simp[lookup_immutable_preserved_after_update]
    >> simp[lookup_name_preserved_after_update]) >>
  (* expr_spec_builtin_make_array needs explicit ISPECL due to higher-order matching *)
  MATCH_MP_TAC (BETA_RULE (ISPECL [stmt1_P, stmt1_P,
    ``cx:evaluation_context``, ``BaseT (IntT 128) : type``, ``Fixed 3 : bound``,
    ``[Literal (IntL (Signed 128) 10); Literal (IntL (Signed 128) 11);
      Literal (IntL (Signed 128) 12)]``,
    ``[IntV (Signed 128) 10; IntV (Signed 128) 11; IntV (Signed 128) 12]``,
    ``BaseTV (IntT 128)``
  ] expr_spec_builtin_make_array)) >>
  simp[vyperTypeValueTheory.evaluate_type_def, vyperTypeValueTheory.compatible_bound_def] >>
  (* exprs_spec for [Literal 10; Literal 11; Literal 12] *)
  MATCH_MP_TAC (BETA_RULE (ISPECL [``cx:evaluation_context``, stmt1_P, stmt1_P,
    ``Literal (IntL (Signed 128) 10)``,
    ``[Literal (IntL (Signed 128) 11); Literal (IntL (Signed 128) 12)]``,
    ``IntV (Signed 128) 10``, ``[IntV (Signed 128) 11; IntV (Signed 128) 12]``,
    stmt1_P] exprs_spec_cons)) >>
  conj_tac >- (
    irule expr_spec_consequence >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧ lookup_name cx st "y" = NONE`,
      `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧ lookup_name cx st "y" = NONE) ∧
          tv = Value (IntV (Signed 128) 10)`] >>
    simp[] >>
    ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Signed 128) 10)``]
      (ISPECL [stmt1_P, ``ARB:'a``, ``cx:evaluation_context``,
               ``IntL (Signed 128) 10``] expr_spec_literal))) >>
  (* exprs_spec for [Literal 11; Literal 12] *)
  MATCH_MP_TAC (BETA_RULE (ISPECL [``cx:evaluation_context``, stmt1_P, stmt1_P,
    ``Literal (IntL (Signed 128) 11)``,
    ``[Literal (IntL (Signed 128) 12)]``,
    ``IntV (Signed 128) 11``, ``[IntV (Signed 128) 12]``,
    stmt1_P] exprs_spec_cons)) >>
  conj_tac >- (
    irule expr_spec_consequence >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧ lookup_name cx st "y" = NONE`,
      `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧ lookup_name cx st "y" = NONE) ∧
          tv = Value (IntV (Signed 128) 11)`] >>
    simp[] >>
    ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Signed 128) 11)``]
      (ISPECL [stmt1_P, ``ARB:'a``, ``cx:evaluation_context``,
               ``IntL (Signed 128) 11``] expr_spec_literal))) >>
  (* exprs_spec for [Literal 12] *)
  MATCH_MP_TAC (BETA_RULE (ISPECL [``cx:evaluation_context``, stmt1_P, stmt1_P,
    ``Literal (IntL (Signed 128) 12)``, ``[] : expr list``,
    ``IntV (Signed 128) 12``, ``[] : value list``,
    stmt1_P] exprs_spec_cons)) >>
  conj_tac >- (
    irule expr_spec_consequence >>
    qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧ lookup_name cx st "y" = NONE`,
      `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "arr" = NONE ∧ lookup_name cx st "y" = NONE) ∧
          tv = Value (IntV (Signed 128) 12)`] >>
    simp[] >>
    ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Signed 128) 12)``]
      (ISPECL [stmt1_P, ``ARB:'a``, ``cx:evaluation_context``,
               ``IntL (Signed 128) 12``] expr_spec_literal))) >>
  ACCEPT_TAC (BETA_RULE (ISPECL [``cx:evaluation_context``, stmt1_P] exprs_spec_nil))
QED

(* ===== Step 2: y := x % 3 ===== *)

(* Common predicate for stmt2 *)
val stmt2_P = ``λst:evaluation_state. st.scopes ≠ [] ∧
  valid_lookups (cx:evaluation_context) st ∧
  lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
  lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) (x:int)) ∧
  lookup_name cx st "y" = NONE``;

Theorem stmt2_y_assign[local]:
  ∀cx x.
    within_int_bound (Unsigned 256) x ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "y" = NONE⦄
    [AnnAssign "y" (BaseT (UintT 256))
       (Builtin (Bop Mod) [Name "x"; Literal (IntL (Unsigned 256) 3)])]
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (x % 3))
     ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_ann_assign >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "y" = NONE`,
    `λtv st. tv = Value (IntV (Unsigned 256) (x % 3)) ∧
             st.scopes ≠ [] ∧ valid_lookups cx st ∧
             lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
             lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
             lookup_name cx st "y" = NONE`] >>
  conj_tac >- simp[] >>
  conj_tac >- (
    simp[] >> rpt strip_tac >> gvs[]
    >- (irule lookup_name_none_to_lookup_scoped_var >> metis_tac[])
    >- gvs[scopes_nonempty_after_update]
    >- (irule valid_lookups_preserved_after_update_no_name >> simp[])
    >- simp[lookup_scoped_var_preserved_after_update]
    >> simp[lookup_after_update]) >>
  (* Builtin (Bop Mod) [Name "x"; Literal 3] with R including lookup_immutable *)
  MATCH_MP_TAC (BETA_RULE (ISPECL [stmt2_P, stmt2_P, stmt2_P,
    ``cx:evaluation_context``, ``Name "x"``,
    ``Literal (IntL (Unsigned 256) 3)``,
    ``IntV (Unsigned 256) (x:int)``, ``IntV (Unsigned 256) 3``,
    ``Mod:binop``, ``IntV (Unsigned 256) (x % 3)``
  ] expr_spec_builtin_bop)) >>
  simp[evaluate_binop_mod_uint256_3] >>
  conj_tac >- (
    (* Name "x": wrap with expr_spec_consequence to add lookup_name *)
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
             lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
             lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
             lookup_name cx st "y" = NONE) ∧
            lookup_name cx st "x" = SOME (IntV (Unsigned 256) x)`,
      `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
             lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
             lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
             lookup_name cx st "y" = NONE) ∧
            lookup_name cx st "x" = SOME (IntV (Unsigned 256) x) ∧
            tv = Value (IntV (Unsigned 256) x)`] >>
    conj_tac >- (simp[] >> metis_tac[lookup_immutable_implies_lookup_name]) >>
    conj_tac >- simp[] >>
    ACCEPT_TAC (BETA_RULE (ISPECL [stmt2_P,
      ``cx:evaluation_context``, ``"x":string``,
      ``IntV (Unsigned 256) (x:int)``] expr_spec_name_eq))) >>
  (* Literal 3 *)
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "y" = NONE`,
    `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
          lookup_name cx st "y" = NONE) ∧
          tv = Value (IntV (Unsigned 256) 3)`] >>
  simp[] >>
  ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 3)``]
    (ISPECL [stmt2_P, ``ARB:'a``, ``cx:evaluation_context``,
             ``IntL (Unsigned 256) 3``] expr_spec_literal))
QED

(* ===== Helper: RHS of stmt3 evaluates correctly ===== *)

(* Common predicate for stmt3 - valid_lookups, arr, y *)
val stmt3_P = ``λst:evaluation_state. valid_lookups (cx:evaluation_context) st ∧
  lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
  lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (yval:int))``;

Theorem stmt3_rhs_spec[local]:
  ∀cx yval a.
    IS_SOME (get_self_code cx) ∧
    within_int_bound (Unsigned 256) yval ∧
    0 ≤ yval ∧ yval < 3 ∧
    array_index arr_init (2 − yval) = SOME (IntV (Signed 128) a) ∧
    within_int_bound (Signed 128) a ∧
    within_int_bound (Signed 128) (a + 7) ⇒
    ⟦cx⟧
    ⦃λst. valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)⦄
    (Builtin (Bop Add)
       [Subscript (Name "arr")
          (Builtin (Bop Sub)
             [Literal (IntL (Unsigned 256) 2); Name "y"]);
        Literal (IntL (Signed 128) 7)])
    ⇓⦃λtv st. tv = Value (IntV (Signed 128) (a + 7)) ∧
              valid_lookups cx st ∧
              lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
              lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)⦄
Proof
  rpt strip_tac >>
  (* Bop Add: arr[2-y] + 7 *)
  MATCH_MP_TAC (BETA_RULE (ISPECL [stmt3_P, stmt3_P, stmt3_P,
    ``cx:evaluation_context``,
    ``Subscript (Name "arr")
        (Builtin (Bop Sub) [Literal (IntL (Unsigned 256) 2); Name "y"])``,
    ``Literal (IntL (Signed 128) 7)``,
    ``IntV (Signed 128) (a:int)``, ``IntV (Signed 128) 7``,
    ``Add:binop``, ``IntV (Signed 128) (a + 7)``
  ] expr_spec_builtin_bop)) >>
  `within_int_bound (Signed 128) 7` by EVAL_TAC >>
  simp[evaluate_binop_add_int128] >>
  conj_tac >- (
    (* Subscript (Name "arr") (Bop Sub [Literal 2; Name "y"]) *)
    MATCH_MP_TAC (BETA_RULE (ISPECL [stmt3_P, stmt3_P, stmt3_P,
      ``cx:evaluation_context``, ``Name "arr"``,
      ``Builtin (Bop Sub) [Literal (IntL (Unsigned 256) 2); Name "y"]``,
      ``arr_init``, ``Unsigned 256``, ``2 − (yval:int)``,
      ``IntV (Signed 128) (a:int)``
    ] expr_spec_subscript_array)) >>
    simp[] >>
    conj_tac >- (
      (* Name "arr" → ArrayV arr_init *)
      irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval) ∧
              valid_lookups cx st ∧
              lookup_scoped_var st "arr" = SOME (ArrayV arr_init)`,
        `λtv st. lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval) ∧
              valid_lookups cx st ∧
              lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
              tv = Value (ArrayV arr_init)`] >>
      simp[] >>
      ACCEPT_TAC (BETA_RULE (ISPECL [
        ``λst:evaluation_state. lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (yval:int))``,
        ``cx:evaluation_context``, ``"arr":string``,
        ``ArrayV arr_init``] expr_spec_scoped_var_eq))) >>
    (* Bop Sub [Literal 2; Name "y"] *)
    MATCH_MP_TAC (BETA_RULE (ISPECL [stmt3_P, stmt3_P, stmt3_P,
      ``cx:evaluation_context``,
      ``Literal (IntL (Unsigned 256) 2)``, ``Name "y"``,
      ``IntV (Unsigned 256) 2``, ``IntV (Unsigned 256) (yval:int)``,
      ``Sub:binop``, ``IntV (Unsigned 256) (2 − yval)``
    ] expr_spec_builtin_bop)) >>
    `within_int_bound (Unsigned 256) 2` by EVAL_TAC >>
    `yval ≤ 2` by intLib.ARITH_TAC >>
    simp[evaluate_binop_sub_small_unsigned] >>
    conj_tac >- (
      (* Literal 2 *)
      irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. valid_lookups cx st ∧
              lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
              lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)`,
        `λtv st. (valid_lookups cx st ∧
              lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
              lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)) ∧
              tv = Value (IntV (Unsigned 256) 2)`] >>
      simp[] >>
      ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 2)``]
        (ISPECL [stmt3_P, ``ARB:'a``, ``cx:evaluation_context``,
                 ``IntL (Unsigned 256) 2``] expr_spec_literal))) >>
    (* Name "y" *)
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
            valid_lookups cx st ∧
            lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)`,
      `λtv st. lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
            valid_lookups cx st ∧
            lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval) ∧
            tv = Value (IntV (Unsigned 256) yval)`] >>
    simp[] >>
    ACCEPT_TAC (BETA_RULE (ISPECL [
      ``λst:evaluation_state. lookup_scoped_var st "arr" = SOME (ArrayV arr_init)``,
      ``cx:evaluation_context``, ``"y":string``,
      ``IntV (Unsigned 256) (yval:int)``] expr_spec_scoped_var_eq))) >>
  (* Literal 7 *)
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)`,
    `λtv st. (valid_lookups cx st ∧
              lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
              lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)) ∧
             tv = Value (IntV (Signed 128) 7)`] >>
  simp[] >>
  ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Signed 128) 7)``]
    (ISPECL [stmt3_P, ``ARB:'a``, ``cx:evaluation_context``,
             ``IntL (Signed 128) 7``] expr_spec_literal))
QED

(* ===== Step 3: arr[y] = arr[2-y] + 7 ===== *)

Theorem stmt3_arr_assign[local]:
  ∀cx yval a.
    IS_SOME (get_self_code cx) ∧
    0 ≤ yval ∧ yval < 3 ∧
    within_int_bound (Unsigned 256) yval ∧
    array_index arr_init (2 − yval) = SOME (IntV (Signed 128) a) ∧
    within_int_bound (Signed 128) a ∧
    within_int_bound (Signed 128) (a + 7) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)⦄
    [Assign (BaseTarget (SubscriptTarget (NameTarget "arr") (Name "y")))
       (Builtin (Bop Add)
          [Subscript (Name "arr")
             (Builtin (Bop Sub)
                [Literal (IntL (Unsigned 256) 2); Name "y"]);
           Literal (IntL (Signed 128) 7)])]
    ⦃λst. ∃arr_new.
          st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval) ∧
          array_index arr_new yval = SOME (IntV (Signed 128) (a + 7))
     ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
           lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)) ∧
          (cx.txn.is_creation ⇒ valid_lookups cx st) ∧
          var_in_scope st "arr"`,
    `λst. ∃arr_new.
          st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval) ∧
          array_index arr_new yval = SOME (IntV (Signed 128) (a + 7))`,
    `λ_ _. F`] >>
  conj_tac >- (simp[] >> metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  MATCH_MP_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state. st.scopes ≠ [] ∧
        valid_lookups (cx:evaluation_context) st ∧
        lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
        lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (yval:int))``,
    stmt3_P,
    ``λst:evaluation_state. ∃arr_new.
        st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
        lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
        lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (yval:int)) ∧
        array_index arr_new yval = SOME (IntV (Signed 128) ((a:int) + 7))``,
    ``cx:evaluation_context``, ``"arr":string``, ``(yval:int)``,
    ``Name "y"``,
    ``Builtin (Bop Add)
       [Subscript (Name "arr")
          (Builtin (Bop Sub) [Literal (IntL (Unsigned 256) 2); Name "y"]);
        Literal (IntL (Signed 128) 7)]``
  ] stmts_spec_assign_scoped_var_array)) >>
  conj_tac >- (
    (* Index: Name "y" → IntSubscript yval *)
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. (lookup_scoped_var st "arr" = SOME (ArrayV arr_init)) ∧
            valid_lookups cx st ∧
            lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)`,
      `λtv st. (lookup_scoped_var st "arr" = SOME (ArrayV arr_init)) ∧
            valid_lookups cx st ∧
            lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval) ∧
            tv = Value (IntV (Unsigned 256) yval)`] >>
    conj_tac >- simp[] >>
    conj_tac >- simp[get_value_to_key_def, value_to_key_def] >>
    ACCEPT_TAC (BETA_RULE (ISPECL [
      ``λst:evaluation_state. lookup_scoped_var st "arr" = SOME (ArrayV arr_init)``,
      ``cx:evaluation_context``, ``"y":string``,
      ``IntV (Unsigned 256) (yval:int)``] expr_spec_scoped_var_eq))) >>
  (* Value: arr[2-y] + 7 *)
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)`,
    `λtv st. tv = Value (IntV (Signed 128) (a + 7)) ∧
             valid_lookups cx st ∧
             lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
             lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)`] >>
  conj_tac >- simp[] >>
  (* Split the postcondition implication from the spec *)
  conj_tac >| [
    (* Postcondition implication: Q ⇒ Q' *)
    simp[] >> rpt strip_tac >>
    (* Subgoal: array_is_mutable arr_init *)
    simp[arr_init_mutable] >>
    (* Subgoal: yval < &array_length arr_init *)
    simp[arr_init_length] >>
    (* Subgoal: ∃arr_new. update properties *)
    sg `∃arr_new. array_set_index arr_init yval (IntV (Signed 128) (a + 7)) =
        INL (ArrayV arr_new)` >-
      (irule (iffLR array_set_index_valid) >>
       simp[arr_init_mutable, arr_init_valid_index] >>
       intLib.ARITH_TAC) >>
    qexists_tac `arr_new` >>
    simp[scopes_nonempty_after_update, lookup_after_update] >>
    conj_tac >- (irule valid_lookups_preserved_after_update_var_in_scope >>
                  metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
    conj_tac >- simp[lookup_scoped_var_preserved_after_update] >>
    drule array_index_after_set_same >> simp[],
    (* Spec: stmt3_rhs_spec *)
    irule stmt3_rhs_spec >> simp[]
  ]
QED

(* ===== Step 4: return arr[y] ===== *)

val stmt4_exists_precond_thm = BETA_RULE (ISPECL [
  ``λ(arr_new:array_value) (st:evaluation_state).
        st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
        lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
        lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (yval:int))``,
  ``λ(arr_new:array_value).
        array_index arr_new (yval:int) = SOME (IntV (Signed 128) (n:int))``]
  stmts_spec_exists_precond);

val stmt4_subscript_thm = SIMP_RULE std_ss [] (BETA_RULE (ISPECL [
  ``λst:evaluation_state. lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (yval:int)) ∧
      valid_lookups (cx:evaluation_context) st ∧
      lookup_scoped_var st "arr" = SOME (ArrayV (arr_new:array_value))``,
  ``λst:evaluation_state. lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (yval:int)) ∧
      valid_lookups (cx:evaluation_context) st ∧
      lookup_scoped_var st "arr" = SOME (ArrayV (arr_new:array_value))``,
  ``λst:evaluation_state. T``,
  ``cx:evaluation_context``, ``Name "arr"``, ``Name "y"``,
  ``arr_new:array_value``, ``Unsigned 256``, ``(yval:int)``,
  ``IntV (Signed 128) (n:int)``] expr_spec_subscript_array));

Theorem stmt4_return[local]:
  ∀cx yval n.
    IS_SOME (get_self_code cx) ∧ 17 ≤ n ∧ n ≤ 19 ⇒
    ⟦cx⟧
    ⦃λst. ∃arr_new.
          st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval) ∧
          array_index arr_new yval = SOME (IntV (Signed 128) n)⦄
    [Return (SOME (Subscript (Name "arr") (Name "y")))]
    ⦃λst. F ∥ λv st. ∃n. v = IntV (Signed 128) n ∧ 17 ≤ n ∧ n ≤ 19⦄
Proof
  rpt strip_tac >>
  (* Rearrange precondition to put array_index first for stmts_spec_exists_precond *)
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. ∃arr_new.
          array_index arr_new yval = SOME (IntV (Signed 128) n) ∧
          st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)`,
    `λst. F`,
    `λv st. ∃m. v = IntV (Signed 128) m ∧ 17 ≤ m ∧ m ≤ 19`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  (* Extract array_index from precondition as hypothesis *)
  irule stmt4_exists_precond_thm >>
  qx_gen_tac `arr_new` >> strip_tac >>
  (* Now: array_index arr_new yval = SOME (...) is in assumptions *)
  irule stmts_spec_return_some >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. (lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)) ∧
          valid_lookups cx st ∧
          lookup_scoped_var st "arr" = SOME (ArrayV arr_new)`,
    `λtv st. tv = Value (IntV (Signed 128) n)`] >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  MATCH_MP_TAC stmt4_subscript_thm >>
  simp[] >>
  conj_tac >- (
    irule expr_spec_consequence >>
    qexistsl_tac [
      `λst. (lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)) ∧
            valid_lookups cx st ∧ lookup_scoped_var st "arr" = SOME (ArrayV arr_new)`,
      `λtv st. (lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)) ∧
            valid_lookups cx st ∧ lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
            tv = Value (ArrayV arr_new)`] >>
    simp[] >>
    ACCEPT_TAC (BETA_RULE (ISPECL [
      ``λst:evaluation_state. lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (yval:int))``,
      ``cx:evaluation_context``, ``"arr":string``,
      ``ArrayV (arr_new:array_value)``] expr_spec_scoped_var_eq))) >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. (lookup_scoped_var st "arr" = SOME (ArrayV arr_new)) ∧
          valid_lookups cx st ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval)`,
    `λtv st. (lookup_scoped_var st "arr" = SOME (ArrayV arr_new)) ∧
          valid_lookups cx st ∧
          lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) yval) ∧
          tv = Value (IntV (Unsigned 256) yval)`] >>
  simp[] >>
  ACCEPT_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state. lookup_scoped_var st "arr" = SOME (ArrayV (arr_new:array_value))``,
    ``cx:evaluation_context``, ``"y":string``,
    ``IntV (Unsigned 256) (yval:int)``] expr_spec_scoped_var_eq))
QED

(* ===== Helper: within_int_bound for small signed values ===== *)

Theorem within_signed_128_small[local]:
  ∀a. 0 ≤ a ∧ a ≤ 19 ⇒ within_int_bound (Signed 128) a
Proof
  rpt strip_tac >>
  simp[vyperTypeValueTheory.within_int_bound_def] >>
  `¬(a < 0)` by intLib.ARITH_TAC >> simp[] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac `20` >>
  conj_tac >- (
    `&(Num a) = a` by simp[integerTheory.INT_OF_NUM] >>
    `a < 20` by intLib.ARITH_TAC >>
    `&(Num a) < &20` by intLib.ARITH_TAC >>
    fs[integerTheory.INT_LT]) >>
  EVAL_TAC
QED

(* ===== Helper: within_int_bound for small unsigned values ===== *)

Theorem within_unsigned_256_small[local]:
  ∀a. 0 ≤ a ∧ a < 3 ⇒ within_int_bound (Unsigned 256) a
Proof
  rpt strip_tac >>
  simp[vyperTypeValueTheory.within_int_bound_def] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac `3` >>
  conj_tac >- (
    `&(Num a) = a` by simp[integerTheory.INT_OF_NUM] >>
    `a < 3` by intLib.ARITH_TAC >>
    `&(Num a) < &3` by intLib.ARITH_TAC >>
    fs[integerTheory.INT_LT]) >>
  EVAL_TAC
QED

(* ===== Main Theorem ===== *)

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
  rpt strip_tac >>
  simp[example_4_body_def, example_4_decl_def, example_4_module_def] >>
  (* Statement 1: arr := [10, 11, 12] *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
                    lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
                    lookup_name cx st "y" = NONE` >>
  conj_tac >- (
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
            lookup_name cx st "arr" = NONE ∧
            lookup_name cx st "y" = NONE`,
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
            lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
            lookup_name cx st "y" = NONE`,
      `λ_ _. F`] >>
    simp[] >>
    irule stmt1_arr_init >> simp[]) >>
  (* Statement 2: y := x % 3 *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
                    lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (x % 3))` >>
  conj_tac >- (
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
            lookup_immutable cx st "x" = SOME (IntV (Unsigned 256) x) ∧
            lookup_name cx st "y" = NONE`,
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
            lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (x % 3))`,
      `λ_ _. F`] >>
    simp[] >>
    irule stmt2_y_assign >> simp[]) >>
  (* Statements 3-4: arr[y] = arr[2-y] + 7; return arr[y]
     Need case analysis: 0 ≤ x%3 < 3 *)
  `0 ≤ x % 3 ∧ x % 3 < 3` by (
    irule uint256_mod_3_bounds >>
    fs[vyperTypeValueTheory.within_int_bound_def]) >>
  `valid_index arr_init (2 − x % 3)` by (
    simp[arr_init_valid_index] >> intLib.ARITH_TAC) >>
  `∃a. array_index arr_init (2 − x % 3) = SOME (IntV (Signed 128) a) ∧
       10 ≤ a ∧ a ≤ 12` by (
    irule arr_init_index_bounds >> simp[]) >>
  `within_int_bound (Unsigned 256) (x % 3)` by (
    irule within_unsigned_256_small >> simp[]) >>
  `within_int_bound (Signed 128) a` by (
    irule within_signed_128_small >> intLib.ARITH_TAC) >>
  `within_int_bound (Signed 128) (a + 7)` by (
    irule within_signed_128_small >> intLib.ARITH_TAC) >>
  (* Statement 3: arr[y] = arr[2-y] + 7 *)
  irule stmts_spec_cons >>
  qexists_tac `λst. ∃arr_new.
                    st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
                    lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (x % 3)) ∧
                    array_index arr_new (x % 3) = SOME (IntV (Signed 128) (a + 7))` >>
  conj_tac >- (
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "arr" = SOME (ArrayV arr_init) ∧
            lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (x % 3))`,
      `λst. ∃arr_new.
            st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_scoped_var st "arr" = SOME (ArrayV arr_new) ∧
            lookup_scoped_var st "y" = SOME (IntV (Unsigned 256) (x % 3)) ∧
            array_index arr_new (x % 3) = SOME (IntV (Signed 128) (a + 7))`,
      `λ_ _. F`] >>
    simp[] >>
    irule stmt3_arr_assign >> simp[]) >>
  (* Statement 4: return arr[y] *)
  irule stmt4_return >>
  simp[] >> intLib.ARITH_TAC
QED
