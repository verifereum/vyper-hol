Theory vyperMembershipSemanticsTest
Ancestors
  vyperAST vyperContext vyperState vyperInterpreter vyperSmallStep
  vyperValueOperation vyperValue vyperTypeContract vyperEvalPureExpr vyperLookup

(* The symbolic scope assumption fixes x=0 without requiring a whole contract. *)
Theorem literal_membership_eval_test:
  lookup_scopes_val "x" st.scopes = SOME (IntV 0) ==>
  eval_expr cx
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Name (BaseT (UintT 256)) "x";
       Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
         [Literal (BaseT (UintT 256)) (IntL 0);
          Literal (BaseT (UintT 256)) (IntL 1)]]) st =
  (INL (Value (BoolV (~is_notin))),st)
Proof
  strip_tac >> Cases_on `is_notin` >>
  simp[evaluate_def, builtin_args_length_ok_def, type_check_def, check_def,
       assert_def, bind_def, ignore_bind_def, return_def, raise_def,
       get_scopes_def, get_accounts_def, lift_option_type_def,
       lift_sum_def, materialise_def, evaluate_literal_def,
       evaluate_builtin_def, evaluate_type_def, expr_type_def,
       evaluate_membership_def, evaluate_in_array_def,
       vyperValueTheory.make_array_value_def,
       vyperValueTheory.enumerate_static_array_def,
       vyperValueTheory.default_value_def, compatible_bound_def,
       type_slot_size_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  EVAL_TAC >> simp[return_def]
QED

(* The named-array witness uses exactly the sparse local value produced by
   a = [7,0,5]. The default zero must still be visible. *)
Theorem local_array_membership_eval_test:
  lookup_scopes_val "x" st.scopes = SOME (IntV 0) /\
  lookup_scopes_val "a" st.scopes =
    SOME (ArrayV (SArrayV [(0,IntV 7); (2,IntV 5)])) ==>
  eval_expr cx
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Name (BaseT (UintT 256)) "x";
       Name (ArrayT (BaseT (UintT 256)) (Fixed 3)) "a"]) st =
  (INL (Value (BoolV (~is_notin))),st)
Proof
  strip_tac >> Cases_on `is_notin` >>
  simp[evaluate_def, builtin_args_length_ok_def, type_check_def, check_def,
       assert_def, bind_def, ignore_bind_def, return_def, raise_def,
       get_scopes_def, lift_option_type_def, lift_sum_def, materialise_def,
       evaluate_type_def, expr_type_def, evaluate_membership_def,
       evaluate_in_array_def, default_value_def, type_slot_size_def,
       wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  EVAL_TAC >> simp[return_def]
QED

Theorem membership_cps_defaults_test:
  lookup_scopes_val "x" st.scopes = SOME (IntV 0) /\
  lookup_scopes_val "a" st.scopes =
    SOME (ArrayV (SArrayV [(0,IntV 7); (2,IntV 5)])) ==>
  fromtvk (cont (eval_expr_cps cx
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Name (BaseT (UintT 256)) "x";
       Name (ArrayT (BaseT (UintT 256)) (Fixed 3)) "a"])
    st DoneK)) = (INL (Value (BoolV (~is_notin))),st)
Proof
  simp[GSYM eval_expr_eq_cont_cps, local_array_membership_eval_test]
QED

(* Closed compile-time probes: sparse zero is present; a missing value is not. *)
Theorem membership_constant_defaults_test:
  !is_notin.
  constant_value [] []
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Literal (BaseT (UintT 256)) (IntL 0);
       Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
         (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
         [Literal (BaseT (UintT 256)) (IntL 0);
          Literal (BaseT (UintT 256)) (IntL 1)]]) = SOME (BoolV (~is_notin)) /\
  constant_value [] []
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Literal (BaseT (UintT 256)) (IntL 2);
       Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
         (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
         [Literal (BaseT (UintT 256)) (IntL 0);
          Literal (BaseT (UintT 256)) (IntL 1)]]) = SOME (BoolV is_notin)
Proof
  Cases >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC >> simp[]
QED

Theorem membership_constant_failure_test:
  constant_value [] []
    (Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT (UintT 256)) (IntL 0);
       Literal (StructT (NONE,"missing")) (IntL 0)]) = NONE /\
  constant_value [] [] (Builtin (BaseT BoolT) (Bop In) []) = NONE /\
  constant_value [] [] (Builtin (BaseT BoolT) (Bop NotIn)
    [Literal (BaseT (UintT 256)) (IntL 0)]) = NONE
Proof
  EVAL_TAC
QED

Theorem membership_pure_defaults_test:
  lookup_scopes_val "x" st.scopes = SOME (IntV 0) /\
  lookup_scopes_val "a" st.scopes =
    SOME (ArrayV (SArrayV [(0,IntV 7); (2,IntV 5)])) ==>
  eval_pure_expr cx st
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Name (BaseT (UintT 256)) "x";
       Name (ArrayT (BaseT (UintT 256)) (Fixed 3)) "a"]) =
  SOME (Value (BoolV (~is_notin)))
Proof
  strip_tac >> Cases_on `is_notin` >>
  simp[eval_pure_expr_def, lookup_name_def, builtin_args_length_ok_def, materialise_def,
       bind_def, return_def, evaluate_type_def, expr_type_def,
       evaluate_membership_def, evaluate_in_array_def, default_value_def,
       type_slot_size_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Theorem membership_pure_failure_test:
  evaluate_type (get_tenv cx) (StructT (NONE,"missing")) = NONE ==>
  eval_pure_expr cx st
    (Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT (UintT 256)) (IntL 0);
       Literal (StructT (NONE,"missing")) (IntL 0)]) = NONE /\
  eval_pure_expr cx st (Builtin (BaseT BoolT) (Bop In) []) = NONE /\
  eval_pure_expr cx st (Builtin (BaseT BoolT) (Bop NotIn)
    [Literal (BaseT (UintT 256)) (IntL 0)]) = NONE
Proof
  strip_tac >>
  simp[eval_pure_expr_def, builtin_args_length_ok_def, materialise_def,
       bind_def, return_def, evaluate_literal_def, expr_type_def] >>
  EVAL_TAC
QED
