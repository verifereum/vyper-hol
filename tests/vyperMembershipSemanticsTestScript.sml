Theory vyperMembershipSemanticsTest
Ancestors
  vyperAST vyperContext vyperState vyperInterpreter vyperSmallStep
  vyperValueOperation vyperValue vyperTypeContract vyperEvalPureExpr vyperLookup
  vyperTypeSystem compileEnv

Theorem read_local_value[local]:
  lookup_scopes_val id st.scopes = SOME v ==>
  read_result cx (PlaceR (MemoryPlace id [])) st = (INL v, st)
Proof
  simp[lookup_scopes_val_SOME] >> strip_tac >>
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_option_def, return_def, lift_sum_def,
       read_memory_path_def, evaluate_subscripts_def]
QED

Theorem lookup_local_exists[local]:
  lookup_scopes_val id sc = SOME v ==> IS_SOME (lookup_scopes id sc)
Proof
  simp[lookup_scopes_val_SOME] >> strip_tac >> simp[]
QED

Theorem evaluate_builtin_bop_type[local,simp]:
  evaluate_type (get_tenv cx) t2 = SOME tv ==>
  evaluate_builtin cx acc ty (Bop bop) [t1; t2] [v1; v2] =
    evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
      tv bop v1 v2
Proof
  strip_tac >> simp[evaluate_builtin_def]
QED

(* The symbolic scope assumption fixes x=0 without requiring a whole contract. *)
Theorem literal_membership_eval_test:
  lookup_scopes_val "x" st.scopes = SOME (IntV 0) /\
  evaluate_type (get_tenv cx)
    (ArrayT (BaseT (UintT 256)) (Fixed 2)) =
    SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) ==>
  eval_expr cx
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Name (BaseT (UintT 256)) "x";
       Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
         [Literal (BaseT (UintT 256)) (IntL 0);
          Literal (BaseT (UintT 256)) (IntL 1)]]) st =
  (INL (Value (BoolV (~is_notin))),st)
Proof
  strip_tac >>
  qpat_assum `evaluate_type (get_tenv cx) (ArrayT (BaseT (UintT 256)) (Fixed 2)) =
              SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2))`
    (fn th => rewrite_tac[th]) >>
  imp_res_tac lookup_local_exists >>
  imp_res_tac read_local_value >>
  Cases_on `is_notin` >>
  simp[expr_type_def] >>
  simp[evaluate_def, builtin_args_length_ok_def, type_check_def, check_def,
       assert_def, bind_def, ignore_bind_def, return_def, raise_def,
       get_scopes_def, get_accounts_def, precompile_call_success_def,
       lift_sum_def, read_local_value, cj 1 read_result_def, evaluate_literal_def,
       evaluate_builtin_bop_type, evaluate_binop_def, binop_negate_def, evaluate_in_array_def,
       vyperValueTheory.make_array_value_def,
       vyperValueTheory.enumerate_static_array_def,
       vyperValueTheory.default_value_def, compatible_bound_def,
       type_slot_size_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  EVAL_TAC >> simp[return_def, wordsTheory.dimword_def,
                    fcpLib.INDEX_CONV ``dimindex(:256)``,
                    vyperValueTheory.default_value_def]
QED

(* The named-array witness uses exactly the sparse local value produced by
   a = [7,0,5]. The default zero must still be visible. *)
Theorem local_array_membership_eval_test:
  lookup_scopes_val "x" st.scopes = SOME (IntV 0) /\
  lookup_scopes_val "a" st.scopes =
    SOME (ArrayV (SArrayV [(0,IntV 7); (2,IntV 5)])) /\
  evaluate_type (get_tenv cx)
    (ArrayT (BaseT (UintT 256)) (Fixed 3)) =
    SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 3)) ==>
  eval_expr cx
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Name (BaseT (UintT 256)) "x";
       Name (ArrayT (BaseT (UintT 256)) (Fixed 3)) "a"]) st =
  (INL (Value (BoolV (~is_notin))),st)
Proof
  strip_tac >>
  imp_res_tac lookup_local_exists >>
  imp_res_tac read_local_value >>
  Cases_on `is_notin` >>
  simp[expr_type_def] >>
  simp[evaluate_def, builtin_args_length_ok_def, type_check_def, check_def,
       assert_def, bind_def, ignore_bind_def, return_def, raise_def,
       get_scopes_def, lift_option_type_def, lift_sum_def, cj 1 read_result_def,
       evaluate_builtin_bop_type, evaluate_binop_def, binop_negate_def,
       evaluate_in_array_def, default_value_def, type_slot_size_def,
       wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  EVAL_TAC >> simp[return_def, wordsTheory.dimword_def,
                    fcpLib.INDEX_CONV ``dimindex(:256)``,
                    vyperValueTheory.default_value_def]
QED

Theorem membership_cps_defaults_test:
  lookup_scopes_val "x" st.scopes = SOME (IntV 0) /\
  lookup_scopes_val "a" st.scopes =
    SOME (ArrayV (SArrayV [(0,IntV 7); (2,IntV 5)])) /\
  evaluate_type (get_tenv cx)
    (ArrayT (BaseT (UintT 256)) (Fixed 3)) =
    SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 3)) ==>
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
    SOME (ArrayV (SArrayV [(0,IntV 7); (2,IntV 5)])) /\
  evaluate_type (get_tenv cx)
    (ArrayT (BaseT (UintT 256)) (Fixed 3)) =
    SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 3)) ==>
  eval_pure_expr cx st
    (Builtin (BaseT BoolT) (Bop (if is_notin then NotIn else In))
      [Name (BaseT (UintT 256)) "x";
       Name (ArrayT (BaseT (UintT 256)) (Fixed 3)) "a"]) =
  SOME (Value (BoolV (~is_notin)))
Proof
  strip_tac >>
  qpat_assum `evaluate_type (get_tenv cx) (ArrayT (BaseT (UintT 256)) (Fixed 3)) =
              SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 3))`
    (fn th => rewrite_tac[th]) >>
  imp_res_tac lookup_local_exists >>
  imp_res_tac read_local_value >>
  Cases_on `is_notin` >>
  rw[expr_type_def] >>
  simp[eval_pure_expr_def, lookup_name_def, builtin_args_length_ok_def, read_result_def,
       bind_def, return_def,
       evaluate_builtin_bop_type, evaluate_binop_def, binop_negate_def, evaluate_in_array_def, default_value_def,
       type_slot_size_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >>
  EVAL_TAC >> simp[wordsTheory.dimword_def,
                    fcpLib.INDEX_CONV ``dimindex(:256)``,
                    vyperValueTheory.default_value_def]
QED

Theorem membership_pure_failure_test:
  eval_pure_expr cx st
    (Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT BoolT) (IntL 0)]) = NONE /\
  eval_pure_expr cx st (Builtin (BaseT BoolT) (Bop In) []) = NONE /\
  eval_pure_expr cx st (Builtin (BaseT BoolT) (Bop NotIn)
    [Literal (BaseT (UintT 256)) (IntL 0)]) = NONE
Proof
  simp[eval_pure_expr_def, builtin_args_length_ok_def, read_result_def,
       bind_def, return_def, evaluate_literal_def, expr_type_def] >>
  EVAL_TAC
QED

Theorem membership_missing_array_type_test:
  evaluate_type (get_tenv cx)
    (ArrayT (StructT (NONE,"missing")) (Fixed 1)) = NONE ==>
  !is_notin.
  evaluate_builtin cx acc (BaseT BoolT) (Bop (if is_notin then NotIn else In))
    [BaseT (UintT 256); ArrayT (StructT (NONE,"missing")) (Fixed 1)]
    [IntV 0; ArrayV (SArrayV [])] = INR (TypeError "Membership type")
Proof
  strip_tac >>
  qpat_assum `evaluate_type (get_tenv cx)
    (ArrayT (StructT (NONE,"missing")) (Fixed 1)) = NONE`
    (fn th => rewrite_tac[th]) >>
  gen_tac >>
  Cases_on `is_notin` >>
  simp[evaluate_builtin_def]
QED

Theorem membership_missing_flag_type_test:
  evaluate_type (get_tenv cx) (FlagT (NONE,"missing")) = NONE ==>
  !is_notin.
  evaluate_builtin cx acc (BaseT BoolT) (Bop (if is_notin then NotIn else In))
    [FlagT (NONE,"missing"); FlagT (NONE,"missing")] [FlagV 1; FlagV 1] =
    INR (TypeError "Membership type")
Proof
  strip_tac >>
  qpat_assum `evaluate_type (get_tenv cx) (FlagT (NONE,"missing")) = NONE`
    (fn th => rewrite_tac[th]) >>
  gen_tac >>
  Cases_on `is_notin` >>
  simp[evaluate_builtin_def]
QED

Theorem membership_resolved_none_type_test:
  evaluate_type (get_tenv cx) NoneT = SOME NoneTV ==>
  evaluate_builtin cx acc (BaseT BoolT) (Bop In)
    [NoneT; NoneT] [FlagV 1; FlagV 1] =
    INL (BoolV (int_and 1 1 ≠ 0))
Proof
  strip_tac >>
  qpat_assum `evaluate_type (get_tenv cx) NoneT = SOME NoneTV`
    (fn th => rewrite_tac[th]) >>
  simp[evaluate_builtin_def, evaluate_binop_def, binop_negate_def,
       int_bitwiseTheory.int_and_def]
QED

(* The checker/lowering interface lives on the lowering side: the type system
   does not depend on compileEnv. *)
(* Symbolic bounds cover both literal/static and variable/dynamic arrays.
   Fixed bytes wider than 32 are not primitive words either. *)
Theorem membership_checker_reject_aggregate_test:
  !neg bd n fields inner ibd name m.
  let bop = if neg then NotIn else In in
  ~well_typed_binop (BaseT BoolT) bop (BaseT (StringT n))
      (ArrayT (BaseT (StringT n)) bd) /\
  ~well_typed_binop (BaseT BoolT) bop (BaseT (BytesT (Dynamic n)))
      (ArrayT (BaseT (BytesT (Dynamic n))) bd) /\
  ~well_typed_binop (BaseT BoolT) bop (StructT name)
      (ArrayT (StructT name) bd) /\
  ~well_typed_binop (BaseT BoolT) bop (TupleT fields)
      (ArrayT (TupleT fields) bd) /\
  ~well_typed_binop (BaseT BoolT) bop (ArrayT inner ibd)
      (ArrayT (ArrayT inner ibd) bd) /\
  (32 < m ==> ~well_typed_binop (BaseT BoolT) bop
      (BaseT (BytesT (Fixed m))) (ArrayT (BaseT (BytesT (Fixed m))) bd))
Proof
  Cases >> simp[well_typed_binop_def, is_prim_word_type_def]
QED

Theorem membership_checker_accept_words_test:
  !neg bd k fid m.
  let bop = if neg then NotIn else In in
  well_typed_binop (BaseT BoolT) bop (BaseT (UintT k))
      (ArrayT (BaseT (UintT k)) bd) /\
  well_typed_binop (BaseT BoolT) bop (BaseT (IntT k))
      (ArrayT (BaseT (IntT k)) bd) /\
  well_typed_binop (BaseT BoolT) bop (BaseT BoolT)
      (ArrayT (BaseT BoolT) bd) /\
  well_typed_binop (BaseT BoolT) bop (BaseT AddressT)
      (ArrayT (BaseT AddressT) bd) /\
  well_typed_binop (BaseT BoolT) bop (BaseT DecimalT)
      (ArrayT (BaseT DecimalT) bd) /\
  well_typed_binop (BaseT BoolT) bop (FlagT fid)
      (ArrayT (FlagT fid) bd) /\
  well_typed_binop (BaseT BoolT) bop (FlagT fid) (FlagT fid) /\
  (m <= 32 ==> well_typed_binop (BaseT BoolT) bop
      (BaseT (BytesT (Fixed m))) (ArrayT (BaseT (BytesT (Fixed m))) bd))
Proof
  Cases >> simp[well_typed_binop_def, is_prim_word_type_def]
QED
