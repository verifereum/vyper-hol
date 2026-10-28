Theory sourceShiftCountTest
Ancestors
  sourceExprTest sourceExprElaborate sourceExprDefs sourceConstAST sourceSyntax
  sourceResolve vyperAST finite_map
Libs
  intLib

(* Context comes from independently declared runtime operands, never metadata.
   Literal arithmetic is validated before canonical-value coercion at the use. *)
Definition source_shift_test_def:
  source_shift_test env count_ty op rhs =
    source_expr_elaborate 12
      (source_expr_test_env env (BaseT (IntT 256)) with
        var_types := FEMPTY |++ [("x",BaseT (IntT 256));("n",count_ty)])
      [[("x",["x"]);("n",["n"])]]
      [(["x"],SR_Dynamic);(["n"],SR_Dynamic)] []
      [(["x"],SE_Runtime (Name (BaseT (IntT 256)) "x"));
       (["n"],SE_Runtime (Name count_ty "n"))]
      (BaseT (IntT 256)) (SX_Binary op (SX_Name "x") rhs)
End

Theorem source_shift_unsigned_narrow_runtime:
  source_shift_test env (BaseT (UintT 8)) SCB_LShift (SX_Name "n") =
    SC_Value (Builtin (BaseT (IntT 256)) (Bop ShL)
      [Name (BaseT (IntT 256)) "x";Name (BaseT (UintT 8)) "n"]) /\
  source_shift_test env (BaseT (UintT 8)) SCB_RShift
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Name "n")) =
    SC_Value (Builtin (BaseT (IntT 256)) (Bop ShR)
      [Name (BaseT (IntT 256)) "x";Builtin (BaseT (UintT 8)) (Bop Add)
        [Literal (BaseT (UintT 8)) (IntL 1);Name (BaseT (UintT 8)) "n"]])
Proof
  EVAL_TAC
QED

Theorem source_shift_constant_count_coercion:
  source_shift_test env (BaseT (UintT 8)) SCB_LShift
    (SX_Binary SCB_Add
      (SX_Binary SCB_Sub (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
      (SX_Literal (SCL_Int 2))) =
    SC_Value (Builtin (BaseT (IntT 256)) (Bop ShL)
      [Name (BaseT (IntT 256)) "x";Literal (BaseT (UintT 256)) (IntL 1)]) /\
  source_shift_test env (BaseT (UintT 8)) SCB_RShift
    (SX_Binary SCB_Sub
      (SX_Binary SCB_Add (SX_Literal (SCL_Int 256)) (SX_Literal (SCL_Int 1)))
      (SX_Literal (SCL_Int 256))) =
    SC_Value (Builtin (BaseT (IntT 256)) (Bop ShR)
      [Name (BaseT (IntT 256)) "x";Literal (BaseT (UintT 256)) (IntL 1)])
Proof
  EVAL_TAC
QED

Theorem source_shift_whole_constant_and_required_contexts:
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Binary SCB_LShift (SX_Literal (SCL_Int 2))
      (SX_Binary SCB_Add
        (SX_Binary SCB_Sub (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
        (SX_Literal (SCL_Int 2)))) =
      SC_Value (Literal (BaseT (UintT 256)) (IntL 4)) /\
  source_expr_range_bound 12 (source_expr_test_env env (BaseT (UintT 256)))
    [] [] [] []
    (SX_Binary SCB_LShift (SX_Literal (SCL_Int 2))
      (SX_Binary SCB_Add
        (SX_Binary SCB_Sub (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
        (SX_Literal (SCL_Int 2)))) = SC_Value 4 /\
  source_expr_test_elaborate env (BaseT (UintT 8))
    (SX_Binary SCB_Add
      (SX_Binary SCB_Sub (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
      (SX_Literal (SCL_Int 2))) = SC_Invalid SCErr_Type
Proof
  EVAL_TAC
QED

(* Kernel-proved wide arithmetic equations avoid bit-at-a-time recomputation. *)
val () = computeLib.add_funs
  [CONV_RULE (RAND_CONV EVAL) source_expr_wide_left,
   CONV_RULE (LAND_CONV (RATOR_CONV (RAND_CONV EVAL))) source_expr_wide_right];

Theorem source_shift_source_rejections_retained:
  source_shift_test env (BaseT (IntT 8)) SCB_LShift (SX_Name "n") =
    SC_Invalid SCErr_Type /\
  source_shift_test env (BaseT (IntT 256)) SCB_RShift
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Name "n")) =
    SC_Invalid SCErr_Type /\
  source_shift_test env (BaseT (UintT 8)) SCB_LShift
    (SX_Unary SCU_Neg
      (SX_Binary SCB_Sub (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 1)))) =
    SC_Invalid SCErr_Type /\
  source_shift_test env (BaseT (UintT 8)) SCB_LShift
    (SX_Binary SCB_FloorDiv (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0))) =
    SC_Invalid SCErr_ZeroDivisor /\
  source_shift_test env (BaseT (UintT 8)) SCB_LShift
    (SX_Binary SCB_RShift
      (SX_Binary SCB_LShift (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 256)))
      (SX_Literal (SCL_Int 255))) = SC_Invalid SCErr_Type
Proof
  rpt conj_tac >> EVAL_TAC
QED
