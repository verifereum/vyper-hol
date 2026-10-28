Theory sourceExprTest
Ancestors
  sourceExprProps sourceExprElaborate sourceExprDefs sourceExprWitnessDefs sourceConstValue
  sourceSyntax sourceResolve sourceTypeResolve sourceTypeDefs sourceConstAnnotation
  sourceConstEval sourceConstAST
  sourceConstBuiltin sourceConstBuiltinTest sourceConstValueStructured
  sourceConstValueStructuredProps
  vyperTypeSystem vyperAST vyperValue vyperTyping finite_map
Libs
  intLib wordsLib cv_transLib

Definition source_expr_test_scopes_def:
  source_expr_test_scopes = [[("x",["x"]); ("y",["y"]); ("t",["t"]);
    ("len",["builtin";"len"]); ("method_id",["builtin";"method_id"]);
    ("abs",["builtin";"abs"]); ("bytes4",["builtin";"bytes4"]);
    ("Bytes",["builtin";"Bytes"])]]
End

Definition source_expr_test_table_def:
  source_expr_test_table = [(["x"],SR_Dynamic); (["y"],SR_Dynamic);
    (["t"],SR_Dynamic); (["builtin";"len"],SR_Builtin SCB_Len);
    (["builtin";"method_id"],SR_Builtin SCB_MethodId);
    (["builtin";"abs"],SR_Builtin SCB_Abs);
    (["builtin";"bytes4"],SR_FixedBytes 4); (["builtin";"Bytes"],SR_Bytes)]
End

Definition source_expr_test_variables_def:
  source_expr_test_variables ty = [(["x"],SE_Runtime (Name ty "x"));
    (["y"],SE_Runtime (Name ty "y"));
    (["t"],SE_Runtime (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t"))]
End

Definition source_expr_test_env_def:
  source_expr_test_env env ty = env with <|
    type_defs := FEMPTY;
    var_types := FEMPTY |++ [("x",ty); ("y",ty);
      ("t",TupleT [BaseT BoolT; BaseT (UintT 256)])] |>
End

Definition source_expr_test_elaborate_def:
  source_expr_test_elaborate env ty source =
    source_expr_elaborate 6 (source_expr_test_env env ty)
      source_expr_test_scopes source_expr_test_table []
      (source_expr_test_variables ty) ty source
End

Theorem source_expr_constant_subtree_power_exponent:
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Binary SCB_Pow (SX_Name "x")
      (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))) =
  SC_Value (Builtin (BaseT (UintT 256)) (Bop Exp)
    [Name (BaseT (UintT 256)) "x"; Literal (BaseT (UintT 256)) (IntL 3)])
Proof
  EVAL_TAC
QED

Theorem source_expr_constant_subtree_power_base:
  source_expr_test_elaborate env (BaseT (IntT 256))
    (SX_Binary SCB_Pow
      (SX_Binary SCB_Sub (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 2)))
      (SX_Name "y")) =
  SC_Value (Builtin (BaseT (IntT 256)) (Bop Exp)
    [Literal (BaseT (IntT 256)) (IntL (-2)); Name (BaseT (IntT 256)) "y"])
Proof
  EVAL_TAC
QED

(* A convenient final constant is NOT a source-typing certificate. *)
Theorem source_expr_original_operator_domains:
  source_expr_test_elaborate env (BaseT (UintT 8))
    (SX_Binary SCB_LShift (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 0))) =
      SC_Invalid SCErr_Type /\
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Unary SCU_Neg (SX_Literal (SCL_Int 1))) =
      SC_Invalid SCErr_Type /\
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Binary SCB_Div (SX_Literal (SCL_Int 4)) (SX_Literal (SCL_Int 2))) =
      SC_Invalid SCErr_Domain
Proof
  EVAL_TAC >> simp[]
QED

Theorem source_expr_nested_domain_cannot_be_erased:
  source_expr_test_elaborate env (BaseT (UintT 8))
    (SX_Binary SCB_Add
      (SX_Binary SCB_LShift (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 0)))
      (SX_Literal (SCL_Int 1))) =
  SC_Invalid SCErr_Type /\
  source_expr_test_elaborate env (BaseT (BytesT (Fixed 1)))
    (SX_Literal (SCL_Bytes [1])) =
  SC_Invalid SCErr_Type
Proof
  EVAL_TAC
QED

Theorem source_expr_original_builtin_domains:
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Call (SX_Name "len") [SX_Literal (SCL_Int 123)] []) =
      SC_Invalid SCErr_Domain /\
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Call (SX_Name "len") [SX_Literal (SCL_Hex "0x1234")] []) =
      SC_Invalid SCErr_Domain /\
  source_expr_test_elaborate env (BaseT (BytesT (Dynamic 4)))
    (SX_Call (SX_Name "method_id") [SX_Name "x"] []) =
      SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_expr_eager_invalid_boolean_child:
  source_expr_test_elaborate env (BaseT BoolT)
    (SX_Boolean SCB_And [SX_Literal (SCL_Bool F);
      SX_Compare SCC_Eq
        (SX_Binary SCB_FloorDiv (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0)))
        (SX_Literal (SCL_Int 0))]) = SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

Theorem source_expr_tuple_index_original_normalized:
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Subscript (SX_Name "t")
      (SX_Binary SCB_Add (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 1)))) =
  SC_Value (Subscript (BaseT (UintT 256))
    (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
    (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  EVAL_TAC
QED

Theorem source_expr_flag_index_range_consumers:
  source_expr_flag 6 (source_expr_test_env env (BaseT BoolT))
    source_expr_test_scopes source_expr_test_table []
    (source_expr_test_variables (BaseT BoolT))
    (SX_Compare SCC_Eq
      (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
      (SX_Literal (SCL_Int 3))) = SC_Value T /\
  source_expr_index 6 (source_expr_test_env env (BaseT (UintT 256)))
    source_expr_test_scopes source_expr_test_table []
    (source_expr_test_variables (BaseT (UintT 256))) 4
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))) = SC_Value 3 /\
  source_expr_range_bound 6 (source_expr_test_env env (BaseT (UintT 256)))
    source_expr_test_scopes source_expr_test_table []
    (source_expr_test_variables (BaseT (UintT 256)))
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))) = SC_Value 3
Proof
  EVAL_TAC
QED

Theorem source_expr_dynamic_required_flag_rejected:
  source_expr_flag 6 (source_expr_test_env env (BaseT BoolT))
    source_expr_test_scopes source_expr_test_table []
    (source_expr_test_variables (BaseT BoolT)) (SX_Name "x") = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_expr_invalid_present_consumers:
  source_expr_flag 6 (source_expr_test_env env (BaseT BoolT))
    source_expr_test_scopes source_expr_test_table []
    (source_expr_test_variables (BaseT BoolT)) (SX_Literal (SCL_Int 1)) =
      SC_Invalid SCErr_Type /\
  source_expr_index 6 (source_expr_test_env env (BaseT (UintT 256)))
    source_expr_test_scopes source_expr_test_table []
    (source_expr_test_variables (BaseT (UintT 256))) 3
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))) =
      SC_Invalid SCErr_Index /\
  source_expr_range_bound 6 (source_expr_test_env env (BaseT (UintT 256)))
    source_expr_test_scopes source_expr_test_table []
    (source_expr_test_variables (BaseT (UintT 256))) (SX_Literal (SCL_Int 0)) =
      SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_expr_source_annotation_connection:
  source_expr_annotated 6 (source_expr_test_env env (BaseT (UintT 256)))
    source_expr_test_scopes source_expr_test_table []
    (source_expr_test_variables (BaseT (UintT 256)))
    [(["uint256"],STI_Integer F 256)] (SCA_Name ["uint256"])
    (SX_Binary SCB_Add (SX_Name "x") (SX_Literal (SCL_Int 2))) =
  ST_Ok (SC_Value (Builtin (BaseT (UintT 256)) (Bop Add)
    [Name (BaseT (UintT 256)) "x"; Literal (BaseT (UintT 256)) (IntL 2)]))
Proof
  EVAL_TAC
QED

(* A shadowed spelling does not inherit builtin identity. *)
Theorem source_expr_shadowed_builtin_no_fallback:
  source_expr_elaborate 4 (source_expr_test_env env (BaseT (UintT 256)))
    [[("len",["user-len"])]] [(["user-len"],SR_Function)] [] []
    (BaseT (UintT 256))
    (SX_Call (SX_Name "len") [SX_Literal (SCL_String "abc")] []) =
  SC_Unsupported SCS_Call
Proof
  EVAL_TAC
QED

(* The hash equation is kernel-proved through the verified cv implementation.
   Registering this specific equation avoids reducing bit-level Keccak again. *)
val () = computeLib.add_funs [source_const_keccak_foo_full];

Theorem source_expr_method_id_original_string:
  source_expr_test_elaborate env (BaseT (BytesT (Dynamic 4)))
    (SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "foo()")] []) =
  SC_Value (Literal (BaseT (BytesT (Dynamic 4))) (BytesL [194w;152w;85w;120w]))
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem source_expr_method_id_original_output_type:
  source_expr_test_elaborate env (BaseT (BytesT (Fixed 4)))
    (SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "foo()")]
      [("output_type",SX_Name "bytes4")]) =
  SC_Value (Literal (BaseT (BytesT (Fixed 4))) (BytesL [194w;152w;85w;120w])) /\
  source_expr_test_elaborate env (BaseT (BytesT (Dynamic 4)))
    (SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "foo()")]
      [("output_type",SX_Subscript (SX_Name "Bytes")
        (SX_Binary SCB_Add (SX_Literal (SCL_Int 2)) (SX_Literal (SCL_Int 2))))]) =
  SC_Value (Literal (BaseT (BytesT (Dynamic 4))) (BytesL [194w;152w;85w;120w]))
Proof
  EVAL_TAC
QED

Theorem source_expr_fuel_no_fallback:
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Binary SCB_Add (SX_Name "x") (SX_Name "y")) =
      SC_Value (Builtin (BaseT (UintT 256)) (Bop Add)
        [Name (BaseT (UintT 256)) "x"; Name (BaseT (UintT 256)) "y"]) /\
  source_expr_elaborate 0 env scopes table constants variables ty source =
    SC_Unsupported (SCS_Syntax "expression-fuel")
Proof
  EVAL_TAC
QED

Theorem source_expr_wide_left:
  source_const_integer_binary SCB_LShift 1 256 = SC_Value (SCV_Int (2 ** 256))
Proof
  EVAL_TAC
QED

Theorem source_expr_wide_right:
  source_const_integer_binary SCB_RShift (2 ** 256) 255 = SC_Value (SCV_Int 2)
Proof
  EVAL_TAC
QED

val () = computeLib.add_funs
  [CONV_RULE (RAND_CONV EVAL) source_expr_wide_left,
   CONV_RULE (LAND_CONV (RATOR_CONV (RAND_CONV EVAL))) source_expr_wide_right];

(* An annotation bound is mathematical source arithmetic, not an executable
   expression subtree. The same intermediate is rejected in a return, range
   bound, tuple index and ABI flag by the authoritative pinned compiler. *)
Theorem source_expr_mathematical_intermediate_bound:
  source_expr_annotated 8
    (source_expr_test_env env (ArrayT (BaseT (UintT 256)) (Fixed 3)))
    source_expr_test_scopes source_expr_test_table [] []
    [(["uint256"],STI_Integer F 256)]
    (SCA_StaticArray (SCA_Name ["uint256"])
      (SCE_Binary SCB_Add
        (SCE_Binary SCB_RShift
          (SCE_Binary SCB_LShift (SCE_Literal (SCL_Int 1)) (SCE_Literal (SCL_Int 256)))
          (SCE_Literal (SCL_Int 255))) (SCE_Literal (SCL_Int 1))))
    (SX_List [SX_Literal (SCL_Int 0);SX_Literal (SCL_Int 0);SX_Literal (SCL_Int 0)]) =
    ST_Ok (SC_Value (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 3))
      (MakeArray (SOME (BaseT (UintT 256))) (Fixed 3))
      (REPLICATE 3 (Literal (BaseT (UintT 256)) (IntL 0))))) /\
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Binary SCB_RShift
      (SX_Binary SCB_LShift (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 256)))
      (SX_Literal (SCL_Int 255))) = SC_Invalid SCErr_Type /\
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Unary SCU_Neg (SX_Literal (SCL_Int 0))) =
      SC_Value (Literal (BaseT (UintT 256)) (IntL 0))
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

(* The pin accepts this mathematical type bound inside a standalone method_id
   call. The former contextual-child runtime elaboration rejected it. The new
   source_expr_original checks the complete source tree before reification. *)
Theorem source_expr_method_id_mathematical_output_bound:
  source_expr_test_elaborate env (BaseT (BytesT (Dynamic 4)))
    (SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "foo()")]
      [("output_type",SX_Subscript (SX_Name "Bytes")
        (SX_Binary SCB_Add
          (SX_Binary SCB_RShift
            (SX_Binary SCB_LShift (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 256)))
            (SX_Literal (SCL_Int 255))) (SX_Literal (SCL_Int 2))))]) =
  SC_Value (Literal (BaseT (BytesT (Dynamic 4))) (BytesL [194w;152w;85w;120w]))
Proof
  EVAL_TAC
QED

Theorem source_expr_decimal_original_source:
  source_expr_test_elaborate env (BaseT DecimalT)
    (SX_Binary SCB_Div (SX_Unary SCU_Neg (SX_Literal (SCL_Decimal 10 1)))
      (SX_Literal (SCL_Decimal 30 1))) =
    SC_Value (Literal (BaseT DecimalT) (DecimalL (-3333333333))) /\
  source_expr_test_elaborate env (BaseT DecimalT)
    (SX_Literal (SCL_Decimal 1 11)) = SC_Invalid SCErr_DecimalPrecision
Proof
  EVAL_TAC
QED

Theorem source_expr_structured_aggregates:
  source_expr_test_elaborate env (TupleT [BaseT BoolT; BaseT (UintT 256)])
    (SX_Tuple [SX_Literal (SCL_Bool T); SX_Literal (SCL_Int 3)]) =
    SC_Value (Builtin (TupleT [BaseT BoolT; BaseT (UintT 256)])
      (MakeArray NONE (Fixed 2))
      [Literal (BaseT BoolT) (BoolL T); Literal (BaseT (UintT 256)) (IntL 3)]) /\
  source_expr_test_elaborate env (ArrayT (BaseT (UintT 256)) (Fixed 2))
    (SX_List [SX_Literal (SCL_Int 0); SX_Literal (SCL_Int 7)]) =
    SC_Value (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
      (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
      [Literal (BaseT (UintT 256)) (IntL 0); Literal (BaseT (UintT 256)) (IntL 7)]) /\
  source_expr_test_elaborate env (BaseT (UintT 256))
    (SX_Subscript (SX_Name "t") (SX_Name "x")) = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

(* Hash reductions are kernel equations from the separate test-input theory. *)
val () = computeLib.add_funs [source_const_keccak_hello, source_expr_hash_transfer,
  source_expr_hash_f, source_expr_hash_E, source_expr_hash_x];

Theorem source_expr_all_retained_witness_bodies:
  LENGTH source_expr_witnesses = 37 /\
  EVERY (\(name,runtime,constants,ty,original,expected).
    source_expr_witness_elaborate env runtime constants ty original = expected)
    source_expr_witnesses
Proof
  simp_tac bool_ss [source_expr_witnesses_def, LET_THM, listTheory.EVERY_DEF,
    listTheory.LENGTH, pairTheory.pair_case_def] >>
  rpt conj_tac >> EVAL_TAC >> simp[source_expr_exists_equal] >>
  EVAL_TAC >> simp[source_expr_exists_equal] >> EVAL_TAC >> simp[source_expr_exists_equal]
QED

(* Additional executable expressions in the witnesses with multiple bodies,
   constructor assignments, tuple initializers, or conditional statements. *)
Theorem source_expr_witness_additional_bodies:
  source_expr_witness_elaborate env [] [(["N"],SCV_Int 10)] (BaseT (UintT 256))
    (SX_Binary SCB_Mul (SX_Name "N") (SX_Literal (SCL_Int 2))) =
      SC_Value (Literal (BaseT (UintT 256)) (IntL 20)) /\
  source_expr_witness_elaborate env [] [] (BaseT (UintT 256)) (SX_Literal (SCL_Int 1)) =
      SC_Value (Literal (BaseT (UintT 256)) (IntL 1)) /\
  source_expr_witness_elaborate env [(["a"],Name (BaseT (UintT 256)) "a")] []
    (BaseT (UintT 256)) (SX_Name "a") = SC_Value (Name (BaseT (UintT 256)) "a") /\
  source_expr_witness_elaborate env [(["msg";"sender"],Builtin (BaseT AddressT) (Env Sender) [])] []
    (BaseT AddressT) (SX_Attribute (SX_Name "msg") "sender") =
      SC_Value (Builtin (BaseT AddressT) (Env Sender) []) /\
  source_expr_witness_elaborate env [] [] (BaseT (BytesT (Fixed 32)))
    (SX_Call (SX_Name "keccak256") [SX_Literal (SCL_String "x")] []) =
      SC_Value (Literal (BaseT (BytesT (Fixed 32)))
        (BytesL [117w;33w;209w;202w;219w;207w;169w;30w;236w;101w;170w;22w;113w;91w;148w;255w;
          193w;201w;101w;75w;165w;126w;162w;239w;26w;33w;39w;188w;161w;18w;122w;131w])) /\
  source_expr_witness_elaborate env [(["A"],TopLevelName (BaseT (UintT 256)) (NONE,"A"))] []
    (BaseT (UintT 256)) (SX_Name "A") = SC_Value (TopLevelName (BaseT (UintT 256)) (NONE,"A")) /\
  source_expr_witness_elaborate env [(["B"],TopLevelName (BaseT AddressT) (NONE,"B"))] []
    (BaseT AddressT) (SX_Name "B") = SC_Value (TopLevelName (BaseT AddressT) (NONE,"B")) /\
  source_expr_witness_elaborate env [(["a"],Name (BaseT (IntT 128)) "a");(["b"],Name (BaseT BoolT) "b")] []
    (TupleT [BaseT (IntT 128);BaseT BoolT]) (SX_Tuple [SX_Name "a";SX_Name "b"]) =
      SC_Value (Builtin (TupleT [BaseT (IntT 128);BaseT BoolT]) (MakeArray NONE (Fixed 2))
        [Name (BaseT (IntT 128)) "a";Name (BaseT BoolT) "b"]) /\
  source_expr_witness_elaborate env [(["x"],Name (BaseT (UintT 256)) "x")] []
    (BaseT BoolT) (SX_Compare SCC_Gt (SX_Name "x") (SX_Literal (SCL_Int 3))) =
      SC_Value (Builtin (BaseT BoolT) (Bop Gt)
        [Name (BaseT (UintT 256)) "x";Literal (BaseT (UintT 256)) (IntL 3)])
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem source_expr_abi_present_invalid_not_default:
  source_expr_witness_elaborate env [] [] (BaseT (BytesT (Dynamic 32)))
    (SX_Call (SX_Name "abi_encode") [SX_Literal (SCL_Int 1)]
      [("ensure_tuple",SX_Literal (SCL_Int 1))]) = SC_Invalid SCErr_Type /\
  source_expr_witness_elaborate env [(["flag"],Name (BaseT BoolT) "flag")] []
    (BaseT (BytesT (Dynamic 32)))
    (SX_Call (SX_Name "abi_encode") [SX_Literal (SCL_Int 1)]
      [("ensure_tuple",SX_Name "flag")]) = SC_Invalid SCErr_Domain /\
  source_expr_witness_elaborate env [] [] (BaseT (BytesT (Dynamic 36)))
    (SX_Call (SX_Name "abi_encode") [SX_Literal (SCL_Int 1)]
      [("method_id",SX_Literal (SCL_Bytes [1;2;3]))]) = SC_Invalid SCErr_Type /\
  source_expr_witness_elaborate env [(["selector"],Name (BaseT (BytesT (Fixed 4))) "selector")] []
    (BaseT (BytesT (Dynamic 36)))
    (SX_Call (SX_Name "abi_encode") [SX_Literal (SCL_Int 1)]
      [("method_id",SX_Name "selector")]) = SC_Invalid SCErr_Domain /\
  source_expr_witness_elaborate env [] [] (BaseT (BytesT (Dynamic 32)))
    (SX_Call (SX_Name "abi_encode") [SX_Literal (SCL_Int 1)]
      [("ensure_tuple",SX_Literal (SCL_Bool T));("ensure_tuple",SX_Literal (SCL_Bool F))]) =
        SC_Invalid SCErr_Keyword /\
  source_expr_witness_elaborate env [(["d"],Name (BaseT (BytesT (Dynamic 64))) "d")] []
    (TupleT [BaseT (UintT 256);BaseT BoolT])
    (SX_Call (SX_Name "abi_decode") [SX_Name "d";SX_Tuple [SX_Name "uint256";SX_Name "bool"]]
      [("unwrap_tuple",SX_Literal (SCL_Int 0))]) = SC_Invalid SCErr_Type
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem source_expr_abi_order_no_tuple_flattening:
  source_expr_witness_elaborate env
    [(["self";"a"],TopLevelName (BaseT (UintT 256)) (NONE,"a"));
     (["self";"b"],TopLevelName (BaseT (UintT 256)) (NONE,"b"))] []
    (BaseT (BytesT (Dynamic 64)))
    (SX_Call (SX_Name "abi_encode")
      [SX_Attribute (SX_Name "self") "a";SX_Attribute (SX_Name "self") "b"] []) =
  SC_Value (TypeBuiltin (BaseT (BytesT (Dynamic 64))) (AbiEncode T NONE)
    (TupleT [BaseT (UintT 256);BaseT (UintT 256)])
    [TopLevelName (BaseT (UintT 256)) (NONE,"a");TopLevelName (BaseT (UintT 256)) (NONE,"b")])
Proof
  EVAL_TAC >> simp[source_expr_exists_equal] >> EVAL_TAC >> simp[]
QED

Theorem source_expr_runtime_list_and_array_index:
  source_expr_witness_elaborate env
    [(["self";"a"],TopLevelName (BaseT (UintT 256)) (NONE,"a"));
     (["self";"b"],TopLevelName (BaseT (UintT 256)) (NONE,"b"))] []
    (ArrayT (BaseT (UintT 256)) (Fixed 2))
    (SX_List [SX_Attribute (SX_Name "self") "a";SX_Attribute (SX_Name "self") "b"]) =
    SC_Value (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
      (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
      [TopLevelName (BaseT (UintT 256)) (NONE,"a");TopLevelName (BaseT (UintT 256)) (NONE,"b")]) /\
  source_expr_witness_elaborate env
    [(["xs"],Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "xs");
     (["self";"i"],TopLevelName (BaseT (UintT 256)) (NONE,"i"))] []
    (BaseT (UintT 256))
    (SX_Subscript (SX_Name "xs") (SX_Attribute (SX_Name "self") "i")) =
    SC_Value (Subscript (BaseT (UintT 256))
      (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "xs")
      (TopLevelName (BaseT (UintT 256)) (NONE,"i")))
Proof
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem source_expr_intrinsic_resolved_alias:
  source_expr_elaborate 6 (env with type_defs := FEMPTY)
    [[("renamed",["alias"])]]
    [(["alias"],SR_Alias ["abi-id"]);(["abi-id"],SR_Function)] []
    [(["abi-id"],SE_Intrinsic SE_AbiEncode)] (BaseT (BytesT (Dynamic 32)))
    (SX_Call (SX_Name "renamed") [SX_Literal (SCL_Int 1)] []) =
  SC_Value (TypeBuiltin (BaseT (BytesT (Dynamic 32))) (AbiEncode T NONE)
    (TupleT [BaseT (UintT 256)]) [Literal (BaseT (UintT 256)) (IntL 1)]) /\
  source_expr_elaborate 6 (env with type_defs := FEMPTY)
    [[("abi_encode",["user"])]] [(["user"],SR_Function)] []
    [(["abi-id"],SE_Intrinsic SE_AbiEncode)] (BaseT (BytesT (Dynamic 32)))
    (SX_Call (SX_Name "abi_encode") [SX_Literal (SCL_Int 1)] []) = SC_Unsupported SCS_Call
Proof
  conj_tac >- (EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]) >> EVAL_TAC
QED

Theorem source_expr_retained_witness_names:
  MAP FST source_expr_witnesses =
    ["pow_folded_exp";"pow_negfold_base";"fold_add";"fold_pow_lit";"fold_cmp";
     "fold_not";"fold_shift";"fold_minmax";"fold_powmod";"fold_addmod";"fold_abs";
     "keccak_literal";"len_string_lit";"method_id_b4";"method_id_bytes";
     "method_id_const";"method_id_storage";"method_id_var";"enc_mid_const";
     "enc_mid_methodid_call";"enc_mid_bytes4lit";"enc_ensF_string_mid";
     "enc_ensF_uint_mid";"enc_ensure_const";"dec_unwrap_const";"ctl03_abi_method_id";
     "enc_ensT_uint_mid";"neg_lit";"pow_neglit_base";"lt_mixed_lit";"boolop_and3";
     "i12_immut_with_storage";"p29_imm_multi";"c16_const_string_in_expr";
     "c27_const_binop_fold";"rc09_abi_encode_data";"rr03_abi"]
Proof
  EVAL_TAC
QED

Theorem source_expr_witness_success_typed:
  MEM (name,runtime,constants,ty,original,SC_Value e) source_expr_witnesses ==>
  expr_type e = ty /\ well_typed_expr (source_expr_witness_env env runtime) e
Proof
  strip_tac >>
  `source_expr_witness_elaborate env runtime constants ty original = SC_Value e` by
    (mp_tac source_expr_all_retained_witness_bodies >>
     simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  gvs[source_expr_witness_elaborate_def] >>
  drule source_expr_elaborate_typed >> simp[]
QED

fun audit_source_expr_theory thy =
  let
    val exports = DB.thms thy
    fun check (name, th) =
      let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
      in
        if null (Thm.hyp th) andalso null axioms andalso
           List.all (fn s => s = "DISK_THM") oracles then ()
        else raise Fail ("source expression kernel audit failed: " ^ thy ^ "." ^ name)
      end
  in
    if null exports then raise Fail ("empty source expression theory: " ^ thy) else ();
    List.app check exports;
    print ("SOURCE_EXPR_KERNEL_CLOSED " ^ thy ^ " exports=" ^
           Int.toString (length exports) ^ "\n")
  end;

val () = List.app audit_source_expr_theory
  ["sourceExprDefs", "sourceExprCall", "sourceExprElaborate", "sourceExprProps",
   "sourceExprWitnessDefs", "sourceExprTest"];
