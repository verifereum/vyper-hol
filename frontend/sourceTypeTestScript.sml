Theory sourceTypeTest
Ancestors
  sourceTypeDefs sourceTypeResolve sourceTypeProps sourceConstAST
  sourceConstAnnotation vyperAST finite_map list
Libs
  intLib wordsLib

(* These test environments stand for independently resolved bindings. There is
   no automatic spelling-to-type fallback in the resolver. *)
Definition source_type_test_names_def:
  source_type_test_names =
    [(["i"], STI_Integer T 128); (["u"], STI_Integer F 256);
     (["b"], STI_Bool); (["d"], STI_Decimal); (["m"], STI_BytesM 7);
     (["String"], STI_Constructor STC_String);
     (["Bytes"], STI_Constructor STC_Bytes);
     (["DynArray"], STI_Constructor STC_DynArray);
     (["HashMap"], STI_Constructor STC_HashMap);
     (["public"], STI_Constructor (STC_Qualifier SCQ_Public));
     (["immutable"], STI_Constructor (STC_Qualifier SCQ_Immutable));
     (["constant"], STI_Constructor (STC_Qualifier SCQ_Constant))]
End

Theorem source_type_primitives:
  source_type_resolve FEMPTY source_type_test_names [] (SCA_Name ["i"]) =
    ST_Ok (SourceTypeResolution (Type (BaseT (IntT 128))) [] []) /\
  source_type_resolve FEMPTY source_type_test_names [] (SCA_Name ["u"]) =
    ST_Ok (SourceTypeResolution (Type (BaseT (UintT 256))) [] []) /\
  source_type_resolve FEMPTY source_type_test_names [] (SCA_Name ["b"]) =
    ST_Ok (SourceTypeResolution (Type (BaseT BoolT)) [] []) /\
  source_type_resolve FEMPTY source_type_test_names [] (SCA_Name ["d"]) =
    ST_Ok (SourceTypeResolution (Type (BaseT DecimalT)) [] []) /\
  source_type_resolve FEMPTY source_type_test_names [] (SCA_Name ["m"]) =
    ST_Ok (SourceTypeResolution (Type (BaseT (BytesT (Fixed 7)))) [] [])
Proof
  EVAL_TAC
QED

Theorem source_type_source_width_rejections:
  source_type_identity (STI_Integer T 7) = ST_Error STE_Width /\
  source_type_identity (STI_Integer F 0) = ST_Error STE_Width /\
  source_type_identity (STI_Integer F 264) = ST_Error STE_Width /\
  source_type_identity (STI_BytesM 0) = ST_Error STE_Width /\
  source_type_identity (STI_BytesM 33) = ST_Error STE_Width
Proof
  EVAL_TAC
QED

Theorem source_type_strings_and_bytes:
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_String (SCE_Binary SCB_Add (SCE_Literal (SCL_Int 2))
                                  (SCE_Literal (SCL_Int 3)))) =
    ST_Ok (SourceTypeResolution (Type (BaseT (StringT 5))) []
      [(SCE_Binary SCB_Add (SCE_Literal (SCL_Int 2))
                          (SCE_Literal (SCL_Int 3)),5)]) /\
  source_type_resolve FEMPTY source_type_test_names
    [(["N"], SC_Constant (SCV_Int 9))] (SCA_Bytes (SCE_Name ["N"])) =
    ST_Ok (SourceTypeResolution (Type (BaseT (BytesT (Dynamic 9)))) []
      [(SCE_Name ["N"],9)])
Proof
  EVAL_TAC
QED

Theorem source_type_nested_arrays:
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_DynArray (SCA_StaticArray (SCA_Name ["u"])
       (SCE_Literal (SCL_Int 3))) (SCE_Literal (SCL_Int 4))) =
    ST_Ok (SourceTypeResolution
      (Type (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 3)) (Dynamic 4))) []
      [(SCE_Literal (SCL_Int 3),3); (SCE_Literal (SCL_Int 4),4)])
Proof
  EVAL_TAC
QED

Theorem source_type_hashmap_value_types:
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_HashMap (SCA_Name ["u"])
      (SCA_HashMap (SCA_Name ["b"])
        (SCA_Bytes (SCE_Literal (SCL_Int 6))))) =
    ST_Ok (SourceTypeResolution
      (HashMapT (BaseT (UintT 256))
        (HashMapT (BaseT BoolT) (Type (BaseT (BytesT (Dynamic 6)))))) []
      [(SCE_Literal (SCL_Int 6),6)]) /\
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_HashMap (SCA_Name ["d"]) (SCA_Name ["b"])) =
    ST_Error STE_HashMapKey
Proof
  EVAL_TAC
QED

Theorem source_type_tuple_and_qualifiers:
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_Qualified SCQ_Public (SCA_Qualified SCQ_Immutable
      (SCA_Tuple [SCA_Name ["b"]; SCA_Name ["d"]; SCA_Name ["m"]]))) =
    ST_Ok (SourceTypeResolution
      (Type (TupleT [BaseT BoolT; BaseT DecimalT; BaseT (BytesT (Fixed 7))]))
      [SCQ_Public; SCQ_Immutable] []) /\
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_Qualified SCQ_Constant (SCA_Qualified SCQ_Immutable (SCA_Name ["u"]))) =
    ST_Error STE_Qualifier /\
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_StaticArray (SCA_Qualified SCQ_Public (SCA_Name ["u"]))
      (SCE_Literal (SCL_Int 3))) = ST_Error STE_NestedQualifier /\
  source_type_resolve FEMPTY source_type_test_names [] (SCA_Tuple []) =
    ST_Error STE_EmptyTuple
Proof
  EVAL_TAC
QED

Theorem source_type_hashmap_not_an_ordinary_type:
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_StaticArray (SCA_HashMap (SCA_Name ["u"]) (SCA_Name ["b"]))
      (SCE_Literal (SCL_Int 3))) = ST_Error STE_ValueType /\
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_Tuple [SCA_HashMap (SCA_Name ["u"]) (SCA_Name ["b"])]) =
    ST_Error STE_ValueType
Proof
  EVAL_TAC
QED

Theorem source_type_required_constant_outcomes:
  source_type_bound [] SCE_Dynamic = ST_Error STE_RequiredConstant /\
  source_type_bound [] (SCE_Name ["missing"]) =
    ST_Error (STE_ConstantUnsupported (SCS_UnresolvedName ["missing"])) /\
  source_type_bound [] (SCE_Binary SCB_Div (SCE_Literal (SCL_Int 1))
                                         (SCE_Literal (SCL_Int 0))) =
    ST_Error (STE_ConstantInvalid SCErr_ZeroDivisor) /\
  source_type_bound [] (SCE_Literal (SCL_Bool T)) = ST_Error STE_IntegerBound /\
  source_type_bound [] (SCE_Literal (SCL_Decimal 1 0)) = ST_Error STE_IntegerBound /\
  source_type_bound [] (SCE_Literal (SCL_Int 0)) = ST_Error STE_BoundRange /\
  source_type_bound [] (SCE_Literal (SCL_Int (-1))) = ST_Error STE_BoundRange /\
  source_type_bound [] (SCE_Literal (SCL_Int (&(2 ** 256)))) = ST_Error STE_BoundRange
Proof
  EVAL_TAC
QED

Theorem source_type_bounds_do_not_wrap:
  source_type_bound []
    (SCE_Binary SCB_Add (SCE_Literal (SCL_Int (&(2 ** 256))))
                        (SCE_Literal (SCL_Int 1))) = ST_Error STE_BoundRange /\
  source_type_resolve FEMPTY source_type_test_names []
    (SCA_StaticArray (SCA_Tuple [SCA_Name ["u"]; SCA_Name ["u"]])
      (SCE_Literal (SCL_Int (&(2 ** 256 - 1))))) = ST_Error STE_RuntimeType
Proof
  EVAL_TAC
QED

Theorem source_type_spelling_is_not_identity:
  source_type_resolve FEMPTY [] [] (SCA_Name ["uint256"]) =
    ST_Error (STE_Unresolved ["uint256"]) /\
  source_type_resolve FEMPTY [(["uint256"],STI_Bool)] [] (SCA_Name ["uint256"]) =
    ST_Ok (SourceTypeResolution (Type (BaseT BoolT)) [] []) /\
  source_type_resolve FEMPTY [(["Bytes"],STI_Bool)] []
    (SCA_Bytes (SCE_Literal (SCL_Int 8))) = ST_Error STE_Constructor
Proof
  EVAL_TAC
QED

Theorem source_type_inferred_claim_rejects_not_reinterprets:
  source_type_check_claim FEMPTY source_type_test_names []
    (SCA_StaticArray (SCA_Name ["u"]) (SCE_Literal (SCL_Int 3)))
    (Type (ArrayT (BaseT (UintT 256)) (Fixed 4))) = ST_Error STE_InferredClaim /\
  source_type_check_claim FEMPTY source_type_test_names []
    (SCA_Bytes SCE_Dynamic) (Type (BaseT (BytesT (Dynamic 32)))) =
    ST_Error STE_RequiredConstant
Proof
  EVAL_TAC
QED
