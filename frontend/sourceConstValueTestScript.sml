Theory sourceConstValueTest
Ancestors
  sourceConstValueStructuredTest
  sourceConstValueProps sourceConstValue sourceConstAST sourceConstBuiltin
  sourceConstEval vyperTypeSystem vyperAST vyperValue vyperValueOperation
  vyperTyping vyperInterpreter vyperState finite_map
Libs
  wordsLib intLib

(* Computation tests are local runtime-bridge tests, not source acceptance
   tests. In particular mathematical values have no original syntax here. *)

Theorem source_const_reify_integer_edges:
  source_const_reify FEMPTY (BaseT (UintT 8)) (SCV_Int 255) =
    SOME (Literal (BaseT (UintT 8)) (IntL 255)) /\
  source_const_reify FEMPTY (BaseT (UintT 8)) (SCV_Int 256) = NONE /\
  source_const_reify FEMPTY (BaseT (UintT 8)) (SCV_Int (-1)) = NONE /\
  source_const_reify FEMPTY (BaseT (IntT 8)) (SCV_Int (-128)) =
    SOME (Literal (BaseT (IntT 8)) (IntL (-128))) /\
  source_const_reify FEMPTY (BaseT (IntT 8)) (SCV_Int (-129)) = NONE /\
  source_const_reify FEMPTY (BaseT (IntT 8)) (SCV_Int 128) = NONE
Proof
  EVAL_TAC
QED

Theorem source_const_reify_type_well_formedness:
  well_typed_literal (BaseT (UintT 0)) (IntL 0) /\
  source_const_reify FEMPTY (BaseT (UintT 0)) (SCV_Int 0) = NONE /\
  source_const_reify FEMPTY (BaseT (UintT 257)) (SCV_Int 0) = NONE /\
  source_const_reify FEMPTY (BaseT (IntT 1)) (SCV_Int 0) = NONE /\
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 33)))
    (SCV_Bytes (REPLICATE 33 0)) = NONE
Proof
  EVAL_TAC
QED

Theorem source_const_reify_bool_and_type_mismatch:
  source_const_reify FEMPTY (BaseT BoolT) (SCV_Bool T) =
    SOME (Literal (BaseT BoolT) (BoolL T)) /\
  source_const_reify FEMPTY (BaseT (UintT 8)) (SCV_Bool T) = NONE /\
  source_const_reify FEMPTY (BaseT BoolT) (SCV_Int 1) = NONE
Proof
  EVAL_TAC
QED

Theorem source_const_reify_decimal_edges:
  source_const_reify FEMPTY (BaseT DecimalT) (SCV_Decimal (2 ** 167 - 1)) =
    SOME (Literal (BaseT DecimalT) (DecimalL (2 ** 167 - 1))) /\
  source_const_reify FEMPTY (BaseT DecimalT) (SCV_Decimal (-(2 ** 167))) =
    SOME (Literal (BaseT DecimalT) (DecimalL (-(2 ** 167)))) /\
  source_const_reify FEMPTY (BaseT DecimalT) (SCV_Decimal (2 ** 167)) = NONE /\
  source_const_reify FEMPTY (BaseT DecimalT) (SCV_Decimal (-(2 ** 167) - 1)) = NONE /\
  source_const_reify FEMPTY (BaseT DecimalT) (SCV_Decimal 10000000000) =
    SOME (Literal (BaseT DecimalT) (DecimalL 10000000000))
Proof
  EVAL_TAC
QED

Theorem source_const_reify_string_edges:
  source_const_reify FEMPTY (BaseT (StringT 3)) (SCV_String "abc") =
    SOME (Literal (BaseT (StringT 3)) (StringL "abc")) /\
  source_const_reify FEMPTY (BaseT (StringT 2)) (SCV_String "abc") = NONE /\
  source_const_reify FEMPTY (BaseT (StringT 1)) (SCV_String [CHR 128]) = NONE /\
  source_const_reify FEMPTY (BaseT (StringT 0)) (SCV_String "") =
    SOME (Literal (BaseT (StringT 0)) (StringL ""))
Proof
  EVAL_TAC
QED

Theorem source_const_reify_bytes_edges:
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 2))) (SCV_Bytes [0;255]) =
    SOME (Literal (BaseT (BytesT (Fixed 2))) (BytesL [0w;255w])) /\
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 1))) (SCV_Bytes [0;255]) = NONE /\
  source_const_reify FEMPTY (BaseT (BytesT (Dynamic 3))) (SCV_Bytes [0;255]) =
    SOME (Literal (BaseT (BytesT (Dynamic 3))) (BytesL [0w;255w])) /\
  source_const_reify FEMPTY (BaseT (BytesT (Dynamic 1))) (SCV_Bytes [0;255]) = NONE /\
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 1))) (SCV_Bytes [256]) = NONE /\
  source_const_reify FEMPTY (BaseT (BytesT (Dynamic 0))) (SCV_Bytes []) =
    SOME (Literal (BaseT (BytesT (Dynamic 0))) (BytesL []))
Proof
  EVAL_TAC
QED

Theorem source_const_reify_hex:
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 3))) (SCV_Hex "0xaB00fF") =
    SOME (Literal (BaseT (BytesT (Fixed 3))) (BytesL [171w;0w;255w])) /\
  source_const_represents (SCV_Hex "0xaB00fF") (BytesV [171w;0w;255w]) /\
  source_const_reify FEMPTY (BaseT AddressT)
    (SCV_Hex "0x0000000000000000000000000000000000000001") =
    SOME (Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [1w]))) /\
  source_const_reify FEMPTY (BaseT AddressT) (SCV_Hex "0x01") = NONE /\
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 1))) (SCV_Hex "0xgg") = NONE /\
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 1))) (SCV_Hex "0x1") = NONE /\
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 0))) (SCV_Hex "0x") = NONE
Proof
  EVAL_TAC
QED

Theorem source_const_reify_descriptor_and_aggregates_rejected:
  source_const_reify FEMPTY (BaseT (BytesT (Dynamic 32)))
    (SCV_BytesType F 32) = NONE /\
  source_const_reify FEMPTY (BaseT (BytesT (Fixed 32)))
    (SCV_BytesType T 32) = NONE /\
  source_const_reify FEMPTY (TupleT [BaseT BoolT])
    (SCV_Tuple [SCV_Bool T]) = NONE /\
  source_const_reify FEMPTY (ArrayT (BaseT BoolT) (Fixed 1))
    (SCV_List [SCV_Bool T]) = NONE /\
  source_const_reify FEMPTY (StructT (NONE,"S"))
    (SCV_Struct ["S"] [("x",SCV_Bool T)]) = NONE
Proof
  EVAL_TAC
QED

Theorem source_const_reify_execution_example:
  !cx st.
    eval_expr cx (Literal (BaseT (UintT 8)) (IntL 255)) st =
      (INL (Value (IntV 255)), st)
Proof
  simp[Once evaluate_def, return_def, evaluate_literal_def]
QED
