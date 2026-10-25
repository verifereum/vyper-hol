(* Permanent plain-EVAL coverage of PLAN 5.6 operators, conversions and
   builtin forms, including F22 exclusions. No typing/evaluator replacement. *)
Theory supportedExprFormProps
Ancestors
  supportedExprForms supportedTypes vyperAST list integer
Libs
  intLib

Definition expr_test_uint_def:
  expr_test_uint = Name (BaseT (UintT 256)) "u"
End
Definition expr_test_int_def:
  expr_test_int = Name (BaseT (IntT 256)) "i"
End
Definition expr_test_decimal_def:
  expr_test_decimal = Name (BaseT DecimalT) "d"
End

Theorem supported_arithmetic_operator_coverage:
  EVERY (\op. supported_binop op (BaseT (UintT 8)) (BaseT (UintT 8)) F F /\
              supported_binop op (BaseT (IntT 256)) (BaseT (IntT 256)) F F /\
              supported_binop op (BaseT DecimalT) (BaseT DecimalT) F F)
    [Add; Sub; Mul; Div; Mod; Lt; LtE; Gt; GtE; Min; Max] /\
  EVERY (\op. supported_binop op (BaseT (UintT 8)) (BaseT (UintT 8)) F F /\
              supported_binop op (BaseT (IntT 256)) (BaseT (IntT 256)) F F /\
              ~supported_binop op (BaseT DecimalT) (BaseT DecimalT) F F)
    [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
  ~supported_binop Add (BaseT BoolT) (BaseT BoolT) F F /\
  ~supported_binop Add (BaseT (UintT 7)) (BaseT (UintT 7)) F F
Proof
  EVAL_TAC
QED

Theorem supported_bitwise_comparison_operator_coverage:
  EVERY (\op. supported_binop op (BaseT (IntT 8)) (BaseT (IntT 8)) F F /\
              supported_binop op (BaseT BoolT) (BaseT BoolT) F F /\
              ~supported_binop op (BaseT DecimalT) (BaseT DecimalT) F F)
    [And; Or; XOr] /\
  EVERY (\op. supported_binop op (BaseT AddressT) (BaseT AddressT) F F /\
              supported_binop op (BaseT (BytesT (Fixed 32)))
                (BaseT (BytesT (Fixed 32))) F F /\
              ~supported_binop op (BaseT (StringT 32)) (BaseT (StringT 32)) F F /\
              ~supported_binop op (BaseT (BytesT (Dynamic 32)))
                (BaseT (BytesT (Dynamic 32))) F F /\
              ~supported_binop op (BaseT (BytesT (Fixed 20)))
                (BaseT (BytesT (Fixed 20))) F F) [Eq; NotEq] /\
  EVERY (\op. ~supported_binop op (BaseT (UintT 256))
                (BaseT (UintT 256)) T T) [In; NotIn; ExpMod]
Proof
  EVAL_TAC
QED

Theorem supported_power_shift_counterexamples:
  supported_builtin_form [] (BaseT (UintT 256)) (Bop Exp)
    [expr_test_uint; Literal (BaseT (UintT 256)) (IntL 0)] /\
  supported_builtin_form [] (BaseT (IntT 256)) (Bop Exp)
    [Literal (BaseT (IntT 256)) (IntL (~2)); expr_test_int] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) (Bop Exp)
    [expr_test_uint; expr_test_uint] /\
  ~supported_builtin_form [] (BaseT (IntT 256)) (Bop Exp)
    [expr_test_int; Literal (BaseT (IntT 256)) (IntL (~1))] /\
  ~supported_builtin_form [] (BaseT DecimalT) (Bop Exp)
    [Literal (BaseT DecimalT) (IntL 2); expr_test_decimal] /\
  supported_binop ShR (BaseT (IntT 8)) (BaseT (UintT 8)) F F /\
  supported_binop ShL (BaseT (IntT 256)) (BaseT (UintT 8)) F F /\
  supported_binop ShL (BaseT (UintT 256)) (BaseT (UintT 256)) F F /\
  ~supported_binop ShL (BaseT (UintT 8)) (BaseT (UintT 8)) F F /\
  ~supported_binop ShL (BaseT (IntT 256)) (BaseT (IntT 8)) F F /\
  ~supported_binop ShR (BaseT (IntT 8)) (BaseT (IntT 8)) F F /\
  ~supported_binop ShR (BaseT (UintT 8)) (BaseT (UintT 7)) F F /\
  ~supported_builtin_form [] (BaseT (UintT 256)) (Bop Add) [expr_test_uint]
Proof
  EVAL_TAC
QED

Theorem supported_conversion_whitelist_coverage:
  EVERY (\(src,dst). supported_conversion src dst)
    [(BaseT (UintT 8), BaseT (IntT 256));
     (BaseT (IntT 8), BaseT (UintT 256));
     (BaseT (UintT 8), BaseT (UintT 256));
     (BaseT (IntT 256), BaseT (IntT 8));
     (BaseT BoolT, BaseT (IntT 8));
     (BaseT BoolT, BaseT (UintT 8));
     (BaseT (IntT 8), BaseT BoolT);
     (BaseT (UintT 8), BaseT BoolT);
     (BaseT (BytesT (Fixed 1)), BaseT BoolT);
     (BaseT (BytesT (Dynamic 32)), BaseT BoolT);
     (BaseT (BytesT (Dynamic 32)), BaseT (UintT 8));
     (BaseT AddressT, BaseT (UintT 256));
     (BaseT (IntT 8), BaseT AddressT);
     (BaseT (UintT 8), BaseT AddressT);
     (BaseT (BytesT (Fixed 1)), BaseT (UintT 8));
     (BaseT (BytesT (Fixed 32)), BaseT (IntT 8));
     (BaseT (BytesT (Fixed 1)), BaseT AddressT);
     (BaseT (BytesT (Fixed 1)), BaseT DecimalT);
     (BaseT (BytesT (Fixed 1)), BaseT (BytesT (Fixed 32)));
     (BaseT (IntT 8), BaseT (BytesT (Fixed 32)));
     (BaseT (UintT 8), BaseT (BytesT (Fixed 32)));
     (BaseT (UintT 256), BaseT DecimalT);
     (BaseT (IntT 128), BaseT DecimalT);
     (BaseT DecimalT, BaseT (IntT 8));
     (BaseT DecimalT, BaseT (UintT 8))]
Proof
  EVAL_TAC
QED

Theorem supported_conversion_exclusion_coverage:
  EVERY (\(src,dst). ~supported_conversion src dst)
    [(BaseT (BytesT (Dynamic 33)), BaseT BoolT);
     (BaseT (BytesT (Dynamic 33)), BaseT (UintT 256));
     (BaseT (BytesT (Dynamic 32)), BaseT (IntT 256));
     (BaseT (BytesT (Fixed 31)), BaseT (IntT 256));
     (BaseT (UintT 256), BaseT (BytesT (Fixed 31)));
     (BaseT (IntT 136), BaseT DecimalT);
     (BaseT (IntT 134), BaseT DecimalT);
     (BaseT (IntT 256), BaseT DecimalT);
     (BaseT (StringT 32), BaseT (BytesT (Dynamic 32)));
     (BaseT (BytesT (Dynamic 32)), BaseT (StringT 32));
     (BaseT AddressT, BaseT (IntT 256));
     (BaseT BoolT, BaseT DecimalT);
     (BaseT DecimalT, BaseT AddressT);
     (BaseT (BytesT (Fixed 20)), BaseT BoolT);
     (BaseT (BytesT (Fixed 1)), BaseT (BytesT (Fixed 20)));
     (BaseT (UintT 7), BaseT (UintT 8));
     (FlagT (NONE,"flag"), BaseT (UintT 256))]
Proof
  EVAL_TAC
QED

Theorem supported_unary_modular_builtin_coverage:
  supported_builtin_form [] (BaseT BoolT) Not [expr_test_uint] /\
  supported_builtin_form [] (BaseT (UintT 256)) Not [expr_test_uint] /\
  ~supported_builtin_form [] (BaseT (UintT 8)) Not [expr_test_uint] /\
  supported_builtin_form [] (BaseT (IntT 8)) Neg [expr_test_int] /\
  supported_builtin_form [] (BaseT DecimalT) Neg [expr_test_decimal] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) Neg [expr_test_uint] /\
  supported_builtin_form [] (BaseT (IntT 256)) Abs [expr_test_int] /\
  ~supported_builtin_form [] (BaseT (IntT 8)) Abs [expr_test_int] /\
  supported_builtin_form [] (BaseT (UintT 256)) (AsWeiValue Ether) [expr_test_uint] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) (AsWeiValue Wei) [expr_test_int] /\
  supported_builtin_form [] (BaseT (UintT 256)) AddMod
    [expr_test_uint; expr_test_uint; expr_test_uint] /\
  supported_builtin_form [] (BaseT (UintT 256)) MulMod
    [expr_test_uint; expr_test_uint; expr_test_uint] /\
  supported_builtin_form [] (BaseT (UintT 256)) PowMod256
    [expr_test_uint; expr_test_uint] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) AddMod
    [expr_test_uint; expr_test_int; expr_test_uint] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) PowMod256
    [expr_test_uint; expr_test_int]
Proof
  EVAL_TAC
QED

Theorem supported_environment_crypto_builtin_coverage:
  EVERY (\item. supported_builtin_form [] (BaseT (UintT 256)) (Env item) [])
    [Sender; SelfAddr; ValueSent; TimeStamp; BlockNumber; BlobBaseFee; GasPrice;
     PrevHash; ChainId; Coinbase; GasLimit; BaseFee; PrevRandao; TxOrigin] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) (Env MsgGas) [] /\
  EVERY (\item. supported_builtin_form [] (BaseT (UintT 256))
    (Acc item) [expr_test_uint]) [Address; Balance; Codehash; Codesize; IsContract] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) (Acc Code) [expr_test_uint] /\
  EVERY (\blt. supported_builtin_form [] (BaseT (UintT 256)) blt [expr_test_uint])
    [BlockHash; BlobHash] /\
  supported_builtin_form [] (BaseT AddressT) ECRecover
    [expr_test_uint; expr_test_uint; expr_test_uint; expr_test_uint] /\
  EVERY (\blt. supported_builtin_form [] (ArrayT (BaseT (UintT 256)) (Fixed 2))
    blt [expr_test_uint; expr_test_uint]) [ECAdd; ECMul]
Proof
  EVAL_TAC
QED

Theorem supported_builtin_exclusion_coverage:
  EVERY (\blt. ~supported_builtin_form [] (BaseT (UintT 256)) blt [expr_test_uint])
    [Len; Keccak256; Sha256; Concat 32; Slice 32; Ceil; Floor; MethodId;
     MakeArray NONE (Dynamic 1)] /\
  ~supported_builtin_form [] (TupleT []) (MakeArray NONE (Fixed 0)) [] /\
  supported_builtin_form [] (TupleT [BaseT (UintT 256)])
    (MakeArray NONE (Fixed 1)) [expr_test_uint] /\
  EVERY (\blt. ~supported_builtin_form [] (BaseT (UintT 256)) blt [])
    [Not; Neg; Abs; AsWeiValue Wei; AddMod; MulMod; PowMod256; Bop Add;
     Acc Balance; BlockHash; BlobHash; ECRecover; ECAdd; ECMul] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) (Env Sender) [expr_test_uint] /\
  ~supported_builtin_form [] (BaseT (UintT 256)) ECRecover
    [expr_test_uint; expr_test_uint; expr_test_uint] /\
  supported_builtin_form [] (BaseT (StringT 78)) (Uint2Str 78) [expr_test_uint] /\
  ~supported_builtin_form [] (BaseT (StringT 78)) (Uint2Str 78) [expr_test_int] /\
  ~supported_builtin_form [] (BaseT (StringT 78)) (Uint2Str 78) [] /\
  supported_builtin_form [] (BaseT (BytesT (Dynamic 4))) (CalldataSlice 4)
    [expr_test_uint] /\
  ~supported_builtin_form [] (BaseT (BytesT (Dynamic 4))) (CalldataSlice 4) []
Proof
  EVAL_TAC
QED

Theorem supported_memory_construction_forms:
  supported_builtin_form [] (ArrayT (BaseT (UintT 256)) (Dynamic 3))
    (MakeArray (SOME (BaseT (UintT 256))) (Dynamic 3)) [expr_test_uint] /\
  supported_builtin_form [] (ArrayT (BaseT (UintT 256)) (Fixed 1))
    (MakeArray (SOME (BaseT (UintT 256))) (Fixed 1)) [expr_test_uint] /\
  supported_type_builtin_form [] (BaseT (StringT 10)) Empty (BaseT (StringT 10)) [] /\
  ~supported_type_builtin_form [] (TupleT [TupleT [BaseT (UintT 8)]]) Empty
    (TupleT [TupleT [BaseT (UintT 8)]]) [] /\
  ~supported_type_builtin_form [] (BaseT (UintT 8)) Empty (BaseT (UintT 16)) []
Proof
  EVAL_TAC
QED

Theorem supported_type_builtin_coverage:
  supported_type_builtin_form [] (BaseT (UintT 8)) Empty (BaseT (UintT 8)) [] /\
  supported_type_builtin_form [] (TupleT [BaseT (UintT 8)]) Empty
    (TupleT [BaseT (UintT 8)]) [] /\
  supported_type_builtin_form [] (BaseT (IntT 8)) MaxValue (BaseT (IntT 8)) [] /\
  supported_type_builtin_form [] (BaseT DecimalT) MinValue (BaseT DecimalT) [] /\
  supported_type_builtin_form [] (BaseT DecimalT) Epsilon (BaseT DecimalT) [] /\
  ~supported_type_builtin_form [] (BaseT (UintT 256)) Epsilon (BaseT (UintT 256)) [] /\
  ~supported_type_builtin_form [] (BaseT BoolT) MaxValue (BaseT BoolT) [] /\
  ~supported_type_builtin_form [] (BaseT AddressT) MinValue (BaseT AddressT) [] /\
  supported_type_builtin_form [] (BaseT (IntT 8)) Convert (BaseT (IntT 8)) [expr_test_uint] /\
  ~supported_type_builtin_form [] (BaseT (IntT 8)) Convert (BaseT (IntT 8)) [] /\
  ~supported_type_builtin_form [] (BaseT (IntT 8)) Convert (BaseT (UintT 8)) [expr_test_uint] /\
  ~supported_type_builtin_form [] (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
    [expr_test_uint; expr_test_uint] /\
  EVERY (\blt. ~supported_type_builtin_form [] (BaseT (UintT 8)) blt
    (BaseT (UintT 8)) [expr_test_uint]) [Empty; MaxValue; MinValue; Epsilon]
Proof
  EVAL_TAC
QED

Theorem supported_abi_forms_coverage:
  supported_type_builtin_form [] (BaseT (BytesT (Dynamic 100)))
    (AbiEncode F (SOME [0w; 1w; 2w; 3w]))
    (TupleT [TupleT [BaseT (UintT 256)]]) [expr_test_uint] /\
  ~supported_type_builtin_form [] (BaseT (BytesT (Dynamic 100)))
    (AbiEncode F NONE) (TupleT [TupleT [BaseT (UintT 256)]]) [expr_test_uint] /\
  ~supported_type_builtin_form [] (BaseT (BytesT (Dynamic 100)))
    (AbiEncode T (SOME [0w; 1w; 2w; 3w]))
    (TupleT [TupleT [BaseT (UintT 256)]]) [expr_test_uint] /\
  ~supported_type_builtin_form [] (BaseT (BytesT (Dynamic 100)))
    (AbiEncode F (SOME [0w; 1w; 2w]))
    (TupleT [TupleT [BaseT (UintT 256)]]) [expr_test_uint] /\
  ~supported_type_builtin_form [] (BaseT (BytesT (Dynamic 100)))
    (AbiEncode F (SOME [0w; 1w; 2w; 3w]))
    (TupleT [BaseT (UintT 256)]) [expr_test_uint] /\
  ~supported_type_builtin_form [] (BaseT (BytesT (Dynamic 100)))
    (AbiEncode F (SOME [0w; 1w; 2w; 3w]))
    (TupleT [TupleT [BaseT (UintT 256)]; TupleT [BaseT (UintT 256)]])
    [expr_test_uint; expr_test_uint] /\
  supported_type_builtin_form [] (TupleT [BaseT (UintT 256); BaseT (StringT 32)])
    (AbiDecode F) (TupleT [BaseT (UintT 256); BaseT (StringT 32)]) [expr_test_uint] /\
  ~supported_type_builtin_form [] (TupleT [BaseT (UintT 256); BaseT (StringT 32)])
    (AbiDecode T) (TupleT [BaseT (UintT 256); BaseT (StringT 32)]) [expr_test_uint] /\
  ~supported_type_builtin_form [] (TupleT [BaseT (UintT 256)]) (AbiDecode F)
    (TupleT [BaseT (UintT 256)]) [expr_test_uint] /\
  ~supported_type_builtin_form [] (TupleT []) (AbiDecode F) (TupleT []) [expr_test_uint] /\
  ~supported_type_builtin_form [] (TupleT [TupleT [BaseT (UintT 256)]; BaseT (UintT 256)])
    (AbiDecode F) (TupleT [TupleT [BaseT (UintT 256)]; BaseT (UintT 256)]) [expr_test_uint]
Proof
  EVAL_TAC
QED
