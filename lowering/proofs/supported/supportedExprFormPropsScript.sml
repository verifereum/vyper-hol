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
              supported_binop op (BaseT (IntT 256)) (BaseT (IntT 256)) F F)
    [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv]
Proof
  EVAL_TAC
QED

(* Conversion support follows the checker, including formerly excluded pairs. *)
Theorem supported_convert_checker_domain:
  supported_type_builtin_form tops ty Convert target [a] <=>
    ty = target /\ valid_conversion (expr_type a) ty
Proof
  simp[supported_type_builtin_form_def]
QED

Theorem conversion_width_boundary_acceptance:
  EVERY (\(src,dst). valid_conversion src dst)
    [(BaseT (UintT 8), BaseT (BytesT (Fixed 1)));
     (BaseT (IntT 128), BaseT (BytesT (Fixed 16)));
     (BaseT (BytesT (Dynamic 32)), BaseT (IntT 8));
     (BaseT (BytesT (Fixed 1)), BaseT (IntT 256));
     (BaseT (BytesT (Dynamic 4)), BaseT (BytesT (Fixed 4)));
     (BaseT (BytesT (Dynamic 8)), BaseT (BytesT (Dynamic 4)));
     (BaseT (StringT 8), BaseT (StringT 4));
     (BaseT (BytesT (Fixed 4)), BaseT (BytesT (Fixed 8)));
     (BaseT (StringT 32), BaseT (BytesT (Dynamic 32)));
     (BaseT (BytesT (Fixed 20)), BaseT BoolT)]
Proof
  EVAL_TAC
QED

Theorem conversion_width_boundary_rejection:
  EVERY (\(src,dst). ~valid_conversion src dst)
    [(BaseT (UintT 256), BaseT (BytesT (Fixed 4)));
     (BaseT (IntT 16), BaseT (BytesT (Fixed 1)));
     (BaseT (BytesT (Dynamic 33)), BaseT BoolT);
     (BaseT (BytesT (Dynamic 33)), BaseT (UintT 256));
     (BaseT (BytesT (Dynamic 33)), BaseT (IntT 256));
     (BaseT (BytesT (Dynamic 33)), BaseT AddressT);
     (BaseT (BytesT (Dynamic 33)), BaseT DecimalT);
     (BaseT (BytesT (Dynamic 8)), BaseT (BytesT (Fixed 4)));
     (BaseT (StringT 4), BaseT (BytesT (Fixed 4)));
     (BaseT (StringT 8), BaseT (BytesT (Fixed 4)));
     (BaseT (BytesT (Dynamic 4)), BaseT (BytesT (Dynamic 4)));
     (BaseT (BytesT (Dynamic 4)), BaseT (BytesT (Dynamic 8)));
     (BaseT (StringT 4), BaseT (StringT 8));
     (BaseT (BytesT (Fixed 4)), BaseT (BytesT (Fixed 4)));
     (BaseT (UintT 256), BaseT (BytesT (Dynamic 32)));
     (BaseT (BytesT (Fixed 4)), BaseT (BytesT (Dynamic 4)));
     (BaseT (BytesT (Fixed 4)), BaseT (StringT 4))]
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
  supported_type_builtin_form [] (BaseT (UintT 256)) Extract32 (BaseT (UintT 256))
    [Name (BaseT (BytesT (Dynamic 64))) "data"; expr_test_uint] /\
  EVERY (\blt. ~supported_type_builtin_form [] (BaseT (UintT 8)) blt
    (BaseT (UintT 8)) [expr_test_uint]) [Empty; MaxValue; MinValue; Epsilon]
Proof
  EVAL_TAC
QED

