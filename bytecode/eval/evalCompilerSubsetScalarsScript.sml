(*
 * Evaluator-small compiler subset fixtures for scalar types and operations.
 *
 * Each *_program definition corresponds exactly to the same-stem Vyper source
 * under bytecode/python-o1-no-asm-opt-sources/.  The original six broad
 * candidates are intentionally split so bytecode parity can evaluate one
 * narrow module at a time.
 *)

Theory evalCompilerSubsetScalars
Ancestors evalCompiler

(* ===== Internal fixture constructors ===== *)

Definition scalar_noop_fn_def:
  scalar_noop_fn name args =
    FunctionDecl External Nonpayable F F name args ([] : expr list) NoneT [Pass]
End

Definition scalar_literal_fn_def:
  scalar_literal_fn name ty lit =
    FunctionDecl External Pure F F name
      ([] : (string # type) list) ([] : expr list) ty
      [Return (SOME (Literal ty lit))]
End

Definition scalar_binary_bop_fn_def:
  scalar_binary_bop_fn name left_ty right_ty result_ty operation =
    FunctionDecl External Pure F F name
      [("a", left_ty); ("b", right_ty)] ([] : expr list) result_ty
      [Return (SOME (Builtin result_ty (Bop operation)
         [Name left_ty "a"; Name right_ty "b"]))]
End

Definition scalar_unary_builtin_fn_def:
  scalar_unary_builtin_fn name arg_ty result_ty operation =
    FunctionDecl External Pure F F name
      [("a", arg_ty)] ([] : expr list) result_ty
      [Return (SOME (Builtin result_ty operation [Name arg_ty "a"]))]
End

Definition scalar_type_builtin0_fn_def:
  scalar_type_builtin0_fn name ty operation =
    FunctionDecl External Pure F F name
      ([] : (string # type) list) ([] : expr list) ty
      [Return (SOME (TypeBuiltin ty operation ty ([] : expr list)))]
End

Definition scalar_convert_fn_def:
  scalar_convert_fn name source_ty target_ty =
    FunctionDecl External Pure F F name
      [("x", source_ty)] ([] : expr list) target_ty
      [Return (SOME (TypeBuiltin target_ty Convert target_ty
         [Name source_ty "x"]))]
End

Definition scalar_wei_fn_def:
  scalar_wei_fn name denomination =
    FunctionDecl External Pure F F name
      [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
      [Return (SOME (Builtin (BaseT (UintT 256))
         (AsWeiValue denomination) [Name (BaseT (UintT 256)) "x"]))]
End

Definition scalar_modular3_fn_def:
  scalar_modular3_fn name operation =
    FunctionDecl External Pure F F name
      [("a", BaseT (UintT 256)); ("b", BaseT (UintT 256));
       ("m", BaseT (UintT 256))]
      ([] : expr list) (BaseT (UintT 256))
      [Return (SOME (Builtin (BaseT (UintT 256)) operation
         [Name (BaseT (UintT 256)) "a";
          Name (BaseT (UintT 256)) "b";
          Name (BaseT (UintT 256)) "m"]))]
End

(* ===== Integer widths ===== *)

Definition scalar_widths_uint_low_program_def:
  scalar_widths_uint_low_program =
    [scalar_noop_fn "uints_8_64"
       [("a", BaseT (UintT 8)); ("b", BaseT (UintT 16));
        ("c", BaseT (UintT 24)); ("d", BaseT (UintT 32));
        ("e", BaseT (UintT 40)); ("f", BaseT (UintT 48));
        ("g", BaseT (UintT 56)); ("h", BaseT (UintT 64))];
     scalar_noop_fn "uints_72_128"
       [("a", BaseT (UintT 72)); ("b", BaseT (UintT 80));
        ("c", BaseT (UintT 88)); ("d", BaseT (UintT 96));
        ("e", BaseT (UintT 104)); ("f", BaseT (UintT 112));
        ("g", BaseT (UintT 120)); ("h", BaseT (UintT 128))]]
End

Definition scalar_widths_uint_high_program_def:
  scalar_widths_uint_high_program =
    [scalar_noop_fn "uints_136_192"
       [("a", BaseT (UintT 136)); ("b", BaseT (UintT 144));
        ("c", BaseT (UintT 152)); ("d", BaseT (UintT 160));
        ("e", BaseT (UintT 168)); ("f", BaseT (UintT 176));
        ("g", BaseT (UintT 184)); ("h", BaseT (UintT 192))];
     scalar_noop_fn "uints_200_256"
       [("a", BaseT (UintT 200)); ("b", BaseT (UintT 208));
        ("c", BaseT (UintT 216)); ("d", BaseT (UintT 224));
        ("e", BaseT (UintT 232)); ("f", BaseT (UintT 240));
        ("g", BaseT (UintT 248)); ("h", BaseT (UintT 256))]]
End

Definition scalar_widths_int_low_program_def:
  scalar_widths_int_low_program =
    [scalar_noop_fn "ints_8_64"
       [("a", BaseT (IntT 8)); ("b", BaseT (IntT 16));
        ("c", BaseT (IntT 24)); ("d", BaseT (IntT 32));
        ("e", BaseT (IntT 40)); ("f", BaseT (IntT 48));
        ("g", BaseT (IntT 56)); ("h", BaseT (IntT 64))];
     scalar_noop_fn "ints_72_128"
       [("a", BaseT (IntT 72)); ("b", BaseT (IntT 80));
        ("c", BaseT (IntT 88)); ("d", BaseT (IntT 96));
        ("e", BaseT (IntT 104)); ("f", BaseT (IntT 112));
        ("g", BaseT (IntT 120)); ("h", BaseT (IntT 128))]]
End

Definition scalar_widths_int_high_program_def:
  scalar_widths_int_high_program =
    [scalar_noop_fn "ints_136_192"
       [("a", BaseT (IntT 136)); ("b", BaseT (IntT 144));
        ("c", BaseT (IntT 152)); ("d", BaseT (IntT 160));
        ("e", BaseT (IntT 168)); ("f", BaseT (IntT 176));
        ("g", BaseT (IntT 184)); ("h", BaseT (IntT 192))];
     scalar_noop_fn "ints_200_256"
       [("a", BaseT (IntT 200)); ("b", BaseT (IntT 208));
        ("c", BaseT (IntT 216)); ("d", BaseT (IntT 224));
        ("e", BaseT (IntT 232)); ("f", BaseT (IntT 240));
        ("g", BaseT (IntT 248)); ("h", BaseT (IntT 256))]]
End

(* ===== Scalar literals ===== *)

Definition scalar_literals_bool_program_def:
  scalar_literals_bool_program =
    [scalar_literal_fn "bool_true" (BaseT BoolT) (BoolL T);
     scalar_literal_fn "bool_false" (BaseT BoolT) (BoolL F)]
End

Definition scalar_literals_int_small_program_def:
  scalar_literals_int_small_program =
    [scalar_literal_fn "uint8_max_literal" (BaseT (UintT 8)) (IntL 255);
     scalar_literal_fn "int8_min_literal" (BaseT (IntT 8)) (IntL (~128))]
End

Definition scalar_literals_int_wide_program_def:
  scalar_literals_int_wide_program =
    [scalar_literal_fn "uint256_max_literal" (BaseT (UintT 256))
       (IntL 115792089237316195423570985008687907853269984665640564039457584007913129639935);
     scalar_literal_fn "int256_min_literal" (BaseT (IntT 256))
       (IntL (~57896044618658097711785492504343953926634992332820282019728792003956564819968))]
End

Definition scalar_literal_decimal_program_def:
  scalar_literal_decimal_program =
    [scalar_literal_fn "decimal_literal" (BaseT DecimalT)
       (DecimalL (~123456789012))]
End

Definition scalar_literals_bytes_program_def:
  scalar_literals_bytes_program =
    [scalar_literal_fn "address_literal" (BaseT AddressT)
       (BytesL [0x00w; 0x00w; 0x00w; 0x00w; 0x00w;
                0x00w; 0x00w; 0x00w; 0x00w; 0x00w;
                0x00w; 0x00w; 0x00w; 0x00w; 0x00w;
                0x00w; 0x00w; 0x00w; 0x00w; 0x01w]);
     scalar_literal_fn "bytes1_literal" (BaseT (BytesT (Fixed 1)))
       (BytesL [0xABw]);
     scalar_literal_fn "bytes32_literal" (BaseT (BytesT (Fixed 32)))
       (BytesL [0x00w; 0x01w; 0x02w; 0x03w; 0x04w; 0x05w; 0x06w; 0x07w;
                0x08w; 0x09w; 0x0Aw; 0x0Bw; 0x0Cw; 0x0Dw; 0x0Ew; 0x0Fw;
                0x10w; 0x11w; 0x12w; 0x13w; 0x14w; 0x15w; 0x16w; 0x17w;
                0x18w; 0x19w; 0x1Aw; 0x1Bw; 0x1Cw; 0x1Dw; 0x1Ew; 0x1Fw])]
End

(* ===== Arithmetic ===== *)

Definition scalar_arith_uint_program_def:
  scalar_arith_uint_program =
    [scalar_binary_bop_fn "add_u256" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) Add;
     scalar_binary_bop_fn "sub_u256" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) Sub;
     scalar_binary_bop_fn "mul_u256" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) Mul;
     scalar_binary_bop_fn "div_u256" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) Div;
     scalar_binary_bop_fn "mod_u256" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) Mod]
End

Definition scalar_arith_pow_program_def:
  scalar_arith_pow_program =
    [FunctionDecl External Pure F F "pow_u8"
       [("a", BaseT (UintT 8))] ([] : expr list) (BaseT (UintT 8))
       [Return (SOME (Builtin (BaseT (UintT 8)) (Bop Exp)
          [Name (BaseT (UintT 8)) "a";
           Literal (BaseT (UintT 8)) (IntL 3)]))]]
End

Definition scalar_arith_pow_base_program_def:
  scalar_arith_pow_base_program =
    [FunctionDecl External Pure F F "pow_base_u8"
       [("exponent", BaseT (UintT 8))] ([] : expr list) (BaseT (UintT 8))
       [Return (SOME (Builtin (BaseT (UintT 8)) (Bop Exp)
          [Literal (BaseT (UintT 8)) (IntL 3);
           Name (BaseT (UintT 8)) "exponent"]))]]
End

Definition scalar_arith_int_program_def:
  scalar_arith_int_program =
    [scalar_binary_bop_fn "add_i256" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT (IntT 256)) Add;
     scalar_binary_bop_fn "sub_i256" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT (IntT 256)) Sub;
     scalar_binary_bop_fn "mul_i256" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT (IntT 256)) Mul;
     scalar_binary_bop_fn "div_i256" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT (IntT 256)) Div;
     scalar_binary_bop_fn "mod_i256" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT (IntT 256)) Mod]
End

Definition scalar_arith_decimal_program_def:
  scalar_arith_decimal_program =
    [scalar_binary_bop_fn "add_decimal" (BaseT DecimalT)
       (BaseT DecimalT) (BaseT DecimalT) Add]
End

Definition scalar_arith_decimal_sub_program_def:
  scalar_arith_decimal_sub_program =
    [scalar_binary_bop_fn "sub_decimal" (BaseT DecimalT)
       (BaseT DecimalT) (BaseT DecimalT) Sub]
End

Definition scalar_arith_decimal_mul_program_def:
  scalar_arith_decimal_mul_program =
    [scalar_binary_bop_fn "mul_decimal" (BaseT DecimalT)
       (BaseT DecimalT) (BaseT DecimalT) Mul]
End

Definition scalar_arith_decimal_div_program_def:
  scalar_arith_decimal_div_program =
    [scalar_binary_bop_fn "div_decimal" (BaseT DecimalT)
       (BaseT DecimalT) (BaseT DecimalT) Div]
End

Definition scalar_arith_unsafe_uint_program_def:
  scalar_arith_unsafe_uint_program =
    [scalar_binary_bop_fn "unsafe_add_u8" (BaseT (UintT 8))
       (BaseT (UintT 8)) (BaseT (UintT 8)) UnsafeAdd;
     scalar_binary_bop_fn "unsafe_sub_u8" (BaseT (UintT 8))
       (BaseT (UintT 8)) (BaseT (UintT 8)) UnsafeSub;
     scalar_binary_bop_fn "unsafe_mul_u8" (BaseT (UintT 8))
       (BaseT (UintT 8)) (BaseT (UintT 8)) UnsafeMul;
     scalar_binary_bop_fn "unsafe_div_u8" (BaseT (UintT 8))
       (BaseT (UintT 8)) (BaseT (UintT 8)) UnsafeDiv]
End

Definition scalar_arith_unsafe_int_program_def:
  scalar_arith_unsafe_int_program =
    [scalar_binary_bop_fn "unsafe_div_i256" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT (IntT 256)) UnsafeDiv]
End

(* ===== Bitwise, comparison, min/max, and unary operations ===== *)

Definition scalar_bits_program_def:
  scalar_bits_program =
    [scalar_binary_bop_fn "bit_and" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) And;
     scalar_binary_bop_fn "bit_or" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) Or;
     scalar_binary_bop_fn "bit_xor" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) XOr]
End

Definition scalar_shifts_program_def:
  scalar_shifts_program =
    [scalar_binary_bop_fn "shift_left" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) ShL;
     scalar_binary_bop_fn "shift_right_unsigned" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) ShR;
     scalar_binary_bop_fn "shift_right_signed" (BaseT (IntT 256))
       (BaseT (UintT 256)) (BaseT (IntT 256)) ShR]
End

Definition scalar_compare_eq_program_def:
  scalar_compare_eq_program =
    [scalar_binary_bop_fn "equal" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT BoolT) Eq;
     scalar_binary_bop_fn "not_equal" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT BoolT) NotEq]
End

Definition scalar_compare_order_uint_program_def:
  scalar_compare_order_uint_program =
    [scalar_binary_bop_fn "less_than" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT BoolT) Lt;
     scalar_binary_bop_fn "less_equal" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT BoolT) LtE;
     scalar_binary_bop_fn "greater_than" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT BoolT) Gt;
     scalar_binary_bop_fn "greater_equal" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT BoolT) GtE]
End

Definition scalar_compare_order_int_program_def:
  scalar_compare_order_int_program =
    [scalar_binary_bop_fn "less_than_signed" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT BoolT) Lt;
     scalar_binary_bop_fn "greater_than_signed" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT BoolT) Gt]
End

Definition scalar_minmax_uint_program_def:
  scalar_minmax_uint_program =
    [scalar_binary_bop_fn "min_unsigned" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) Min;
     scalar_binary_bop_fn "max_unsigned" (BaseT (UintT 256))
       (BaseT (UintT 256)) (BaseT (UintT 256)) Max]
End

Definition scalar_minmax_int_program_def:
  scalar_minmax_int_program =
    [scalar_binary_bop_fn "min_signed" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT (IntT 256)) Min;
     scalar_binary_bop_fn "max_signed" (BaseT (IntT 256))
       (BaseT (IntT 256)) (BaseT (IntT 256)) Max]
End

Definition scalar_unary_program_def:
  scalar_unary_program =
    [scalar_unary_builtin_fn "logical_not" (BaseT BoolT) (BaseT BoolT) Not;
     scalar_unary_builtin_fn "bitwise_not" (BaseT (UintT 256))
       (BaseT (UintT 256)) Not;
     scalar_unary_builtin_fn "negate" (BaseT (IntT 256))
       (BaseT (IntT 256)) Neg;
     scalar_unary_builtin_fn "absolute" (BaseT (IntT 256))
       (BaseT (IntT 256)) Abs]
End

(* ===== Type builtins and conversions ===== *)

Definition scalar_empty_program_def:
  scalar_empty_program =
    [scalar_type_builtin0_fn "empty_uint" (BaseT (UintT 256)) Empty;
     scalar_type_builtin0_fn "empty_bool" (BaseT BoolT) Empty;
     scalar_type_builtin0_fn "empty_decimal" (BaseT DecimalT) Empty;
     scalar_type_builtin0_fn "empty_address" (BaseT AddressT) Empty;
     scalar_type_builtin0_fn "get_empty_bytes32"
       (BaseT (BytesT (Fixed 32))) Empty]
End

Definition scalar_decimal_bounds_program_def:
  scalar_decimal_bounds_program =
    [scalar_type_builtin0_fn "epsilon_decimal" (BaseT DecimalT) Epsilon]
End

Definition scalar_decimal_max_program_def:
  scalar_decimal_max_program =
    [scalar_type_builtin0_fn "get_max_decimal" (BaseT DecimalT) MaxValue]
End

Definition scalar_decimal_min_program_def:
  scalar_decimal_min_program =
    [scalar_type_builtin0_fn "get_min_decimal" (BaseT DecimalT) MinValue]
End

Definition scalar_integer_bounds_program_def:
  scalar_integer_bounds_program =
    [scalar_type_builtin0_fn "max_uint8" (BaseT (UintT 8)) MaxValue]
End

Definition scalar_integer_min_uint8_program_def:
  scalar_integer_min_uint8_program =
    [scalar_type_builtin0_fn "min_uint8" (BaseT (UintT 8)) MinValue]
End

Definition scalar_integer_max_int256_program_def:
  scalar_integer_max_int256_program =
    [scalar_type_builtin0_fn "max_int256" (BaseT (IntT 256)) MaxValue]
End

Definition scalar_integer_min_int256_program_def:
  scalar_integer_min_int256_program =
    [scalar_type_builtin0_fn "min_int256" (BaseT (IntT 256)) MinValue]
End

Definition scalar_convert_integer_program_def:
  scalar_convert_integer_program =
    [scalar_convert_fn "uint_to_uint" (BaseT (UintT 256)) (BaseT (UintT 8));
     scalar_convert_fn "int_to_uint" (BaseT (IntT 256)) (BaseT (UintT 256));
     scalar_convert_fn "uint_to_int" (BaseT (UintT 256)) (BaseT (IntT 256));
     scalar_convert_fn "bool_to_uint" (BaseT BoolT) (BaseT (UintT 8))]
End

Definition scalar_convert_address_program_def:
  scalar_convert_address_program =
    [scalar_convert_fn "address_to_uint" (BaseT AddressT) (BaseT (UintT 256));
     scalar_convert_fn "uint_to_address" (BaseT (UintT 256)) (BaseT AddressT)]
End

Definition scalar_convert_decimal_program_def:
  scalar_convert_decimal_program =
    [FunctionDecl External Pure F F "f"
       ([] : (string # type) list) ([] : expr list) (BaseT (IntT 8))
       [Return (SOME
          (TypeBuiltin (BaseT (IntT 8)) Convert (BaseT (IntT 8))
            [Literal (BaseT DecimalT) (DecimalL 10000000000)]))]]
End

Definition scalar_convert_int_to_decimal_program_def:
  scalar_convert_int_to_decimal_program =
    [FunctionDecl External Pure F F "f"
       ([] : (string # type) list) ([] : expr list) (BaseT DecimalT)
       [Return (SOME
          (TypeBuiltin (BaseT DecimalT) Convert (BaseT DecimalT)
            [Literal (BaseT (IntT 8)) (IntL 1)]))]]
End

Definition scalar_convert_bytes_fixed_program_def:
  scalar_convert_bytes_fixed_program =
    [scalar_convert_fn "bytes32_to_uint" (BaseT (BytesT (Fixed 32)))
       (BaseT (UintT 256))]
End

Definition scalar_convert_uint_to_bytes32_program_def:
  scalar_convert_uint_to_bytes32_program =
    [scalar_convert_fn "uint_to_bytes32" (BaseT (UintT 256))
       (BaseT (BytesT (Fixed 32)))]
End

Definition scalar_convert_bytes32_to_address_program_def:
  scalar_convert_bytes32_to_address_program =
    [scalar_convert_fn "bytes32_to_address" (BaseT (BytesT (Fixed 32)))
       (BaseT AddressT)]
End

Definition scalar_convert_bytes32_to_decimal_program_def:
  scalar_convert_bytes32_to_decimal_program =
    [scalar_convert_fn "bytes32_to_decimal" (BaseT (BytesT (Fixed 32)))
       (BaseT DecimalT)]
End

Definition scalar_convert_bytes32_to_bytes4_program_def:
  scalar_convert_bytes32_to_bytes4_program =
    [scalar_convert_fn "bytes32_to_bytes4" (BaseT (BytesT (Fixed 32)))
       (BaseT (BytesT (Fixed 4)))]
End

Definition scalar_convert_bytes_dynamic_program_def:
  scalar_convert_bytes_dynamic_program =
    [scalar_convert_fn "dynbytes_to_bool" (BaseT (BytesT (Dynamic 32)))
       (BaseT BoolT);
     scalar_convert_fn "dynbytes_to_uint" (BaseT (BytesT (Dynamic 32)))
       (BaseT (UintT 256))]
End

(* ===== Wei denominations and modular arithmetic ===== *)

Definition scalar_wei_small_program_def:
  scalar_wei_small_program =
    [scalar_wei_fn "wei_value" Wei;
     scalar_wei_fn "kwei_value" Kwei;
     scalar_wei_fn "mwei_value" Mwei;
     scalar_wei_fn "gwei_value" Gwei]
End

Definition scalar_wei_large_program_def:
  scalar_wei_large_program =
    [scalar_wei_fn "szabo_value" Szabo;
     scalar_wei_fn "finney_value" Finney;
     scalar_wei_fn "ether_value" Ether;
     scalar_wei_fn "kether_value" KEther]
End

Definition scalar_modular_program_def:
  scalar_modular_program =
    [scalar_modular3_fn "add_mod" AddMod;
     scalar_modular3_fn "mul_mod" MulMod;
     FunctionDecl External Pure F F "power_mod_256"
       [("a", BaseT (UintT 256)); ("b", BaseT (UintT 256))]
       ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) PowMod256
          [Name (BaseT (UintT 256)) "a";
           Name (BaseT (UintT 256)) "b"]))]]
End
