Theory sourceConstBuiltinTest
Ancestors
  sourceConstEvalProps sourceConstBuiltinProps sourceConstBuiltin sourceConstEval
  sourceConstBuiltinCompute
Libs
  cv_transLib intLib

(* Hash regression oracles are discharged by the dependency's proved cv
   implementation, never by Python/compiler metadata or an ML hash oracle. *)
Theorem source_const_keccak_hello:
  source_const_keccak [104;101;108;108;111] =
  [28;138;255;149;6;133;194;237;75;195;23;79;52;114;40;123;
   86;217;81;123;156;148;129;39;49;154;9;167;163;109;234;200]
Proof
  CONV_TAC cv_eval
QED

val source_const_keccak_foo_full = save_thm ("source_const_keccak_foo_full",
  cv_eval ``source_const_keccak [102;111;111;40;41]``);

Theorem source_const_keccak_foo:
  TAKE 4 (source_const_keccak [102;111;111;40;41]) = [194;152;85;120]
Proof
  CONV_TAC cv_eval
QED

Theorem source_const_keccak_transfer:
  TAKE 4 (source_const_keccak
    [116;114;97;110;115;102;101;114;40;97;100;100;114;101;115;115;44;
     117;105;110;116;50;53;54;41]) = [169;5;156;187]
Proof
  CONV_TAC cv_eval
QED

Theorem source_const_numeric_builtin_examples:
  source_const_eval [] (SCE_Builtin SCB_Min
    [SCE_Literal (SCL_Int 4); SCE_Literal (SCL_Int 1)] []) = SC_Value (SCV_Int 1) /\
  source_const_eval [] (SCE_Builtin SCB_Max
    [SCE_Literal (SCL_Int 1); SCE_Literal (SCL_Int 2)] []) = SC_Value (SCV_Int 2) /\
  source_const_eval [] (SCE_Builtin SCB_Abs [SCE_Literal (SCL_Int (-5))] []) =
    SC_Value (SCV_Int 5) /\
  source_const_eval [] (SCE_Builtin SCB_PowMod256
    [SCE_Literal (SCL_Int 2); SCE_Literal (SCL_Int 10)] []) = SC_Value (SCV_Int 1024) /\
  source_const_eval [] (SCE_Builtin SCB_Uint256AddMod
    [SCE_Literal (SCL_Int 5); SCE_Literal (SCL_Int 6); SCE_Literal (SCL_Int 7)] []) =
    SC_Value (SCV_Int 4) /\
  source_const_eval [] (SCE_Builtin SCB_Uint256MulMod
    [SCE_Literal (SCL_Int 5); SCE_Literal (SCL_Int 6); SCE_Literal (SCL_Int 7)] []) =
    SC_Value (SCV_Int 2)
Proof
  EVAL_TAC
QED

Theorem source_const_numeric_domain_examples:
  source_const_builtin SCB_Abs [SCV_Int (-(2 ** 255))] [] = SC_Invalid SCErr_Overflow /\
  source_const_builtin SCB_Abs [SCV_Int (2 ** 255)] [] = SC_Invalid SCErr_Overflow /\
  source_const_builtin SCB_PowMod256 [SCV_Int (-1); SCV_Int 0] [] = SC_Invalid SCErr_Overflow /\
  source_const_builtin SCB_PowMod256 [SCV_Int (2 ** 256); SCV_Int 0] [] =
    SC_Invalid SCErr_Overflow /\
  source_const_builtin SCB_Uint256AddMod [SCV_Int (-1); SCV_Int 1; SCV_Int 2] [] =
    SC_Invalid SCErr_Overflow /\
  source_const_builtin SCB_Uint256MulMod [SCV_Int 0; SCV_Int (2 ** 256); SCV_Int 1] [] =
    SC_Invalid SCErr_Overflow /\
  source_const_builtin SCB_Min [SCV_Int (-1); SCV_Int (2 ** 255)] [] = SC_Invalid SCErr_Domain /\
  source_const_builtin SCB_Max [SCV_Bool T; SCV_Bool F] [] = SC_Invalid SCErr_Domain /\
  source_const_builtin SCB_Min [SCV_Decimal 1; SCV_Int 1] [] = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_modular_boundary_examples:
  source_const_builtin SCB_Uint256AddMod
    [SCV_Int (2 ** 256 - 1); SCV_Int 1; SCV_Int 3] [] = SC_Value (SCV_Int 1) /\
  source_const_builtin SCB_Uint256MulMod
    [SCV_Int (2 ** 255); SCV_Int 2; SCV_Int 3] [] = SC_Value (SCV_Int 1) /\
  source_const_builtin SCB_PowMod256 [SCV_Int 2; SCV_Int 256] [] = SC_Value (SCV_Int 0) /\
  source_const_builtin SCB_PowMod256 [SCV_Int 0; SCV_Int 0] [] = SC_Value (SCV_Int 1) /\
  source_const_builtin SCB_Uint256AddMod [SCV_Int 1; SCV_Int 1; SCV_Int 0] [] =
    SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

Theorem source_const_large_modular_power:
  source_const_modexp 1 (2 ** 256 - 1) = 1
Proof
  CONV_TAC cv_eval
QED

Theorem source_const_decimal_minmax_examples:
  source_const_builtin SCB_Min [SCV_Decimal (-12300000000); SCV_Decimal 10000000000] [] =
    SC_Value (SCV_Decimal (-12300000000)) /\
  source_const_builtin SCB_Max [SCV_Decimal (-12300000000); SCV_Decimal 10000000000] [] =
    SC_Value (SCV_Decimal 10000000000) /\
  source_const_builtin SCB_Min [SCV_Decimal (-(2 ** 167) - 1); SCV_Decimal 0] [] =
    SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_signature_examples:
  source_const_builtin SCB_Abs [] [] = SC_Invalid SCErr_Arity /\
  source_const_builtin SCB_Min [SCV_Int 1] [] = SC_Invalid SCErr_Arity /\
  source_const_builtin SCB_PowMod256 [SCV_Int 2; SCV_Int 3] [("x",SCV_Int 0)] =
    SC_Invalid SCErr_Keyword /\
  source_const_builtin SCB_MethodId [SCV_String "foo()"] [("output_type",SCV_Int 4)] =
    SC_Invalid SCErr_Type /\
  source_const_builtin SCB_MethodId [SCV_String "foo()"]
    [("output_type",SCV_BytesType T 4);("output_type",SCV_BytesType T 4)] =
    SC_Invalid SCErr_Keyword /\
  source_const_builtin SCB_MethodId [SCV_String "foo()"] [("unknown",SCV_BytesType T 4)] =
    SC_Invalid SCErr_Keyword /\
  source_const_builtin SCB_MethodId [SCV_String "foo()"] [("output_type",SCV_BytesType F 5)] =
    SC_Invalid SCErr_Type /\
  source_const_builtin SCB_MethodId [SCV_String "foo( )"] [] = SC_Invalid SCErr_Domain /\
  source_const_builtin SCB_MethodId [SCV_Bytes [1;2;3;4]] [] = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_builtin_eager_examples:
  source_const_eval [] (SCE_Builtin SCB_Abs
    [SCE_Dynamic; SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 1))
                                         (SCE_Literal (SCL_Int 0))] []) =
    SC_Invalid SCErr_ZeroDivisor /\
  source_const_eval [] (SCE_Builtin SCB_MethodId [SCE_Literal (SCL_String "foo()")]
    [("output_type",SCE_BytesType F
      (SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 4)) (SCE_Literal (SCL_Int 0))))]) =
    SC_Invalid SCErr_ZeroDivisor /\
  source_const_eval [] (SCE_Builtin SCB_MethodId [SCE_Dynamic]
    [("output_type",SCE_BytesType T (SCE_Literal (SCL_Int 4)))]) = SC_Invalid SCErr_Domain /\
  source_const_eval [] (SCE_Builtin SCB_Concat [SCE_Dynamic] []) =
    SC_Unsupported (SCS_Builtin SCB_Concat)
Proof
  EVAL_TAC
QED

Theorem source_const_length_examples:
  source_const_eval [] (SCE_Builtin SCB_Len [SCE_Literal (SCL_String "test")] []) =
    SC_Value (SCV_Int 4) /\
  source_const_builtin SCB_Len [SCV_Bytes [0;255;0]] [] = SC_Value (SCV_Int 3) /\
  source_const_builtin SCB_Len [SCV_Bytes []] [] = SC_Value (SCV_Int 0) /\
  source_const_builtin SCB_Len [SCV_Hex "0x0102"] [] = SC_Invalid SCErr_Domain /\
  source_const_builtin SCB_Keccak256 [SCV_Hex "0x0102"] [] = SC_Invalid SCErr_Domain /\
  source_const_builtin SCB_Keccak256 [SCV_Int 1] [] = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_keccak_literal_example:
  source_const_eval [] (SCE_Builtin SCB_Keccak256
    [SCE_Literal (SCL_String "hello")] []) = SC_Value (SCV_Hex
      "0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8")
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``source_const_keccak``]) >>
  REWRITE_TAC [source_const_keccak_hello] >> EVAL_TAC
QED

Theorem source_const_keccak_bytes_example:
  source_const_eval [] (SCE_Builtin SCB_Keccak256
    [SCE_Literal (SCL_Bytes [104;101;108;108;111])] []) = SC_Value (SCV_Hex
      "0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8")
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``source_const_keccak``]) >>
  REWRITE_TAC [source_const_keccak_hello] >> EVAL_TAC
QED

val source_const_keccak_zero32 = save_thm ("source_const_keccak_zero32",
  cv_eval ``source_const_keccak (REPLICATE 32 0)``);

Theorem source_const_keccak_bytes32_example:
  source_const_eval [] (SCE_Builtin SCB_Keccak256 [SCE_Literal
    (SCL_Hex "0x0000000000000000000000000000000000000000000000000000000000000000")] []) =
  SC_Value (SCV_Hex "0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563")
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``source_const_keccak``]) >>
  REWRITE_TAC [CONV_RULE (LAND_CONV (RAND_CONV EVAL)) source_const_keccak_zero32] >> EVAL_TAC
QED

Theorem source_const_method_id_source_output_examples:
  source_const_eval [] (SCE_Builtin SCB_MethodId [SCE_Literal (SCL_String "foo()")]
    [("output_type",SCE_BytesType T (SCE_Literal (SCL_Int 4)))]) =
      SC_Value (SCV_Hex "0xc2985578") /\
  source_const_eval [] (SCE_Builtin SCB_MethodId [SCE_Literal (SCL_String "foo()")]
    [("output_type",SCE_BytesType F
      (SCE_Binary SCB_Add (SCE_Literal (SCL_Int 2)) (SCE_Literal (SCL_Int 2))))]) =
      SC_Value (SCV_Bytes [194;152;85;120]) /\
  source_const_eval [(["SIG"],SC_Constant (SCV_String "foo()"))]
    (SCE_Builtin SCB_MethodId [SCE_Name ["SIG"]] []) =
      SC_Value (SCV_Bytes [194;152;85;120])
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``source_const_keccak``]) >>
  REWRITE_TAC [source_const_keccak_foo_full] >> EVAL_TAC
QED

fun audit_builtin_theory thy =
  let
    val exports = DB.thms thy
    fun check (name, th) =
      let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
      in
        if null (Thm.hyp th) andalso null axioms andalso
           List.all (fn s => s = "DISK_THM") oracles then ()
        else raise Fail ("builtin kernel audit failed: " ^ thy ^ "." ^ name)
      end
  in
    List.app check exports;
    print ("SOURCE_CONST_KERNEL_CLOSED " ^ thy ^ " exports=" ^
           Int.toString (length exports) ^ "\n")
  end;

val () = List.app audit_builtin_theory
  ["sourceConstBuiltin", "sourceConstBuiltinCompute",
   "sourceConstBuiltinProps", "sourceConstBuiltinTest"];
