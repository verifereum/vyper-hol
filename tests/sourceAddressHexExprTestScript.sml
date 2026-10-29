Theory sourceAddressHexExprTest
Ancestors
  sourceExprElaborate sourceExprDefs sourceConstBuiltinCompute sourceConstBuiltin
  sourceConstAST sourceResolve sourceSyntax vyperTypeSystem vyperAST finite_map
Libs
  cv_transLib

(* Kernel-computed hash equations from original ASCII, not compiler metadata. *)
fun hash name s = let
  val chars = listSyntax.mk_list (map (numSyntax.term_of_int o Char.ord)
    (String.explode s),numSyntax.num)
  val th = save_thm (name,cv_eval ``source_const_keccak ^chars``)
in computeLib.add_funs [th] end;
val () = hash "address_checksum_keccak" "abcdefabcdefabcdefabcdefabcdefabcdefabcd";
val () = hash "address_zero_keccak" "0000000000000000000000000000000000000000";

Theorem address_hex_source_categories:
  source_expr_literal_domain
    (SCL_Hex "0xABcdEFABcdEFabcdEfAbCdefabcdeFABcDEFabCD") (BaseT AddressT) /\
  ~source_expr_literal_domain
    (SCL_Hex "0xABcdEFABcdEFabcdEfAbCdefabcdeFABcDEFabCD") (BaseT (BytesT (Fixed 20))) /\
  ~source_expr_literal_domain
    (SCL_Hex "0xabcdefabcdefabcdefabcdefabcdefabcdefabcd") (BaseT AddressT) /\
  source_expr_literal_domain
    (SCL_Hex "0xabcdefabcdefabcdefabcdefabcdefabcdefabcd") (BaseT (BytesT (Fixed 20))) /\
  source_expr_literal_domain
    (SCL_Hex "0xABCDEFABCDEFABCDEFABCDEFABCDEFABCDEFABCD") (BaseT (BytesT (Fixed 20))) /\
  ~source_expr_literal_domain (SCL_Hex "0x1234") (BaseT AddressT) /\
  ~source_expr_literal_domain (SCL_Hex "0x1234") (BaseT (BytesT (Fixed 20)))
Proof
  EVAL_TAC
QED

(* Parameter types and type-operand identities are independently supplied.
   In particular the requested return type cannot license the argument type. *)
Definition address_hex_dynamic_def:
  address_hex_dynamic env aty rty target =
    source_expr_elaborate 12 (env with var_types := FEMPTY |+ ("a",aty))
      [[("a",["a"]);("convert",["builtin";"convert"]);
        ("address",["builtin";"address"]);("bytes20",["builtin";"bytes20"])]]
      [(["a"],SR_Dynamic);(["builtin";"convert"],SR_Builtin SCB_Convert);
       (["builtin";"address"],SR_Type);(["builtin";"bytes20"],SR_FixedBytes 20)] []
      [(["a"],SE_Runtime (Name aty "a"));
       (["builtin";"address"],SE_Type (BaseT AddressT));
       (["builtin";"bytes20"],SE_Type (BaseT (BytesT (Fixed 20))))]
      rty (SX_Call (SX_Name "convert") [SX_Name "a";SX_Name target] [])
End

Theorem address_hex_dynamic_conversion_exact:
  address_hex_dynamic env (BaseT AddressT) (BaseT (BytesT (Fixed 20))) "bytes20" =
    SC_Value (TypeBuiltin (BaseT (BytesT (Fixed 20))) Convert (BaseT (BytesT (Fixed 20)))
      [Name (BaseT AddressT) "a"]) /\
  address_hex_dynamic env (BaseT (BytesT (Fixed 20))) (BaseT AddressT) "address" =
    SC_Value (TypeBuiltin (BaseT AddressT) Convert (BaseT AddressT)
      [Name (BaseT (BytesT (Fixed 20))) "a"]) /\
  address_hex_dynamic env (BaseT AddressT) (BaseT AddressT) "address" = SC_Invalid SCErr_Type /\
  address_hex_dynamic env (BaseT (BytesT (Fixed 20))) (BaseT (BytesT (Fixed 20))) "bytes20" =
    SC_Invalid SCErr_Type /\
  address_hex_dynamic env (BaseT AddressT) (BaseT AddressT) "bytes20" = SC_Invalid SCErr_Type
Proof
  EVAL_TAC
QED

Theorem address_hex_declared_constant_type:
  source_expr_hex_argument_type [[("C",["C"])]] [(["C"],SR_Constant)]
    [(["C"],SC_Constant (SCV_Hex "0x0000000000000000000000000000000000000000"))]
    [(["C"],SE_Runtime (TopLevelName (BaseT (BytesT (Fixed 20))) (NONE,"C")))]
    (SX_Name "C") = SOME (BaseT (BytesT (Fixed 20))) /\
  source_expr_hex_argument_type [[("C",["C"])]] [(["C"],SR_Constant)]
    [(["C"],SC_Constant (SCV_Hex "0x0000000000000000000000000000000000000000"))]
    [(["C"],SE_Runtime (TopLevelName (BaseT AddressT) (NONE,"C")))]
    (SX_Name "C") = SOME (BaseT AddressT) /\
  source_expr_hex_argument_type [[("C",["C"])]] [(["C"],SR_Constant)]
    [(["C"],SC_Constant (SCV_Hex "0x0000000000000000000000000000000000000000"))] []
    (SX_Name "C") = NONE
Proof
  EVAL_TAC
QED

(* Constant declaration types, not the default category of an all-zero token,
   must also reject same-type conversion. No full-Source body API is required. *)
Definition address_hex_constant_conversion_def:
  address_hex_constant_conversion env ty target =
    source_expr_elaborate 12 env
      [[("C",["C"]);("convert",["builtin";"convert"]);(target,["target"])]]
      [(["C"],SR_Constant);(["builtin";"convert"],SR_Builtin SCB_Convert);
       (["target"],SR_Type)]
      [(["C"],SC_Constant (SCV_Hex "0x0000000000000000000000000000000000000000"))]
      [(["C"],SE_Runtime (TopLevelName ty (NONE,"C")));(["target"],SE_Type ty)]
      ty (SX_Call (SX_Name "convert") [SX_Name "C";SX_Name target] [])
End

Theorem address_hex_same_type_constant_rejected:
  address_hex_constant_conversion env (BaseT AddressT) "address" = SC_Invalid SCErr_Type /\
  address_hex_constant_conversion env (BaseT (BytesT (Fixed 20))) "bytes20" = SC_Invalid SCErr_Type
Proof
  EVAL_TAC
QED

val () = app (fn (_,th) => let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "address/hex expression theorem audit" end) (DB.thms "sourceAddressHexExprTest");
