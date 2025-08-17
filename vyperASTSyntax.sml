structure vyperASTSyntax :> vyperASTSyntax = struct

  open HolKernel vyperASTTheory byteStringCacheLib
  open stringSyntax pairSyntax optionSyntax listSyntax numSyntax

  fun astk s = prim_mk_const{Thy="vyperAST",Name=s}
  fun asty s = mk_thy_type{Thy="vyperAST",Tyop=s,Args=[]}

  val Fixed_tm        = astk"Fixed"
  val Dynamic_tm      = astk"Dynamic"
  val UintT_tm        = astk"UintT"
  val IntT_tm         = astk"IntT"
  val BoolT_tm        = astk"BoolT"
  val DecimalT_tm     = astk"DecimalT"
  val StringT_tm      = astk"StringT"
  val BytesT_tm       = astk"BytesT"
  val AddressT_tm     = astk"AddressT"
  val BaseT_tm        = astk"BaseT"
  val TupleT_tm       = astk"TupleT"
  val ArrayT_tm       = astk"ArrayT"
  val StructT_tm      = astk"StructT"
  val FlagT_tm        = astk"FlagT"
  val NoneT_tm        = astk"NoneT"
  val Signed_tm       = astk"Signed"
  val Unsigned_tm     = astk"Unsigned"
  val BoolL_tm        = astk"BoolL"
  val StringL_tm      = astk"StringL"
  val BytesL_tm       = astk"BytesL"
  val IntL_tm         = astk"IntL"
  val DecimalL_tm     = astk"DecimalL"
  val Add_tm          = astk"Add"
  val Sub_tm          = astk"Sub"
  val Mul_tm          = astk"Mul"
  val Div_tm          = astk"Div"
  val UAdd_tm         = astk"UAdd"
  val USub_tm         = astk"USub"
  val UMul_tm         = astk"UMul"
  val UDiv_tm         = astk"UDiv"
  val ExpMod_tm       = astk"ExpMod"
  val Mod_tm          = astk"Mod"
  val Exp_tm          = astk"Exp"
  val And_tm          = astk"And"
  val Or_tm           = astk"Or"
  val XOr_tm          = astk"XOr"
  val ShL_tm          = astk"ShL"
  val ShR_tm          = astk"ShR"
  val In_tm           = astk"In"
  val NotIn_tm        = astk"NotIn"
  val Eq_tm           = astk"Eq"
  val NotEq_tm        = astk"NotEq"
  val Lt_tm           = astk"Lt"
  val LtE_tm          = astk"LtE"
  val Gt_tm           = astk"Gt"
  val GtE_tm          = astk"GtE"
  val Sender_tm       = astk"Sender"
  val SelfAddr_tm     = astk"SelfAddr"
  val TimeStamp_tm    = astk"TimeStamp"
  val BlockNumber_tm  = astk"BlockNumber"
  val BlobBaseFee_tm  = astk"BlobBaseFee"
  val GasPrice_tm     = astk"GasPrice"
  val PrevHash_tm     = astk"PrevHash"
  val Address_tm      = astk"Address"
  val Balance_tm      = astk"Balance"
  val Wei_tm          = astk"Wei"
  val Kwei_tm         = astk"Kwei"
  val Mwei_tm         = astk"Mwei"
  val Gwei_tm         = astk"Gwei"
  val Szabo_tm        = astk"Szabo"
  val Finney_tm       = astk"Finney"
  val Ether_tm        = astk"Ether"
  val KEther_tm       = astk"KEther"
  val MEther_tm       = astk"MEther"
  val GEther_tm       = astk"GEther"
  val TEther_tm       = astk"TEther"
  val Len_tm          = astk"Len"
  val Not_tm          = astk"Not"
  val Neg_tm          = astk"Neg"
  val Keccak256_tm    = astk"Keccak256"
  val AsWeiValue_tm   = astk"AsWeiValue"
  val Concat_tm       = astk"Concat"
  val Slice_tm        = astk"Slice"
  val MakeArray_tm    = astk"MakeArray"
  val Floor_tm        = astk"Floor"
  val Bop_tm          = astk"Bop"
  val AddMod_tm       = astk"AddMod"
  val MulMod_tm       = astk"MulMod"
  val Env_tm          = astk"Env"
  val BlockHash_tm    = astk"BlockHash"
  val Acc_tm          = astk"Acc"
  val IntCall_tm      = astk"IntCall"
  val Send_tm         = astk"Send"
  val Empty_tm        = astk"Empty"
  val MaxValue_tm     = astk"MaxValue"
  val MinValue_tm     = astk"MinValue"
  val Epsilon_tm      = astk"Epsilon"
  val Convert_tm      = astk"Convert"
  val Name_tm         = astk"Name"
  val TopLevelName_tm = astk"TopLevelName"
  val IfExp_tm        = astk"IfExp"
  val Literal_tm      = astk"Literal"
  val StructLit_tm    = astk"StructLit"
  val Subscript_tm    = astk"Subscript"
  val Attribute_tm    = astk"Attribute"
  val Builtin_tm      = astk"Builtin"
  val TypeBuiltin_tm  = astk"TypeBuiltin"
  val Pop_tm          = astk"Pop"
  val AstCall_tm      = astk"Call"
  val NameTarget_tm         = astk"NameTarget"
  val TopLevelNameTarget_tm = astk"TopLevelNameTarget"
  val SubscriptTarget_tm    = astk"SubscriptTarget"
  val AttributeTarget_tm    = astk"AttributeTarget"
  val BaseTarget_tm   = astk"BaseTarget"
  val TupleTarget_tm  = astk"TupleTarget"
  val Array_tm        = astk"Array"
  val Range_tm        = astk"Range"
  val Pass_tm         = astk"Pass"
  val Continue_tm     = astk"Continue"
  val Break_tm        = astk"Break"
  val Expr_tm         = astk"Expr"
  val For_tm          = astk"For"
  val If_tm           = astk"If"
  val Assert_tm       = astk"Assert"
  val Log_tm          = astk"Log"
  val Raise_tm        = astk"Raise"
  val Return_tm       = astk"Return"
  val Assign_tm       = astk"Assign"
  val AugAssign_tm    = astk"AugAssign"
  val Append_tm       = astk"Append"
  val AnnAssign_tm    = astk"AnnAssign"
  val External_tm     = astk"External"
  val Internal_tm     = astk"Internal"
  val Deploy_tm       = astk"Deploy"
  val Pure_tm         = astk"Pure"
  val View_tm         = astk"View"
  val Nonpayable_tm   = astk"Nonpayable"
  val Payable_tm      = astk"Payable"
  val Public_tm       = astk"Public"
  val Private_tm      = astk"Private"
  val Constant_tm     = astk"Constant"
  val Immutable_tm    = astk"Immutable"
  val Transient_tm    = astk"Transient"
  val Storage_tm      = astk"Storage"
  val Type_tm         = astk"Type"
  val HashMapT_tm     = astk"HashMapT"
  val FunctionDecl_tm = astk"FunctionDecl"
  val VariableDecl_tm = astk"VariableDecl"
  val HashMapDecl_tm  = astk"HashMapDecl"
  val StructDecl_tm   = astk"StructDecl"
  val EventDecl_tm    = astk"EventDecl"
  val FlagDecl_tm     = astk"FlagDecl"

  val type_ty = asty"type"
  val stmt_ty = asty"stmt"
  val expr_ty = asty"expr"
  val toplevel_ty = asty"toplevel"

  val identifier_ty = string_ty
  val argument_ty = mk_prod(identifier_ty, type_ty)
  val bool_tm = mk_comb(BaseT_tm, BoolT_tm)
  val address_tm = mk_comb(BaseT_tm, AddressT_tm)
  val decimal_tm = mk_comb(BaseT_tm, DecimalT_tm)
  fun mk_Fixed n = mk_comb(Fixed_tm, n)
  fun mk_Dynamic n = mk_comb(Dynamic_tm, n)
  fun mk_Signed n = mk_comb(Signed_tm, n)
  fun mk_Unsigned n = mk_comb(Unsigned_tm, n)
  fun mk_uint n = mk_comb(BaseT_tm, mk_comb(UintT_tm, n))
  fun mk_int n = mk_comb(BaseT_tm, mk_comb(IntT_tm, n))
  fun mk_bytes n = mk_comb(BaseT_tm, mk_comb(BytesT_tm, mk_Fixed n))
  fun mk_FunctionDecl v m n a t b = list_mk_comb(FunctionDecl_tm, [v,m,n,a,t,b])
  fun mk_VariableDecl (v,m,n,t) = list_mk_comb(VariableDecl_tm, [v,m,n,t])
  fun mk_HashMapDecl (v,bt,n,t,vt) = list_mk_comb(HashMapDecl_tm, [v,bt,n,t,vt])
  fun mk_String n = mk_comb(BaseT_tm, mk_comb(StringT_tm, n))
  fun mk_Bytes n = mk_comb(BaseT_tm, mk_comb(BytesT_tm, mk_Dynamic n))
  fun mk_BytesM n = mk_comb(BaseT_tm, mk_comb(BytesT_tm, mk_Fixed n))
  fun mk_Expr e = mk_comb(Expr_tm, e)
  fun mk_For s t i n b = list_mk_comb(For_tm, [s,t,i,n,b])
  fun mk_Name s = mk_comb(Name_tm, fromMLstring s)
  fun mk_StructLit (s,ls) = list_mk_comb(StructLit_tm, [
    s, mk_list(ls, mk_prod(string_ty, expr_ty))])
  fun mk_IfExp (e1,e2,e3) = list_mk_comb(IfExp_tm, [e1,e2,e3])
  fun mk_IntCall s = mk_comb(IntCall_tm, s)
  fun mk_Empty t = list_mk_comb(TypeBuiltin_tm, [
    Empty_tm, t, mk_list([], expr_ty)])
  fun mk_MaxValue t = list_mk_comb(TypeBuiltin_tm, [
    MaxValue_tm, t, mk_list([], expr_ty)])
  fun mk_MinValue t = list_mk_comb(TypeBuiltin_tm, [
    MinValue_tm, t, mk_list([], expr_ty)])
  fun mk_Convert (t,v) = list_mk_comb(TypeBuiltin_tm, [
    Convert_tm, t, mk_list([v], expr_ty)])
  fun mk_Call ct args = list_mk_comb(AstCall_tm, [ct, mk_list (args, expr_ty)])
  fun mk_Assert (e,s) = list_mk_comb(Assert_tm, [e, s])
  fun mk_Log (id,es) = list_mk_comb(Log_tm, [id, es])
  fun mk_Subscript e1 e2 = list_mk_comb(Subscript_tm, [e1, e2])
  fun mk_If e s1 s2 = list_mk_comb(If_tm, [e,s1,s2])
  fun mk_li (b,i) = mk_comb(Literal_tm, list_mk_comb(IntL_tm, [b,i]))
  fun mk_ld i = mk_comb(Literal_tm, mk_comb(DecimalL_tm, i))
  fun mk_lb b = mk_comb(Literal_tm, mk_comb(BoolL_tm, b))
  fun mk_ls (n,s) = mk_comb(Literal_tm,
    list_mk_comb(StringL_tm, [n, fromMLstring s]))
  val empty_lstr = mk_ls(numSyntax.zero_tm, "")
  fun mk_Return tmo = mk_comb(Return_tm, lift_option (mk_option expr_ty) I tmo)
  fun mk_AnnAssign (s,t,e) = list_mk_comb(AnnAssign_tm, [s, t, e])
  fun mk_AugAssign t b e = list_mk_comb(AugAssign_tm, [t, b, e])
  fun mk_Hex_dyn (n, s) = let
    val s = if String.isPrefix "0x" s then String.extract(s,2,NONE) else s
    val b = mk_comb(Dynamic_tm, n)
  in
    mk_comb(Literal_tm,
      list_mk_comb(BytesL_tm, [b, cached_bytes_from_hex s]))
  end
  fun mk_Hex s = let
    val s = if String.isPrefix "0x" s then String.extract(s,2,NONE) else s
    val n = numSyntax.term_of_int $ String.size s div 2
    val b = mk_comb(Fixed_tm, n)
  in
    mk_comb(Literal_tm,
      list_mk_comb(BytesL_tm, [b, cached_bytes_from_hex s]))
  end
  fun mk_Builtin b es = list_mk_comb(Builtin_tm, [b, es])
  fun mk_Concat n = mk_comb(Concat_tm, n)
  fun mk_Slice n = mk_comb(Slice_tm, n)
  fun mk_Not t = mk_Builtin Not_tm (mk_list([t], expr_ty))
  fun mk_Neg t = mk_Builtin Neg_tm (mk_list([t], expr_ty))
  fun mk_Keccak256 t = mk_Builtin Keccak256_tm (mk_list([t], expr_ty))
  fun mk_AsWeiValue (d,t) = mk_Builtin (mk_comb(AsWeiValue_tm, d)) (mk_list([t], expr_ty))
  fun mk_Floor e = mk_Builtin Floor_tm (mk_list([e], expr_ty))
  fun mk_Bop b = mk_comb(Bop_tm, b)
  fun mk_Len e = mk_Builtin Len_tm (mk_list([e], expr_ty))
  fun mk_MakeArray (to,b,ls) =
    mk_Builtin (list_mk_comb(MakeArray_tm, [to,b]))
      (mk_list (ls, expr_ty))
  fun mk_Tuple ls = let
    val n = numSyntax.term_of_int $ List.length ls
    val b = mk_comb(Fixed_tm, n)
  in
    mk_MakeArray (mk_none type_ty, b, ls)
  end
  fun mk_SArray (t,ls) = let
    val n = numSyntax.term_of_int $ List.length ls
    val b = mk_comb(Fixed_tm, n)
  in
    mk_MakeArray (mk_some t, b, ls)
  end
  val msg_sender_tm = list_mk_comb(Builtin_tm, [
    mk_comb(Env_tm, Sender_tm), mk_list([], expr_ty)])
  val self_addr_tm = list_mk_comb(Builtin_tm, [
    mk_comb(Env_tm, SelfAddr_tm), mk_list([], expr_ty)])
  val time_stamp_tm = list_mk_comb(Builtin_tm, [
    mk_comb(Env_tm, TimeStamp_tm), mk_list([], expr_ty)])
  val block_number_tm = list_mk_comb(Builtin_tm, [
    mk_comb(Env_tm, BlockNumber_tm), mk_list([], expr_ty)])
  val blob_base_fee_tm = list_mk_comb(Builtin_tm, [
    mk_comb(Env_tm, BlobBaseFee_tm), mk_list([], expr_ty)])
  val gas_price_tm = list_mk_comb(Builtin_tm, [
    mk_comb(Env_tm, GasPrice_tm), mk_list([], expr_ty)])
  val prev_hash_tm = list_mk_comb(Builtin_tm, [
    mk_comb(Env_tm, PrevHash_tm), mk_list([], expr_ty)])
  fun mk_BlockHash e = list_mk_comb(Builtin_tm, [
    BlockHash_tm, mk_list([e], expr_ty)])

end
