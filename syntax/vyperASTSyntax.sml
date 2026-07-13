structure vyperASTSyntax :> vyperASTSyntax = struct

open HolKernel vyperASTTheory boolSyntax stringSyntax pairSyntax optionSyntax listSyntax

val ERR = Feedback.mk_HOL_ERR "vyperASTSyntax"

fun astk s = prim_mk_const {Thy = "vyperAST", Name = s}
fun asty s = mk_thy_type {Thy = "vyperAST", Tyop = s, Args = []}

val bound_ty = asty "bound"
val base_type_ty = asty "base_type"
val type_ty = asty "type"
val int_bound_ty = asty "int_bound"
val literal_ty = asty "literal"
val binop_ty = asty "binop"
val env_item_ty = asty "env_item"
val account_item_ty = asty "account_item"
val denomination_ty = asty "denomination"
val builtin_ty = asty "builtin"
val ext_call_sig_ty = mk_prod (string_ty, mk_prod (mk_list_type type_ty, type_ty))
val raw_call_flags_ty = asty "raw_call_flags"
val create_kind_ty = asty "create_kind"
val type_builtin_ty = asty "type_builtin"
val expr_ty = asty "expr"
val stmt_ty = asty "stmt"
val assignment_target_ty = asty "assignment_target"
val base_assignment_target_ty = asty "base_assignment_target"
val iterator_ty = asty "iterator"
val call_target_ty = asty "call_target"
val assert_reason_ty = asty "assert_reason"
val raise_reason_ty = asty "raise_reason"
val function_visibility_ty = asty "function_visibility"
val function_mutability_ty = asty "function_mutability"
val variable_visibility_ty = asty "variable_visibility"
val variable_mutability_ty = asty "variable_mutability"
val argument_ty = mk_prod (string_ty, type_ty)
val interface_func_ty = mk_prod (string_ty, mk_prod (mk_list_type argument_ty, mk_prod (type_ty, function_mutability_ty)))
val value_type_ty = asty "value_type"
val toplevel_ty = asty "toplevel"

fun syntax0 name =
  let val tm = astk name in
    (tm, fn x => aconv x tm)
  end

fun dest_n name c n tm =
  let
    val (h, args) = strip_comb tm
  in
    if aconv h c andalso length args = n then args
    else raise ERR ("dest_" ^ name) "unexpected term shape"
  end

fun mk_n c args = list_mk_comb (c, args)

fun syntax5 name =
  let val c = astk name in
    ( c
    , fn (a,b,c1,d,e) => mk_n c [a,b,c1,d,e]
    , fn tm =>
        (case dest_n name c 5 tm of
           [a,b,c1,d,e] => (a,b,c1,d,e)
         | _ => raise ERR ("dest_" ^ name) "internal arity error")
    , can (dest_n name c 5)
    )
  end

fun syntax6 name =
  let val c = astk name in
    ( c
    , fn (a,b,c1,d,e,f) => mk_n c [a,b,c1,d,e,f]
    , fn tm =>
        (case dest_n name c 6 tm of
           [a,b,c1,d,e,f] => (a,b,c1,d,e,f)
         | _ => raise ERR ("dest_" ^ name) "internal arity error")
    , can (dest_n name c 6)
    )
  end

fun syntax7 name =
  let val c = astk name in
    ( c
    , fn (a,b,c1,d,e,f,g) => mk_n c [a,b,c1,d,e,f,g]
    , fn tm =>
        (case dest_n name c 7 tm of
           [a,b,c1,d,e,f,g] => (a,b,c1,d,e,f,g)
         | _ => raise ERR ("dest_" ^ name) "internal arity error")
    , can (dest_n name c 7)
    )
  end

fun syntax9 name =
  let val c = astk name in
    ( c
    , fn (a,b,c1,d,e,f,g,h,i) => mk_n c [a,b,c1,d,e,f,g,h,i]
    , fn tm =>
        (case dest_n name c 9 tm of
           [a,b,c1,d,e,f,g,h,i] => (a,b,c1,d,e,f,g,h,i)
         | _ => raise ERR ("dest_" ^ name) "internal arity error")
    , can (dest_n name c 9)
    )
  end

fun dest_string tm = fromHOLstring tm
fun mk_string s = fromMLstring s

fun dest_term_list ty tm =
  let val (xs, elem_ty) = dest_list tm in
    if elem_ty = ty then xs else raise ERR "dest_term_list" "wrong element type"
  end

fun mk_term_list ty xs = mk_list (xs, ty)

fun dest_term_option ty tm =
  if is_none tm then (ignore (dest_none tm); NONE)
  else if is_some tm then SOME (dest_some tm)
  else raise ERR "dest_term_option" "not an option term"

fun mk_term_option ty NONE = mk_none ty
  | mk_term_option _ (SOME tm) = mk_some tm

val (Fixed_tm, mk_Fixed_tm, dest_Fixed_tm, is_Fixed) = syntax_fns1 "vyperAST" "Fixed"
val (Dynamic_tm, mk_Dynamic_tm, dest_Dynamic_tm, is_Dynamic) = syntax_fns1 "vyperAST" "Dynamic"

val (UintT_tm, mk_UintT_tm, dest_UintT_tm, is_UintT) = syntax_fns1 "vyperAST" "UintT"
val (IntT_tm, mk_IntT_tm, dest_IntT_tm, is_IntT) = syntax_fns1 "vyperAST" "IntT"
val (BoolT_tm, is_BoolT) = syntax0 "BoolT"
val (DecimalT_tm, is_DecimalT) = syntax0 "DecimalT"
val (StringT_tm, mk_StringT_tm, dest_StringT_tm, is_StringT) = syntax_fns1 "vyperAST" "StringT"
val (BytesT_tm, mk_BytesT_tm, dest_BytesT_tm, is_BytesT) = syntax_fns1 "vyperAST" "BytesT"
val (AddressT_tm, is_AddressT) = syntax0 "AddressT"

val (BaseT_tm, mk_BaseT_tm, dest_BaseT_tm, is_BaseT) = syntax_fns1 "vyperAST" "BaseT"
val (TupleT_tm, mk_TupleT_tm, dest_TupleT_tm, is_TupleT) = syntax_fns1 "vyperAST" "TupleT"
fun mk_TupleT tys = mk_TupleT_tm (mk_term_list type_ty tys)
fun dest_TupleT tm = dest_term_list type_ty (dest_TupleT_tm tm)
val (ArrayT_tm, mk_ArrayT_tm, dest_ArrayT_tm, is_ArrayT) = syntax_fns2 "vyperAST" "ArrayT"
val (StructT_tm, mk_StructT_tm, dest_StructT_tm, is_StructT) = syntax_fns1 "vyperAST" "StructT"
val (FlagT_tm, mk_FlagT_tm, dest_FlagT_tm, is_FlagT) = syntax_fns1 "vyperAST" "FlagT"
val (NoneT_tm, is_NoneT) = syntax0 "NoneT"

val (BoolL_tm, mk_BoolL_tm, dest_BoolL_tm, is_BoolL) = syntax_fns1 "vyperAST" "BoolL"
val (StringL_tm, mk_StringL_tm, dest_StringL_tm, is_StringL) = syntax_fns1 "vyperAST" "StringL"
fun mk_StringL s = mk_StringL_tm (mk_string s)
fun dest_StringL tm = dest_string (dest_StringL_tm tm)
val (BytesL_tm, mk_BytesL_tm, dest_BytesL_tm, is_BytesL) = syntax_fns1 "vyperAST" "BytesL"
val (IntL_tm, mk_IntL_tm, dest_IntL_tm, is_IntL) = syntax_fns1 "vyperAST" "IntL"
val (DecimalL_tm, mk_DecimalL_tm, dest_DecimalL_tm, is_DecimalL) = syntax_fns1 "vyperAST" "DecimalL"

val (Signed_tm, mk_Signed_tm, dest_Signed_tm, is_Signed) = syntax_fns1 "vyperAST" "Signed"
val (Unsigned_tm, mk_Unsigned_tm, dest_Unsigned_tm, is_Unsigned) = syntax_fns1 "vyperAST" "Unsigned"

val (Add_tm, is_Add) = syntax0 "Add"
val (Sub_tm, is_Sub) = syntax0 "Sub"
val (Mul_tm, is_Mul) = syntax0 "Mul"
val (Div_tm, is_Div) = syntax0 "Div"
val (UnsafeAdd_tm, is_UnsafeAdd) = syntax0 "UnsafeAdd"
val (UnsafeSub_tm, is_UnsafeSub) = syntax0 "UnsafeSub"
val (UnsafeMul_tm, is_UnsafeMul) = syntax0 "UnsafeMul"
val (UnsafeDiv_tm, is_UnsafeDiv) = syntax0 "UnsafeDiv"
val (ExpMod_tm, is_ExpMod) = syntax0 "ExpMod"
val (Mod_tm, is_Mod) = syntax0 "Mod"
val (Exp_tm, is_Exp) = syntax0 "Exp"
val (And_tm, is_And) = syntax0 "And"
val (Or_tm, is_Or) = syntax0 "Or"
val (XOr_tm, is_XOr) = syntax0 "XOr"
val (ShL_tm, is_ShL) = syntax0 "ShL"
val (ShR_tm, is_ShR) = syntax0 "ShR"
val (In_tm, is_In) = syntax0 "In"
val (NotIn_tm, is_NotIn) = syntax0 "NotIn"
val (Eq_tm, is_Eq) = syntax0 "Eq"
val (NotEq_tm, is_NotEq) = syntax0 "NotEq"
val (Lt_tm, is_Lt) = syntax0 "Lt"
val (LtE_tm, is_LtE) = syntax0 "LtE"
val (Gt_tm, is_Gt) = syntax0 "Gt"
val (GtE_tm, is_GtE) = syntax0 "GtE"
val (Min_tm, is_Min) = syntax0 "Min"
val (Max_tm, is_Max) = syntax0 "Max"

val (Sender_tm, is_Sender) = syntax0 "Sender"
val (SelfAddr_tm, is_SelfAddr) = syntax0 "SelfAddr"
val (ValueSent_tm, is_ValueSent) = syntax0 "ValueSent"
val (TimeStamp_tm, is_TimeStamp) = syntax0 "TimeStamp"
val (BlockNumber_tm, is_BlockNumber) = syntax0 "BlockNumber"
val (BlobBaseFee_tm, is_BlobBaseFee) = syntax0 "BlobBaseFee"
val (GasPrice_tm, is_GasPrice) = syntax0 "GasPrice"
val (PrevHash_tm, is_PrevHash) = syntax0 "PrevHash"
val (ChainId_tm, is_ChainId) = syntax0 "ChainId"
val (Coinbase_tm, is_Coinbase) = syntax0 "Coinbase"
val (GasLimit_tm, is_GasLimit) = syntax0 "GasLimit"
val (BaseFee_tm, is_BaseFee) = syntax0 "BaseFee"
val (PrevRandao_tm, is_PrevRandao) = syntax0 "PrevRandao"
val (TxOrigin_tm, is_TxOrigin) = syntax0 "TxOrigin"
val (MsgGas_tm, is_MsgGas) = syntax0 "MsgGas"

val (Address_tm, is_Address) = syntax0 "Address"
val (Balance_tm, is_Balance) = syntax0 "Balance"
val (Codehash_tm, is_Codehash) = syntax0 "Codehash"
val (Codesize_tm, is_Codesize) = syntax0 "Codesize"
val (IsContract_tm, is_IsContract) = syntax0 "IsContract"
val (Code_tm, is_Code) = syntax0 "Code"

val (Wei_tm, is_Wei) = syntax0 "Wei"
val (Kwei_tm, is_Kwei) = syntax0 "Kwei"
val (Mwei_tm, is_Mwei) = syntax0 "Mwei"
val (Gwei_tm, is_Gwei) = syntax0 "Gwei"
val (Szabo_tm, is_Szabo) = syntax0 "Szabo"
val (Finney_tm, is_Finney) = syntax0 "Finney"
val (Ether_tm, is_Ether) = syntax0 "Ether"
val (KEther_tm, is_KEther) = syntax0 "KEther"
val (MEther_tm, is_MEther) = syntax0 "MEther"
val (GEther_tm, is_GEther) = syntax0 "GEther"
val (TEther_tm, is_TEther) = syntax0 "TEther"

val (Len_tm, is_Len) = syntax0 "Len"
val (Not_tm, is_Not) = syntax0 "Not"
val (Neg_tm, is_Neg) = syntax0 "Neg"
val (Abs_tm, is_Abs) = syntax0 "Abs"
val (Keccak256_tm, is_Keccak256) = syntax0 "Keccak256"
val (Sha256_tm, is_Sha256) = syntax0 "Sha256"
val (AsWeiValue_tm, mk_AsWeiValue_tm, dest_AsWeiValue_tm, is_AsWeiValue) = syntax_fns1 "vyperAST" "AsWeiValue"
val (Concat_tm, mk_Concat_tm, dest_Concat_tm, is_Concat) = syntax_fns1 "vyperAST" "Concat"
val (Slice_tm, mk_Slice_tm, dest_Slice_tm, is_Slice) = syntax_fns1 "vyperAST" "Slice"
val (Uint2Str_tm, mk_Uint2Str_tm, dest_Uint2Str_tm, is_Uint2Str) = syntax_fns1 "vyperAST" "Uint2Str"
val (MakeArray_tm, mk_MakeArray_tm, dest_MakeArray_tm, is_MakeArray) = syntax_fns2 "vyperAST" "MakeArray"
val (Ceil_tm, is_Ceil) = syntax0 "Ceil"
val (Floor_tm, is_Floor) = syntax0 "Floor"
val (AddMod_tm, is_AddMod) = syntax0 "AddMod"
val (MulMod_tm, is_MulMod) = syntax0 "MulMod"
val (Bop_tm, mk_Bop_tm, dest_Bop_tm, is_Bop) = syntax_fns1 "vyperAST" "Bop"
val (BlockHash_tm, is_BlockHash) = syntax0 "BlockHash"
val (BlobHash_tm, is_BlobHash) = syntax0 "BlobHash"
val (Env_tm, mk_Env_tm, dest_Env_tm, is_Env) = syntax_fns1 "vyperAST" "Env"
val (Acc_tm, mk_Acc_tm, dest_Acc_tm, is_Acc) = syntax_fns1 "vyperAST" "Acc"
val (MethodId_tm, is_MethodId) = syntax0 "MethodId"
val (ECRecover_tm, is_ECRecover) = syntax0 "ECRecover"
val (ECAdd_tm, is_ECAdd) = syntax0 "ECAdd"
val (ECMul_tm, is_ECMul) = syntax0 "ECMul"
val (PowMod256_tm, is_PowMod256) = syntax0 "PowMod256"

val (CreateMinimalProxy_tm, is_CreateMinimalProxy) = syntax0 "CreateMinimalProxy"
val (CreateCopyOf_tm, is_CreateCopyOf) = syntax0 "CreateCopyOf"
val (CreateFromBlueprint_tm, mk_CreateFromBlueprint_tm, dest_CreateFromBlueprint_tm, is_CreateFromBlueprint) = syntax_fns2 "vyperAST" "CreateFromBlueprint"
val (RawCreate_tm, is_RawCreate) = syntax0 "RawCreate"

val (Empty_tm, is_Empty) = syntax0 "Empty"
val (MaxValue_tm, is_MaxValue) = syntax0 "MaxValue"
val (MinValue_tm, is_MinValue) = syntax0 "MinValue"
val (Epsilon_tm, is_Epsilon) = syntax0 "Epsilon"
val (Convert_tm, is_Convert) = syntax0 "Convert"
val (Extract32_tm, is_Extract32) = syntax0 "Extract32"
val (AbiDecode_tm, mk_AbiDecode_tm, dest_AbiDecode_tm, is_AbiDecode) = syntax_fns1 "vyperAST" "AbiDecode"
val (AbiEncode_tm, mk_AbiEncode_tm, dest_AbiEncode_tm, is_AbiEncode) = syntax_fns1 "vyperAST" "AbiEncode"

fun dest_string_pair_expr tm =
  let val (s, e) = dest_pair tm in (dest_string s, e) end

fun mk_string_pair_expr (s, e) = mk_pair (mk_string s, e)

val (Name_tm, mk_Name_tm, dest_Name_tm, is_Name) =
  syntax_fns2 "vyperAST" "Name"
fun mk_Name (ty, id) = mk_Name_tm (ty, mk_string id)
fun dest_Name tm = let val (ty, id) = dest_Name_tm tm in (ty, dest_string id) end

val (TopLevelName_tm, mk_TopLevelName_tm, dest_TopLevelName_tm,
     is_TopLevelName) = syntax_fns2 "vyperAST" "TopLevelName"

val (FlagMember_tm, mk_FlagMember_tm, dest_FlagMember_tm, is_FlagMember) =
  syntax_fns3 "vyperAST" "FlagMember"
fun mk_FlagMember (ty, nsid, id) = mk_FlagMember_tm (ty, nsid, mk_string id)
fun dest_FlagMember tm =
  let val (ty, nsid, id) = dest_FlagMember_tm tm in (ty, nsid, dest_string id) end

val (IfExp_tm, mk_IfExp_tm, dest_IfExp_tm, is_IfExp) =
  syntax_fns4 "vyperAST" "IfExp"

val (Literal_tm, mk_Literal_tm, dest_Literal_tm, is_Literal) =
  syntax_fns2 "vyperAST" "Literal"

val (StructLit_tm, mk_StructLit_tm, dest_StructLit_tm, is_StructLit) =
  syntax_fns3 "vyperAST" "StructLit"
fun mk_StructLit (ty, nsid, fields) =
  mk_StructLit_tm (ty, nsid, mk_term_list (mk_prod (string_ty, expr_ty))
    (map mk_string_pair_expr fields))
fun dest_StructLit tm =
  let
    val (ty, nsid, fields_tm) = dest_StructLit_tm tm
  in
    (ty, nsid, map dest_string_pair_expr
      (dest_term_list (mk_prod (string_ty, expr_ty)) fields_tm))
  end

val (Subscript_tm, mk_Subscript_tm, dest_Subscript_tm, is_Subscript) =
  syntax_fns3 "vyperAST" "Subscript"

val (Attribute_tm, mk_Attribute_tm, dest_Attribute_tm, is_Attribute) =
  syntax_fns3 "vyperAST" "Attribute"
fun mk_Attribute (ty, e, id) = mk_Attribute_tm (ty, e, mk_string id)
fun dest_Attribute tm =
  let val (ty, e, id) = dest_Attribute_tm tm in (ty, e, dest_string id) end

val (Builtin_tm, mk_Builtin_tm, dest_Builtin_tm, is_Builtin) =
  syntax_fns3 "vyperAST" "Builtin"
fun mk_Builtin (ty, b, es) = mk_Builtin_tm (ty, b, mk_term_list expr_ty es)
fun dest_Builtin tm =
  let val (ty, b, es) = dest_Builtin_tm tm in (ty, b, dest_term_list expr_ty es) end

val (TypeBuiltin_tm, mk_TypeBuiltin_tm, dest_TypeBuiltin_tm, is_TypeBuiltin) =
  syntax_fns4 "vyperAST" "TypeBuiltin"
fun mk_TypeBuiltin (ty, tb, target_ty, es) =
  mk_TypeBuiltin_tm (ty, tb, target_ty, mk_term_list expr_ty es)
fun dest_TypeBuiltin tm =
  let val (ty, tb, target_ty, es) = dest_TypeBuiltin_tm tm in
    (ty, tb, target_ty, dest_term_list expr_ty es)
  end

val (Pop_tm, mk_Pop_tm, dest_Pop_tm, is_Pop) = syntax_fns2 "vyperAST" "Pop"

val (Call_tm, mk_Call_tm, dest_Call_tm, is_Call) = syntax_fns4 "vyperAST" "Call"
fun mk_Call (ty, ct, es, drv) =
  mk_Call_tm (ty, ct, mk_term_list expr_ty es, mk_term_option expr_ty drv)
fun dest_Call tm =
  let val (ty, ct, es, drv) = dest_Call_tm tm in
    (ty, ct, dest_term_list expr_ty es, dest_term_option expr_ty drv)
  end

val (NameTarget_tm, mk_NameTarget_tm, dest_NameTarget_tm, is_NameTarget) =
  syntax_fns1 "vyperAST" "NameTarget"
fun mk_NameTarget id = mk_NameTarget_tm (mk_string id)
fun dest_NameTarget tm = dest_string (dest_NameTarget_tm tm)

val (TopLevelNameTarget_tm, mk_TopLevelNameTarget_tm,
     dest_TopLevelNameTarget_tm, is_TopLevelNameTarget) =
  syntax_fns1 "vyperAST" "TopLevelNameTarget"

val (SubscriptTarget_tm, mk_SubscriptTarget_tm, dest_SubscriptTarget_tm,
     is_SubscriptTarget) = syntax_fns2 "vyperAST" "SubscriptTarget"

val (AttributeTarget_tm, mk_AttributeTarget_tm, dest_AttributeTarget_tm,
     is_AttributeTarget) = syntax_fns2 "vyperAST" "AttributeTarget"
fun mk_AttributeTarget (bt, id) = mk_AttributeTarget_tm (bt, mk_string id)
fun dest_AttributeTarget tm =
  let val (bt, id) = dest_AttributeTarget_tm tm in (bt, dest_string id) end

val (BaseTarget_tm, mk_BaseTarget_tm, dest_BaseTarget_tm, is_BaseTarget) =
  syntax_fns1 "vyperAST" "BaseTarget"

val (TupleTarget_tm, mk_TupleTarget_tm, dest_TupleTarget_tm, is_TupleTarget) =
  syntax_fns1 "vyperAST" "TupleTarget"
fun mk_TupleTarget targets = mk_TupleTarget_tm (mk_term_list assignment_target_ty targets)
fun dest_TupleTarget tm = dest_term_list assignment_target_ty (dest_TupleTarget_tm tm)

val (Array_tm, mk_Array_tm, dest_Array_tm, is_Array) = syntax_fns1 "vyperAST" "Array"
val (Range_tm, mk_Range_tm, dest_Range_tm, is_Range) = syntax_fns2 "vyperAST" "Range"

val (Pass_tm, is_Pass) = syntax0 "Pass"
val (Continue_tm, is_Continue) = syntax0 "Continue"
val (Break_tm, is_Break) = syntax0 "Break"

val (Expr_tm, mk_Expr_tm, dest_Expr_tm, is_Expr) = syntax_fns1 "vyperAST" "Expr"
val (For_tm, mk_For_tm, dest_For_tm, is_For) = syntax5 "For"
fun mk_For (id, ty, it, bound, body) =
  mk_For_tm (mk_string id, ty, it, bound, mk_term_list stmt_ty body)
fun dest_For tm =
  let val (id, ty, it, bound, body) = dest_For_tm tm in
    (dest_string id, ty, it, bound, dest_term_list stmt_ty body)
  end

val (If_tm, mk_If_tm, dest_If_tm, is_If) = syntax_fns3 "vyperAST" "If"
fun mk_If (cond, th, el) = mk_If_tm (cond, mk_term_list stmt_ty th, mk_term_list stmt_ty el)
fun dest_If tm =
  let val (cond, th, el) = dest_If_tm tm in
    (cond, dest_term_list stmt_ty th, dest_term_list stmt_ty el)
  end

val (Assert_tm, mk_Assert_tm, dest_Assert_tm, is_Assert) =
  syntax_fns2 "vyperAST" "Assert"

val (Log_tm, mk_Log_tm, dest_Log_tm, is_Log) = syntax_fns2 "vyperAST" "Log"
fun mk_Log (id, es) = mk_Log_tm (id, mk_term_list expr_ty es)
fun dest_Log tm =
  let val (id, es) = dest_Log_tm tm in (id, dest_term_list expr_ty es) end

val (Raise_tm, mk_Raise_tm, dest_Raise_tm, is_Raise) =
  syntax_fns1 "vyperAST" "Raise"

val (Return_tm, mk_Return_tm, dest_Return_tm, is_Return) =
  syntax_fns1 "vyperAST" "Return"
fun mk_Return opt = mk_Return_tm (mk_term_option expr_ty opt)
fun dest_Return tm = dest_term_option expr_ty (dest_Return_tm tm)

val (Assign_tm, mk_Assign_tm, dest_Assign_tm, is_Assign) =
  syntax_fns2 "vyperAST" "Assign"
val (AugAssign_tm, mk_AugAssign_tm, dest_AugAssign_tm, is_AugAssign) =
  syntax_fns4 "vyperAST" "AugAssign"
val (Append_tm, mk_Append_tm, dest_Append_tm, is_Append) =
  syntax_fns2 "vyperAST" "Append"
val (AnnAssign_tm, mk_AnnAssign_tm, dest_AnnAssign_tm, is_AnnAssign) =
  syntax_fns3 "vyperAST" "AnnAssign"
fun mk_AnnAssign (id, ty, e) = mk_AnnAssign_tm (mk_string id, ty, e)
fun dest_AnnAssign tm =
  let val (id, ty, e) = dest_AnnAssign_tm tm in (dest_string id, ty, e) end

val (IntCall_tm, mk_IntCall_tm, dest_IntCall_tm, is_IntCall) =
  syntax_fns1 "vyperAST" "IntCall"
val (ExtCall_tm, mk_ExtCall_tm, dest_ExtCall_tm, is_ExtCall) =
  syntax_fns2 "vyperAST" "ExtCall"
val (Send_tm, is_Send) = syntax0 "Send"
val (RawCallTarget_tm, mk_RawCallTarget_tm, dest_RawCallTarget_tm,
     is_RawCallTarget) = syntax_fns1 "vyperAST" "RawCallTarget"
val (RawLog_tm, is_RawLog) = syntax0 "RawLog"
val (RawRevert_tm, is_RawRevert) = syntax0 "RawRevert"
val (SelfDestructTarget_tm, is_SelfDestructTarget) = syntax0 "SelfDestructTarget"
val (CreateTarget_tm, mk_CreateTarget_tm, dest_CreateTarget_tm, is_CreateTarget) =
  syntax_fns2 "vyperAST" "CreateTarget"

val (AssertBare_tm, is_AssertBare) = syntax0 "AssertBare"
val (AssertUnreachable_tm, is_AssertUnreachable) = syntax0 "AssertUnreachable"
val (AssertReason_tm, mk_AssertReason_tm, dest_AssertReason_tm, is_AssertReason) =
  syntax_fns1 "vyperAST" "AssertReason"
val (RaiseBare_tm, is_RaiseBare) = syntax0 "RaiseBare"
val (RaiseUnreachable_tm, is_RaiseUnreachable) = syntax0 "RaiseUnreachable"
val (RaiseReason_tm, mk_RaiseReason_tm, dest_RaiseReason_tm, is_RaiseReason) =
  syntax_fns1 "vyperAST" "RaiseReason"

fun mk_raw_call_flags {max_outsize, is_delegate, is_static, revert_on_failure} =
  TypeBase.mk_record
    (raw_call_flags_ty,
     [("rcf_max_outsize", max_outsize),
      ("rcf_is_delegate", is_delegate),
      ("rcf_is_static", is_static),
      ("rcf_revert_on_failure", revert_on_failure)])

fun dest_raw_call_flags tm =
  let
    val (ty, fields) = TypeBase.dest_record tm
    fun field name =
      case List.find (fn (n, _) => n = name) fields of
        SOME (_, v) => v
      | NONE => raise ERR "dest_raw_call_flags" ("missing field " ^ name)
  in
    if ty = raw_call_flags_ty then
      {max_outsize = field "rcf_max_outsize",
       is_delegate = field "rcf_is_delegate",
       is_static = field "rcf_is_static",
       revert_on_failure = field "rcf_revert_on_failure"}
    else raise ERR "dest_raw_call_flags" "wrong record type"
  end

val is_raw_call_flags = can dest_raw_call_flags

val (External_tm, is_External) = syntax0 "External"
val (Internal_tm, is_Internal) = syntax0 "Internal"
val (Deploy_tm, is_Deploy) = syntax0 "Deploy"
val (Pure_tm, is_Pure) = syntax0 "Pure"
val (View_tm, is_View) = syntax0 "View"
val (Nonpayable_tm, is_Nonpayable) = syntax0 "Nonpayable"
val (Payable_tm, is_Payable) = syntax0 "Payable"
val (Public_tm, is_Public) = syntax0 "Public"
val (Private_tm, is_Private) = syntax0 "Private"
val (Constant_tm, mk_Constant_tm, dest_Constant_tm, is_Constant) = syntax_fns1 "vyperAST" "Constant"
val (Immutable_tm, is_Immutable) = syntax0 "Immutable"
val (Transient_tm, is_Transient) = syntax0 "Transient"
val (Storage_tm, is_Storage) = syntax0 "Storage"
val (Type_tm, mk_Type_tm, dest_Type_tm, is_Type) = syntax_fns1 "vyperAST" "Type"
val (HashMapT_tm, mk_HashMapT_tm, dest_HashMapT_tm, is_HashMapT) = syntax_fns2 "vyperAST" "HashMapT"

val (FunctionDecl_tm, mk_FunctionDecl_tm, dest_FunctionDecl_tm, is_FunctionDecl) = syntax9 "FunctionDecl"
val (VariableDecl_tm, mk_VariableDecl_tm, dest_VariableDecl_tm, is_VariableDecl) = syntax5 "VariableDecl"
val (HashMapDecl_tm, mk_HashMapDecl_tm, dest_HashMapDecl_tm, is_HashMapDecl) = syntax6 "HashMapDecl"
val (StructDecl_tm, mk_StructDecl_tm, dest_StructDecl_tm, is_StructDecl) = syntax_fns2 "vyperAST" "StructDecl"
val (EventDecl_tm, mk_EventDecl_tm, dest_EventDecl_tm, is_EventDecl) = syntax_fns2 "vyperAST" "EventDecl"
val (FlagDecl_tm, mk_FlagDecl_tm, dest_FlagDecl_tm, is_FlagDecl) = syntax_fns2 "vyperAST" "FlagDecl"
val (InterfaceDecl_tm, mk_InterfaceDecl_tm, dest_InterfaceDecl_tm, is_InterfaceDecl) = syntax_fns2 "vyperAST" "InterfaceDecl"

datatype base_assignment_target_view =
    VBNameTarget of string
  | VBTopLevelNameTarget of term
  | VBSubscriptTarget of term * term
  | VBAttributeTarget of term * string

fun view_base_assignment_target tm =
  if is_NameTarget tm then VBNameTarget (dest_NameTarget tm)
  else if is_TopLevelNameTarget tm then
    VBTopLevelNameTarget (dest_TopLevelNameTarget_tm tm)
  else if is_SubscriptTarget tm then
    VBSubscriptTarget (dest_SubscriptTarget_tm tm)
  else if is_AttributeTarget tm then
    VBAttributeTarget (dest_AttributeTarget tm)
  else raise ERR "view_base_assignment_target"
    "not a vyperAST base_assignment_target constructor"

datatype assignment_target_view =
    VATBase of term
  | VATTuple of term list

fun view_assignment_target tm =
  if is_BaseTarget tm then VATBase (dest_BaseTarget_tm tm)
  else if is_TupleTarget tm then VATTuple (dest_TupleTarget tm)
  else raise ERR "view_assignment_target"
    "not a vyperAST assignment_target constructor"

datatype iterator_view =
    VIArray of term
  | VIRange of term * term

fun view_iterator tm =
  if is_Array tm then VIArray (dest_Array_tm tm)
  else if is_Range tm then VIRange (dest_Range_tm tm)
  else raise ERR "view_iterator" "not a vyperAST iterator constructor"

datatype assert_reason_view =
    VAssertBareReason
  | VAssertUnreachableReason
  | VAssertReasonExpr of term

fun view_assert_reason tm =
  if is_AssertBare tm then VAssertBareReason
  else if is_AssertUnreachable tm then VAssertUnreachableReason
  else if is_AssertReason tm then VAssertReasonExpr (dest_AssertReason_tm tm)
  else raise ERR "view_assert_reason"
    "not a vyperAST assert_reason constructor"

datatype raise_reason_view =
    VRaiseBareReason
  | VRaiseUnreachableReason
  | VRaiseReasonExpr of term

fun view_raise_reason tm =
  if is_RaiseBare tm then VRaiseBareReason
  else if is_RaiseUnreachable tm then VRaiseUnreachableReason
  else if is_RaiseReason tm then VRaiseReasonExpr (dest_RaiseReason_tm tm)
  else raise ERR "view_raise_reason"
    "not a vyperAST raise_reason constructor"

datatype expr_view =
    VName of term * string
  | VTopLevelName of term * term
  | VFlagMember of term * term * string
  | VIfExp of term * term * term * term
  | VLiteral of term * term
  | VStructLit of term * term * (string * term) list
  | VSubscript of term * term * term
  | VAttribute of term * term * string
  | VBuiltin of term * term * term list
  | VTypeBuiltin of term * term * term * term list
  | VPop of term * term
  | VCall of term * term * term list * term option

fun view_expr tm =
  if is_Name tm then VName (dest_Name tm)
  else if is_TopLevelName tm then VTopLevelName (dest_TopLevelName_tm tm)
  else if is_FlagMember tm then VFlagMember (dest_FlagMember tm)
  else if is_IfExp tm then VIfExp (dest_IfExp_tm tm)
  else if is_Literal tm then VLiteral (dest_Literal_tm tm)
  else if is_StructLit tm then VStructLit (dest_StructLit tm)
  else if is_Subscript tm then VSubscript (dest_Subscript_tm tm)
  else if is_Attribute tm then VAttribute (dest_Attribute tm)
  else if is_Builtin tm then VBuiltin (dest_Builtin tm)
  else if is_TypeBuiltin tm then VTypeBuiltin (dest_TypeBuiltin tm)
  else if is_Pop tm then VPop (dest_Pop_tm tm)
  else if is_Call tm then VCall (dest_Call tm)
  else raise ERR "view_expr" "not a vyperAST expr constructor"

datatype stmt_view =
    VPass
  | VContinue
  | VBreak
  | VExpr of term
  | VFor of string * term * term * term * term list
  | VIf of term * term list * term list
  | VAssert of term * term
  | VLog of term * term list
  | VRaise of term
  | VReturn of term option
  | VAssign of term * term
  | VAugAssign of term * term * term * term
  | VAppend of term * term
  | VAnnAssign of string * term * term

fun view_stmt tm =
  if is_Pass tm then VPass
  else if is_Continue tm then VContinue
  else if is_Break tm then VBreak
  else if is_Expr tm then VExpr (dest_Expr_tm tm)
  else if is_For tm then VFor (dest_For tm)
  else if is_If tm then VIf (dest_If tm)
  else if is_Assert tm then VAssert (dest_Assert_tm tm)
  else if is_Log tm then VLog (dest_Log tm)
  else if is_Raise tm then VRaise (dest_Raise_tm tm)
  else if is_Return tm then VReturn (dest_Return tm)
  else if is_Assign tm then VAssign (dest_Assign_tm tm)
  else if is_AugAssign tm then VAugAssign (dest_AugAssign_tm tm)
  else if is_Append tm then VAppend (dest_Append_tm tm)
  else if is_AnnAssign tm then VAnnAssign (dest_AnnAssign tm)
  else raise ERR "view_stmt" "not a vyperAST stmt constructor"

datatype call_target_view =
    VIntCall of term
  | VExtCall of term * term
  | VSend
  | VRawCallTarget of term
  | VRawLog
  | VRawRevert
  | VSelfDestructTarget
  | VCreateTarget of term * term

fun view_call_target tm =
  if is_IntCall tm then VIntCall (dest_IntCall_tm tm)
  else if is_ExtCall tm then VExtCall (dest_ExtCall_tm tm)
  else if is_Send tm then VSend
  else if is_RawCallTarget tm then VRawCallTarget (dest_RawCallTarget_tm tm)
  else if is_RawLog tm then VRawLog
  else if is_RawRevert tm then VRawRevert
  else if is_SelfDestructTarget tm then VSelfDestructTarget
  else if is_CreateTarget tm then VCreateTarget (dest_CreateTarget_tm tm)
  else raise ERR "view_call_target" "not a vyperAST call_target constructor"

datatype toplevel_view =
    VFunctionDecl of term * term * term * term * term * term * term * term * term
  | VVariableDecl of term * term * term * term * term
  | VHashMapDecl of term * term * term * term * term * term
  | VStructDecl of term * term
  | VEventDecl of term * term
  | VFlagDecl of term * term
  | VInterfaceDecl of term * term

fun view_toplevel tm =
  if is_FunctionDecl tm then VFunctionDecl (dest_FunctionDecl_tm tm)
  else if is_VariableDecl tm then VVariableDecl (dest_VariableDecl_tm tm)
  else if is_HashMapDecl tm then VHashMapDecl (dest_HashMapDecl_tm tm)
  else if is_StructDecl tm then VStructDecl (dest_StructDecl_tm tm)
  else if is_EventDecl tm then VEventDecl (dest_EventDecl_tm tm)
  else if is_FlagDecl tm then VFlagDecl (dest_FlagDecl_tm tm)
  else if is_InterfaceDecl tm then VInterfaceDecl (dest_InterfaceDecl_tm tm)
  else raise ERR "view_toplevel" "not a vyperAST toplevel constructor"

end
