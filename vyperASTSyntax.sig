signature vyperASTSyntax = sig
  include Abbrev

  val Fixed_tm        : term
  val Dynamic_tm      : term
  val UintT_tm        : term
  val IntT_tm         : term
  val BoolT_tm        : term
  val DecimalT_tm     : term
  val StringT_tm      : term
  val BytesT_tm       : term
  val AddressT_tm     : term
  val BaseT_tm        : term
  val TupleT_tm       : term
  val ArrayT_tm       : term
  val StructT_tm      : term
  val FlagT_tm        : term
  val NoneT_tm        : term
  val Signed_tm       : term
  val Unsigned_tm     : term
  val BoolL_tm        : term
  val StringL_tm      : term
  val BytesL_tm       : term
  val IntL_tm         : term
  val DecimalL_tm     : term
  val Add_tm          : term
  val Sub_tm          : term
  val Mul_tm          : term
  val Div_tm          : term
  val UAdd_tm         : term
  val USub_tm         : term
  val UMul_tm         : term
  val UDiv_tm         : term
  val Mod_tm          : term
  val Exp_tm          : term
  val And_tm          : term
  val Or_tm           : term
  val XOr_tm          : term
  val ShL_tm          : term
  val ShR_tm          : term
  val In_tm           : term
  val NotIn_tm        : term
  val Eq_tm           : term
  val NotEq_tm        : term
  val Lt_tm           : term
  val LtE_tm          : term
  val Gt_tm           : term
  val GtE_tm          : term
  val Sender_tm       : term
  val SelfAddr_tm     : term
  val TimeStamp_tm    : term
  val Address_tm      : term
  val Balance_tm      : term
  val Wei_tm          : term
  val Kwei_tm         : term
  val Mwei_tm         : term
  val Gwei_tm         : term
  val Szabo_tm        : term
  val Finney_tm       : term
  val Ether_tm        : term
  val KEther_tm       : term
  val MEther_tm       : term
  val GEther_tm       : term
  val TEther_tm       : term
  val Len_tm          : term
  val Not_tm          : term
  val Neg_tm          : term
  val Keccak256_tm    : term
  val Concat_tm       : term
  val Slice_tm        : term
  val MakeArray_tm    : term
  val Floor_tm        : term
  val Bop_tm          : term
  val Env_tm          : term
  val Acc_tm          : term
  val BlockHash_tm    : term
  val IntCall_tm      : term
  val Send_tm         : term
  val Empty_tm        : term
  val MaxValue_tm     : term
  val MinValue_tm     : term
  val Epsilon_tm      : term
  val Convert_tm      : term
  val Name_tm         : term
  val TopLevelName_tm : term
  val IfExp_tm        : term
  val Literal_tm      : term
  val StructLit_tm    : term
  val Subscript_tm    : term
  val Attribute_tm    : term
  val Builtin_tm      : term
  val TypeBuiltin_tm  : term
  val Pop_tm          : term
  val AstCall_tm      : term
  val NameTarget_tm   : term
  val TopLevelNameTarget_tm : term
  val SubscriptTarget_tm    : term
  val AttributeTarget_tm    : term
  val BaseTarget_tm   : term
  val TupleTarget_tm  : term
  val Array_tm        : term
  val Range_tm        : term
  val Pass_tm         : term
  val Continue_tm     : term
  val Break_tm        : term
  val Expr_tm         : term
  val For_tm          : term
  val If_tm           : term
  val Assert_tm       : term
  val Log_tm          : term
  val Raise_tm        : term
  val Return_tm       : term
  val Assign_tm       : term
  val AugAssign_tm    : term
  val Append_tm       : term
  val AnnAssign_tm    : term
  val External_tm     : term
  val Internal_tm     : term
  val Deploy_tm       : term
  val Pure_tm         : term
  val View_tm         : term
  val Nonpayable_tm   : term
  val Payable_tm      : term
  val Public_tm       : term
  val Private_tm      : term
  val Constant_tm     : term
  val Immutable_tm    : term
  val Transient_tm    : term
  val Storage_tm      : term
  val Type_tm         : term
  val HashMapT_tm     : term
  val FunctionDecl_tm : term
  val VariableDecl_tm : term
  val HashMapDecl_tm  : term
  val StructDecl_tm   : term
  val EventDecl_tm    : term
  val FlagDecl_tm     : term

  val type_ty       : hol_type
  val stmt_ty       : hol_type
  val expr_ty       : hol_type
  val toplevel_ty   : hol_type

  val identifier_ty : hol_type
  val argument_ty   : hol_type

  val bool_tm      : term
  val address_tm   : term
  val decimal_tm   : term
  val mk_Fixed     : term -> term
  val mk_Dynamic   : term -> term
  val mk_Signed    : term -> term
  val mk_Unsigned  : term -> term
  val mk_uint      : term -> term
  val mk_int       : term -> term
  val mk_bytes     : term -> term
  val mk_FunctionDecl : term -> term -> term -> term -> term -> term -> term
  val mk_VariableDecl : term * term * term * term -> term
  val mk_HashMapDecl  : term * term * term * term * term -> term
  val mk_String    : term -> term
  val mk_Bytes     : term -> term
  val mk_BytesM    : term -> term
  val mk_Expr      : term -> term
  val mk_For       : term -> term -> term -> term -> term -> term
  val mk_Name      : string -> term
  val mk_StructLit : term * term list -> term
  val mk_IfExp     : term * term * term -> term
  val mk_IntCall   : term -> term
  val mk_Empty     : term -> term
  val mk_MaxValue  : term -> term
  val mk_MinValue  : term -> term
  val mk_Convert   : term * term -> term
  val mk_Call      : term -> term list -> term
  val mk_Assert    : term * term -> term
  val mk_Log       : term * term -> term
  val mk_Subscript : term -> term -> term
  val mk_If        : term -> term -> term -> term
  val mk_li        : term * term -> term
  val mk_ld        : term -> term
  val mk_lb        : term -> term
  val mk_ls        : term * string -> term
  val empty_lstr   : term
  val mk_Return    : term option -> term
  val mk_AnnAssign : term * term * term -> term
  val mk_AugAssign : term -> term -> term -> term
  val mk_Hex_dyn   : term * string -> term
  val mk_Hex       : string -> term
  val mk_Builtin   : term -> term -> term
  val mk_Concat    : term -> term
  val mk_Slice     : term -> term
  val mk_Not       : term -> term
  val mk_Neg       : term -> term
  val mk_Keccak256 : term -> term
  val mk_AsWeiValue : (term * term) -> term
  val mk_Floor     : term -> term
  val mk_Bop       : term -> term
  val mk_Len       : term -> term
  val mk_MakeArray : term * term * term list -> term
  val mk_Tuple     : term list -> term
  val mk_SArray    : term * term list -> term
  val msg_sender_tm    : term
  val self_addr_tm     : term
  val time_stamp_tm    : term
  val block_number_tm  : term
  val blob_base_fee_tm : term
  val gas_price_tm     : term
  val prev_hash_tm     : term
  val mk_BlockHash : term -> term

end
