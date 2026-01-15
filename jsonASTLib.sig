(* jsonASTLib.sig - Signature for JSON to jsonAST parser *)

signature jsonASTLib = sig
  include Abbrev

  (* ===== Types ===== *)
  val json_typeclass_ty : hol_type
  val json_type_ty : hol_type
  val json_binop_ty : hol_type
  val json_unaryop_ty : hol_type
  val json_boolop_ty : hol_type
  val json_expr_ty : hol_type
  val json_keyword_ty : hol_type
  val json_stmt_ty : hol_type
  val json_iter_ty : hol_type
  val json_base_target_ty : hol_type
  val json_target_ty : hol_type
  val json_decorator_ty : hol_type
  val json_arg_ty : hol_type
  val json_func_type_ty : hol_type
  val json_value_type_ty : hol_type
  val json_toplevel_ty : hol_type
  val json_module_ty : hol_type

  (* ===== Typeclass Constructors ===== *)
  val TC_integer_tm : term
  val TC_bytes_m_tm : term
  val TC_static_array_tm : term
  val TC_dynamic_array_tm : term
  val TC_struct_tm : term
  val TC_flag_tm : term
  val TC_tuple_tm : term
  val TC_hashmap_tm : term
  val TC_interface_tm : term
  val TC_contract_function_tm : term
  val TC_builtin_function_tm : term
  val TC_module_tm : term
  val TC_other_tm : term
  val mk_TC_other : string -> term

  (* ===== Type Constructors ===== *)
  val JT_Named_tm : term
  val JT_Integer_tm : term
  val JT_BytesM_tm : term
  val JT_String_tm : term
  val JT_Bytes_tm : term
  val JT_StaticArray_tm : term
  val JT_DynArray_tm : term
  val JT_Struct_tm : term
  val JT_Flag_tm : term
  val JT_Tuple_tm : term
  val JT_HashMap_tm : term
  val JT_None_tm : term

  val mk_JT_Named : string -> term
  val mk_JT_Integer : term * bool -> term
  val mk_JT_BytesM : term -> term
  val mk_JT_String : term -> term
  val mk_JT_Bytes : term -> term
  val mk_JT_StaticArray : term * term -> term
  val mk_JT_DynArray : term * term -> term
  val mk_JT_Struct : string -> term
  val mk_JT_Flag : string -> term
  val mk_JT_Tuple : term list -> term
  val mk_JT_HashMap : term * term -> term

  (* ===== Operator Constructors ===== *)
  val JBop_Add_tm : term
  val JBop_Sub_tm : term
  val JBop_Mult_tm : term
  val JBop_Div_tm : term
  val JBop_FloorDiv_tm : term
  val JBop_Mod_tm : term
  val JBop_Pow_tm : term
  val JBop_And_tm : term
  val JBop_Or_tm : term
  val JBop_BitAnd_tm : term
  val JBop_BitOr_tm : term
  val JBop_BitXor_tm : term
  val JBop_LShift_tm : term
  val JBop_RShift_tm : term
  val JBop_Eq_tm : term
  val JBop_NotEq_tm : term
  val JBop_Lt_tm : term
  val JBop_LtE_tm : term
  val JBop_Gt_tm : term
  val JBop_GtE_tm : term
  val JBop_In_tm : term
  val JBop_NotIn_tm : term

  val JUop_USub_tm : term
  val JUop_Not_tm : term
  val JUop_Invert_tm : term

  val JBoolop_And_tm : term
  val JBoolop_Or_tm : term

  (* ===== Expression Constructors ===== *)
  val JE_Int_tm : term
  val JE_Decimal_tm : term
  val JE_Str_tm : term
  val JE_Bytes_tm : term
  val JE_Hex_tm : term
  val JE_Bool_tm : term
  val JE_Name_tm : term
  val JE_Attribute_tm : term
  val JE_Subscript_tm : term
  val JE_BinOp_tm : term
  val JE_BoolOp_tm : term
  val JE_UnaryOp_tm : term
  val JE_IfExp_tm : term
  val JE_Tuple_tm : term
  val JE_List_tm : term
  val JE_Call_tm : term
  val JKeyword_tm : term

  val mk_JE_Int : term * term -> term
  val mk_JE_Decimal : string -> term
  val mk_JE_Str : term * string -> term
  val mk_JE_Bytes : term * string -> term
  val mk_JE_Hex : string -> term
  val mk_JE_Bool : bool -> term
  val mk_JE_Name : string * string option -> term
  val mk_JE_Attribute : term * string -> term
  val mk_JE_Subscript : term * term -> term
  val mk_JE_BinOp : term * term * term -> term
  val mk_JE_BoolOp : term * term list -> term
  val mk_JE_UnaryOp : term * term -> term
  val mk_JE_IfExp : term * term * term -> term
  val mk_JE_Tuple : term list -> term
  val mk_JE_List : term list * term -> term
  val mk_JE_Call : term * term list * term list * term * int option -> term
  val mk_JKeyword : string * term -> term

  (* ===== Statement Constructors ===== *)
  val JS_Pass_tm : term
  val JS_Break_tm : term
  val JS_Continue_tm : term
  val JS_Expr_tm : term
  val JS_Return_tm : term
  val JS_Raise_tm : term
  val JS_Assert_tm : term
  val JS_Log_tm : term
  val JS_If_tm : term
  val JS_For_tm : term
  val JS_Assign_tm : term
  val JS_AnnAssign_tm : term
  val JS_AugAssign_tm : term
  val JS_Append_tm : term

  val mk_JS_Expr : term -> term
  val mk_JS_Return : term option -> term
  val mk_JS_Raise : term option -> term
  val mk_JS_Assert : term * term option -> term
  val mk_JS_Log : string * term list -> term
  val mk_JS_If : term * term list * term list -> term
  val mk_JS_For : string * term * term * term list -> term
  val mk_JS_Assign : term * term -> term
  val mk_JS_AnnAssign : string * term * term -> term
  val mk_JS_AugAssign : term * term * term -> term
  val mk_JS_Append : term * term -> term

  (* ===== Iterator Constructors ===== *)
  val JIter_Range_tm : term
  val JIter_Array_tm : term

  val mk_JIter_Range : term * term option -> term
  val mk_JIter_Array : term * term -> term

  (* ===== Target Constructors ===== *)
  val JBT_Name_tm : term
  val JBT_TopLevelName_tm : term
  val JBT_Subscript_tm : term
  val JBT_Attribute_tm : term
  val JTgt_Base_tm : term
  val JTgt_Tuple_tm : term

  val mk_JBT_Name : string -> term
  val mk_JBT_TopLevelName : string -> term
  val mk_JBT_Subscript : term * term -> term
  val mk_JBT_Attribute : term * string -> term
  val mk_JTgt_Base : term -> term
  val mk_JTgt_Tuple : term list -> term

  (* ===== Top-level Constructors ===== *)
  val JDec_tm : term
  val JArg_tm : term
  val JFuncType_tm : term
  val JVT_Type_tm : term
  val JVT_HashMap_tm : term
  val JTL_FunctionDef_tm : term
  val JTL_VariableDecl_tm : term
  val JTL_HashMapDecl_tm : term
  val JTL_EventDef_tm : term
  val JTL_StructDef_tm : term
  val JTL_FlagDef_tm : term
  val JTL_InterfaceDef_tm : term
  val JModule_tm : term

  val mk_JDec : string -> term
  val mk_JArg : string * term -> term
  val mk_JFuncType : term list * term -> term
  val mk_JVT_Type : term -> term
  val mk_JVT_HashMap : term * term -> term
  val mk_JTL_FunctionDef : string * string list * term list * term * term list -> term
  val mk_JTL_VariableDecl : string * term * bool * bool * bool * term option -> term
  val mk_JTL_HashMapDecl : string * term * term * bool * bool -> term
  val mk_JTL_EventDef : string * term list -> term
  val mk_JTL_StructDef : string * term list -> term
  val mk_JTL_FlagDef : string * string list -> term
  val mk_JTL_InterfaceDef : string -> term
  val mk_JModule : term list -> term

  (* ===== Decoders ===== *)
  val json_type : term JSONDecode.decoder
  val ast_type : term JSONDecode.decoder
  val json_binop : term JSONDecode.decoder
  val json_unaryop : term JSONDecode.decoder
  val json_boolop : term JSONDecode.decoder
  val json_expr : term JSONDecode.decoder
  val json_keyword : term JSONDecode.decoder
  val json_stmt : term JSONDecode.decoder
  val json_base_target : term JSONDecode.decoder
  val json_target : term JSONDecode.decoder
  val json_arg : term JSONDecode.decoder
  val json_func_type : term JSONDecode.decoder
  val json_value_type : term JSONDecode.decoder
  val json_toplevel : term JSONDecode.decoder
  val json_module : term JSONDecode.decoder
  val json_imported_module : term JSONDecode.decoder
  val annotated_ast : term JSONDecode.decoder
  val annotated_ast_simple : term JSONDecode.decoder

end
