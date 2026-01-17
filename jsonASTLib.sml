(* jsonASTLib.sml - Parse JSON into jsonAST HOL terms
 *
 * This is a "dumb" parser that mirrors JSON structure exactly.
 * NO semantic decisions (msg.sender recognition, loop bounds, etc.)
 * Those are handled in jsonToVyperScript.sml (Phase 3).
 *)

structure jsonASTLib :> jsonASTLib = struct

open HolKernel boolLib
open pairSyntax listSyntax stringSyntax optionSyntax numSyntax intSyntax
open jsonASTTheory JSONDecode

(* ===== HOL Term Helpers ===== *)

fun jastk s = prim_mk_const{Thy="jsonAST",Name=s}
fun jasty s = mk_thy_type{Thy="jsonAST",Tyop=s,Args=[]};

(* nsid: namespaced identifier (num option # string) *)
fun mk_nsid (src_id_opt, name) =
  mk_pair(src_id_opt, fromMLstring name);

fun mk_nsid_none name = mk_nsid(mk_none num, name);

(* ===== Types ===== *)

val json_typeclass_ty = jasty "json_typeclass"
val json_type_ty = jasty "json_type"
val json_binop_ty = jasty "json_binop"
val json_unaryop_ty = jasty "json_unaryop"
val json_boolop_ty = jasty "json_boolop"
val json_expr_ty = jasty "json_expr"
val json_keyword_ty = jasty "json_keyword"
val json_stmt_ty = jasty "json_stmt"
val json_iter_ty = jasty "json_iter"
val json_base_target_ty = jasty "json_base_target"
val json_target_ty = jasty "json_target"
val json_decorator_ty = jasty "json_decorator"
val json_arg_ty = jasty "json_arg"
val json_func_type_ty = jasty "json_func_type"
val json_value_type_ty = jasty "json_value_type"
val json_import_info_ty = jasty "json_import_info"
val json_toplevel_ty = jasty "json_toplevel"
val json_module_ty = jasty "json_module"

(* ===== Typeclass Constructors ===== *)

val TC_integer_tm = jastk "TC_integer"
val TC_bytes_m_tm = jastk "TC_bytes_m"
val TC_static_array_tm = jastk "TC_static_array"
val TC_dynamic_array_tm = jastk "TC_dynamic_array"
val TC_struct_tm = jastk "TC_struct"
val TC_flag_tm = jastk "TC_flag"
val TC_tuple_tm = jastk "TC_tuple"
val TC_hashmap_tm = jastk "TC_hashmap"
val TC_interface_tm = jastk "TC_interface"
val TC_contract_function_tm = jastk "TC_contract_function"
val TC_builtin_function_tm = jastk "TC_builtin_function"
val TC_module_tm = jastk "TC_module"
val TC_other_tm = jastk "TC_other"

fun mk_TC_other s = mk_comb(TC_other_tm, fromMLstring s)

(* ===== Type Constructors ===== *)

val JT_Named_tm = jastk "JT_Named"
val JT_Integer_tm = jastk "JT_Integer"
val JT_BytesM_tm = jastk "JT_BytesM"
val JT_String_tm = jastk "JT_String"
val JT_Bytes_tm = jastk "JT_Bytes"
val JT_StaticArray_tm = jastk "JT_StaticArray"
val JT_DynArray_tm = jastk "JT_DynArray"
val JT_Struct_tm = jastk "JT_Struct"
val JT_Flag_tm = jastk "JT_Flag"
val JT_Tuple_tm = jastk "JT_Tuple"
val JT_HashMap_tm = jastk "JT_HashMap"
val JT_None_tm = jastk "JT_None"

fun mk_JT_Named s = mk_comb(JT_Named_tm, fromMLstring s)
fun mk_JT_Integer (bits, is_signed) =
  list_mk_comb(JT_Integer_tm, [bits, mk_bool is_signed])
fun mk_JT_BytesM m = mk_comb(JT_BytesM_tm, m)
fun mk_JT_String len = mk_comb(JT_String_tm, len)
fun mk_JT_Bytes len = mk_comb(JT_Bytes_tm, len)
fun mk_JT_StaticArray (vt, len) = list_mk_comb(JT_StaticArray_tm, [vt, len])
fun mk_JT_DynArray (vt, len) = list_mk_comb(JT_DynArray_tm, [vt, len])
fun mk_JT_Struct s = mk_comb(JT_Struct_tm, fromMLstring s)
fun mk_JT_Flag s = mk_comb(JT_Flag_tm, fromMLstring s)
fun mk_JT_Tuple ts = mk_comb(JT_Tuple_tm, mk_list(ts, json_type_ty))
fun mk_JT_HashMap (kt, vt) = list_mk_comb(JT_HashMap_tm, [kt, vt])

(* ===== Operator Constructors ===== *)

val JBop_Add_tm = jastk "JBop_Add"
val JBop_Sub_tm = jastk "JBop_Sub"
val JBop_Mult_tm = jastk "JBop_Mult"
val JBop_Div_tm = jastk "JBop_Div"
val JBop_FloorDiv_tm = jastk "JBop_FloorDiv"
val JBop_Mod_tm = jastk "JBop_Mod"
val JBop_Pow_tm = jastk "JBop_Pow"
val JBop_And_tm = jastk "JBop_And"
val JBop_Or_tm = jastk "JBop_Or"
val JBop_BitAnd_tm = jastk "JBop_BitAnd"
val JBop_BitOr_tm = jastk "JBop_BitOr"
val JBop_BitXor_tm = jastk "JBop_BitXor"
val JBop_LShift_tm = jastk "JBop_LShift"
val JBop_RShift_tm = jastk "JBop_RShift"
val JBop_Eq_tm = jastk "JBop_Eq"
val JBop_NotEq_tm = jastk "JBop_NotEq"
val JBop_Lt_tm = jastk "JBop_Lt"
val JBop_LtE_tm = jastk "JBop_LtE"
val JBop_Gt_tm = jastk "JBop_Gt"
val JBop_GtE_tm = jastk "JBop_GtE"
val JBop_In_tm = jastk "JBop_In"
val JBop_NotIn_tm = jastk "JBop_NotIn"

val JUop_USub_tm = jastk "JUop_USub"
val JUop_Not_tm = jastk "JUop_Not"
val JUop_Invert_tm = jastk "JUop_Invert"

val JBoolop_And_tm = jastk "JBoolop_And"
val JBoolop_Or_tm = jastk "JBoolop_Or"

(* ===== Expression Constructors ===== *)

val JE_Int_tm = jastk "JE_Int"
val JE_Decimal_tm = jastk "JE_Decimal"
val JE_Str_tm = jastk "JE_Str"
val JE_Bytes_tm = jastk "JE_Bytes"
val JE_Hex_tm = jastk "JE_Hex"
val JE_Bool_tm = jastk "JE_Bool"
val JE_Name_tm = jastk "JE_Name"
val JE_Attribute_tm = jastk "JE_Attribute"
val JE_Subscript_tm = jastk "JE_Subscript"
val JE_BinOp_tm = jastk "JE_BinOp"
val JE_BoolOp_tm = jastk "JE_BoolOp"
val JE_UnaryOp_tm = jastk "JE_UnaryOp"
val JE_IfExp_tm = jastk "JE_IfExp"
val JE_Tuple_tm = jastk "JE_Tuple"
val JE_List_tm = jastk "JE_List"
val JE_Call_tm = jastk "JE_Call"

val JKeyword_tm = jastk "JKeyword"

fun mk_JE_Int (v, ty) = list_mk_comb(JE_Int_tm, [v, ty])
fun mk_JE_Decimal s = mk_comb(JE_Decimal_tm, fromMLstring s)
fun mk_JE_Str (len, v) = list_mk_comb(JE_Str_tm, [len, fromMLstring v])
fun mk_JE_Bytes (len, v) = list_mk_comb(JE_Bytes_tm, [len, fromMLstring v])
fun mk_JE_Hex s = mk_comb(JE_Hex_tm, fromMLstring s)
fun mk_JE_Bool b = mk_comb(JE_Bool_tm, mk_bool b)
fun mk_JE_Name (s, tc_opt, src_id_opt) =
  list_mk_comb(JE_Name_tm, [fromMLstring s,
                           lift_option (mk_option string_ty) fromMLstring tc_opt,
                           src_id_opt])
fun mk_JE_Attribute (e, attr) = list_mk_comb(JE_Attribute_tm, [e, fromMLstring attr])
fun mk_JE_Subscript (e1, e2) = list_mk_comb(JE_Subscript_tm, [e1, e2])
fun mk_JE_BinOp (l, op_tm, r) = list_mk_comb(JE_BinOp_tm, [l, op_tm, r])
fun mk_JE_BoolOp (op_tm, es) = list_mk_comb(JE_BoolOp_tm, [op_tm, mk_list(es, json_expr_ty)])
fun mk_JE_UnaryOp (op_tm, e) = list_mk_comb(JE_UnaryOp_tm, [op_tm, e])
fun mk_JE_IfExp (test, body, els) = list_mk_comb(JE_IfExp_tm, [test, body, els])
fun mk_JE_Tuple es = mk_comb(JE_Tuple_tm, mk_list(es, json_expr_ty))
fun mk_JE_List (es, ty) = list_mk_comb(JE_List_tm, [mk_list(es, json_expr_ty), ty])
fun mk_JE_Call (func, args, kwargs, ty, src_id_opt_tm) =
  list_mk_comb(JE_Call_tm, [func, mk_list(args, json_expr_ty),
                            mk_list(kwargs, json_keyword_ty), ty, src_id_opt_tm])
fun mk_JKeyword (arg, v) = list_mk_comb(JKeyword_tm, [fromMLstring arg, v])

(* ===== Statement Constructors ===== *)

val JS_Pass_tm = jastk "JS_Pass"
val JS_Break_tm = jastk "JS_Break"
val JS_Continue_tm = jastk "JS_Continue"
val JS_Expr_tm = jastk "JS_Expr"
val JS_Return_tm = jastk "JS_Return"
val JS_Raise_tm = jastk "JS_Raise"
val JS_Assert_tm = jastk "JS_Assert"
val JS_Log_tm = jastk "JS_Log"
val JS_If_tm = jastk "JS_If"
val JS_For_tm = jastk "JS_For"
val JS_Assign_tm = jastk "JS_Assign"
val JS_AnnAssign_tm = jastk "JS_AnnAssign"
val JS_AugAssign_tm = jastk "JS_AugAssign"
val JS_Append_tm = jastk "JS_Append"

fun mk_JS_Expr e = mk_comb(JS_Expr_tm, e)
fun mk_JS_Return eopt = mk_comb(JS_Return_tm, lift_option (mk_option json_expr_ty) I eopt)
fun mk_JS_Raise eopt = mk_comb(JS_Raise_tm, lift_option (mk_option json_expr_ty) I eopt)
fun mk_JS_Assert (test, msgopt) =
  list_mk_comb(JS_Assert_tm, [test, lift_option (mk_option json_expr_ty) I msgopt])
fun mk_JS_Log (nsid, args) =
  list_mk_comb(JS_Log_tm, [nsid, mk_list(args, json_expr_ty)])
fun mk_JS_If (test, body, els) =
  list_mk_comb(JS_If_tm, [test, mk_list(body, json_stmt_ty), mk_list(els, json_stmt_ty)])
fun mk_JS_For (var, ty, iter, body) =
  list_mk_comb(JS_For_tm, [fromMLstring var, ty, iter, mk_list(body, json_stmt_ty)])
fun mk_JS_Assign (tgt, v) = list_mk_comb(JS_Assign_tm, [tgt, v])
fun mk_JS_AnnAssign (var, ty, v) =
  list_mk_comb(JS_AnnAssign_tm, [fromMLstring var, ty, v])
fun mk_JS_AugAssign (tgt, op_tm, v) = list_mk_comb(JS_AugAssign_tm, [tgt, op_tm, v])
fun mk_JS_Append (tgt, v) = list_mk_comb(JS_Append_tm, [tgt, v])

(* ===== Iterator Constructors ===== *)

val JIter_Range_tm = jastk "JIter_Range"
val JIter_Array_tm = jastk "JIter_Array"

fun mk_JIter_Range (args, boundopt) =
  list_mk_comb(JIter_Range_tm,
    [args,
     lift_option (mk_option num) I boundopt])
fun mk_JIter_Array (e, ty) = list_mk_comb(JIter_Array_tm, [e, ty])

(* ===== Target Constructors ===== *)

val JBT_Name_tm = jastk "JBT_Name"
val JBT_TopLevelName_tm = jastk "JBT_TopLevelName"
val JBT_Subscript_tm = jastk "JBT_Subscript"
val JBT_Attribute_tm = jastk "JBT_Attribute"
val JTgt_Base_tm = jastk "JTgt_Base"
val JTgt_Tuple_tm = jastk "JTgt_Tuple"

fun mk_JBT_Name s = mk_comb(JBT_Name_tm, fromMLstring s)
fun mk_JBT_TopLevelName nsid = mk_comb(JBT_TopLevelName_tm, nsid)
fun mk_JBT_Subscript (bt, e) = list_mk_comb(JBT_Subscript_tm, [bt, e])
fun mk_JBT_Attribute (bt, attr) = list_mk_comb(JBT_Attribute_tm, [bt, fromMLstring attr])
fun mk_JTgt_Base bt = mk_comb(JTgt_Base_tm, bt)
fun mk_JTgt_Tuple ts = mk_comb(JTgt_Tuple_tm, mk_list(ts, json_target_ty))

(* ===== Top-level Constructors ===== *)

val JDec_tm = jastk "JDec"
val JArg_tm = jastk "JArg"
val JFuncType_tm = jastk "JFuncType"
val JVT_Type_tm = jastk "JVT_Type"
val JVT_HashMap_tm = jastk "JVT_HashMap"
val JTL_FunctionDef_tm = jastk "JTL_FunctionDef"
val JTL_VariableDecl_tm = jastk "JTL_VariableDecl"
val JTL_HashMapDecl_tm = jastk "JTL_HashMapDecl"
val JTL_EventDef_tm = jastk "JTL_EventDef"
val JTL_StructDef_tm = jastk "JTL_StructDef"
val JTL_FlagDef_tm = jastk "JTL_FlagDef"
val JTL_InterfaceDef_tm = jastk "JTL_InterfaceDef"
val JTL_Import_tm = jastk "JTL_Import"
val JTL_ExportsDecl_tm = jastk "JTL_ExportsDecl"
val JTL_InitializesDecl_tm = jastk "JTL_InitializesDecl"
val JTL_UsesDecl_tm = jastk "JTL_UsesDecl"
val JTL_ImplementsDecl_tm = jastk "JTL_ImplementsDecl"
val JImportInfo_tm = jastk "JImportInfo"
val JModule_tm = jastk "JModule"
val JImportedModule_tm = jastk "JImportedModule"
val JAnnotatedAST_tm = jastk "JAnnotatedAST"

fun mk_JDec s = mk_comb(JDec_tm, fromMLstring s)
fun mk_JArg (name, ty) = list_mk_comb(JArg_tm, [fromMLstring name, ty])
fun mk_JFuncType (argtys, retty) =
  list_mk_comb(JFuncType_tm, [mk_list(argtys, json_type_ty), retty])
fun mk_JVT_Type ty = mk_comb(JVT_Type_tm, ty)
fun mk_JVT_HashMap (kt, vt) = list_mk_comb(JVT_HashMap_tm, [kt, vt])
fun mk_JTL_FunctionDef (name, decs, args, func_type, body) =
  list_mk_comb(JTL_FunctionDef_tm,
    [fromMLstring name,
     mk_list(List.map fromMLstring decs, string_ty),
     mk_list(args, json_arg_ty),
     func_type,
     mk_list(body, json_stmt_ty)])
fun mk_JTL_VariableDecl (name, ty, is_public, is_immutable, is_transient, valopt) =
  list_mk_comb(JTL_VariableDecl_tm,
    [fromMLstring name, ty, mk_bool is_public, mk_bool is_immutable,
     mk_bool is_transient, lift_option (mk_option json_expr_ty) I valopt])
fun mk_JTL_HashMapDecl (name, kt, vt, is_public, is_transient) =
  list_mk_comb(JTL_HashMapDecl_tm,
    [fromMLstring name, kt, vt, mk_bool is_public, mk_bool is_transient])
fun mk_JTL_EventDef (name, args) =
  list_mk_comb(JTL_EventDef_tm, [fromMLstring name, mk_list(args, json_arg_ty)])
fun mk_JTL_StructDef (name, args) =
  list_mk_comb(JTL_StructDef_tm, [fromMLstring name, mk_list(args, json_arg_ty)])
fun mk_JTL_FlagDef (name, members) =
  list_mk_comb(JTL_FlagDef_tm,
    [fromMLstring name, mk_list(List.map fromMLstring members, string_ty)])
fun mk_JTL_InterfaceDef name = mk_comb(JTL_InterfaceDef_tm, fromMLstring name)
fun mk_JImportInfo (alias, path, qual_name) =
  list_mk_comb(JImportInfo_tm,
    [fromMLstring alias, fromMLstring path, fromMLstring qual_name])
fun mk_JTL_Import infos =
  mk_comb(JTL_Import_tm, mk_list(infos, json_import_info_ty))
fun mk_JTL_ExportsDecl ann = mk_comb(JTL_ExportsDecl_tm, ann)
fun mk_JTL_InitializesDecl ann = mk_comb(JTL_InitializesDecl_tm, ann)
fun mk_JTL_UsesDecl ann = mk_comb(JTL_UsesDecl_tm, ann)
fun mk_JTL_ImplementsDecl ann = mk_comb(JTL_ImplementsDecl_tm, ann)
fun mk_JModule tls = mk_comb(JModule_tm, mk_list(tls, json_toplevel_ty))
fun mk_JImportedModule (src_id_tm, path, body) =
  list_mk_comb(JImportedModule_tm,
    [src_id_tm,
     fromMLstring path,
     mk_list(body, json_toplevel_ty)])
fun mk_JAnnotatedAST (main_ast, imports) =
  list_mk_comb(JAnnotatedAST_tm,
    [main_ast,
     mk_list(imports, mk_type("json_imported_module", []))])

(* ===== Decoder Helpers ===== *)

(* Helper to check a field equals a specific string *)
fun check cd pred err d =
  andThen cd (fn x => if pred x then d else fail err)

fun check_field lab req =
  check (field lab string) (fn s => s = req) (lab ^ " not " ^ req)

fun check_ast_type req = check_field "ast_type" req

fun achoose err ls = orElse(choose ls, fail err)

(* Convert ML int to HOL num term *)
fun mk_num_from_int n = numSyntax.mk_numeral (Arbnum.fromInt n)

val numtm : term decoder =
  JSONDecode.map (numSyntax.mk_numeral o Arbnum.fromLargeInt o IntInf.toLarge) intInf

(* Convert ML int to HOL int term *)
val inttm : term decoder =
  JSONDecode.map (intSyntax.term_of_int o Arbint.fromLargeInt) intInf

val stringtm : term decoder = JSONDecode.map fromMLstring string
val booltm : bool decoder = bool

(* ===== Type Decoders ===== *)

(* Decode typeclass string to constructor *)
fun typeclass_of_string s =
  if s = "integer" then TC_integer_tm
  else if s = "bytes_m" then TC_bytes_m_tm
  else if s = "static_array" orelse s = "$SArray" then TC_static_array_tm
  else if s = "dynamic_array" orelse s = "DynArray" then TC_dynamic_array_tm
  else if s = "struct" then TC_struct_tm
  else if s = "flag" then TC_flag_tm
  else if s = "tuple" then TC_tuple_tm
  else if s = "hashmap" then TC_hashmap_tm
  else if s = "interface" then TC_interface_tm
  else if s = "contract_function" then TC_contract_function_tm
  else if s = "builtin_function" then TC_builtin_function_tm
  else if s = "module" then TC_module_tm
  else mk_TC_other s

val json_typeclass : term decoder =
  JSONDecode.map typeclass_of_string (field "typeclass" string)

(* Main type decoder - handles all json_type cases *)
fun d_json_type () : term decoder = achoose "json_type" [
  (* Integer: has typeclass "integer", bits and is_signed fields *)
  check (field "typeclass" string) (fn s => s = "integer") "not integer" $
    JSONDecode.map (fn (bits, is_signed) => mk_JT_Integer(bits, is_signed)) $
    tuple2 (field "bits" numtm, field "is_signed" bool),

  (* bytes_m: has typeclass "bytes_m" and m field *)
  check (field "typeclass" string) (fn s => s = "bytes_m") "not bytes_m" $
    JSONDecode.map mk_JT_BytesM (field "m" numtm),

  (* String: name = "String" with length *)
  check (field "name" string) (fn s => s = "String") "not String" $
    JSONDecode.map mk_JT_String (field "length" numtm),

  (* Bytes: name = "Bytes" with length *)
  check (field "name" string) (fn s => s = "Bytes") "not Bytes" $
    JSONDecode.map mk_JT_Bytes (field "length" numtm),

  (* Static array: typeclass = "static_array" or "$SArray" *)
  check (field "typeclass" string) (fn s => s = "static_array" orelse s = "$SArray") "not static_array" $
    JSONDecode.map (fn (vt, len) => mk_JT_StaticArray(vt, len)) $
    tuple2 (field "value_type" (delay d_json_type), field "length" numtm),

  (* Dynamic array: typeclass = "dynamic_array" or name = "DynArray" *)
  check (field "typeclass" string) (fn s => s = "dynamic_array") "not dynamic_array" $
    JSONDecode.map (fn (vt, len) => mk_JT_DynArray(vt, len)) $
    tuple2 (field "value_type" (delay d_json_type), field "length" numtm),

  check (field "name" string) (fn s => s = "DynArray") "not DynArray" $
    JSONDecode.map (fn (vt, len) => mk_JT_DynArray(vt, len)) $
    tuple2 (field "value_type" (delay d_json_type), field "length" numtm),

  (* Struct: typeclass = "struct" *)
  check (field "typeclass" string) (fn s => s = "struct") "not struct" $
    JSONDecode.map mk_JT_Struct (field "name" string),

  (* Flag: typeclass = "flag" *)
  check (field "typeclass" string) (fn s => s = "flag") "not flag" $
    JSONDecode.map mk_JT_Flag (field "name" string),

  (* Tuple: typeclass = "tuple" *)
  check (field "typeclass" string) (fn s => s = "tuple") "not tuple" $
    JSONDecode.map mk_JT_Tuple (field "member_types" (array (delay d_json_type))),

  (* HashMap: typeclass = "hashmap" *)
  check (field "typeclass" string) (fn s => s = "hashmap") "not hashmap" $
    JSONDecode.map (fn (kt, vt) => mk_JT_HashMap(kt, vt)) $
    tuple2 (field "key_type" (delay d_json_type), field "value_type" (delay d_json_type)),

  (* Interface - treat as named type *)
  check (field "typeclass" string) (fn s => s = "interface") "not interface" $
    succeed (mk_JT_Named "address"),

  (* Named types (bool, address, decimal, etc) - just use name field *)
  JSONDecode.map mk_JT_Named (field "name" string),

  (* Null type *)
  null JT_None_tm
]

val json_type = delay d_json_type

(* Type from AST node (for subscript/name patterns) *)
fun d_ast_type () : term decoder = achoose "ast_type" [
  (* Name node - check id for primitive types *)
  check_ast_type "Name" $
  achoose "Name type" [
    (* uintN *)
    check (field "id" string) (String.isPrefix "uint") "not uint" $
      JSONDecode.map (fn s =>
        let val bits = Option.valOf (Int.fromString (String.extract(s, 4, NONE)))
        in mk_JT_Integer(mk_num_from_int bits, false) end) $
      field "id" string,
    (* intN *)
    check (field "id" string) (String.isPrefix "int") "not int" $
      JSONDecode.map (fn s =>
        let val bits = Option.valOf (Int.fromString (String.extract(s, 3, NONE)))
        in mk_JT_Integer(mk_num_from_int bits, true) end) $
      field "id" string,
    (* bytesN (fixed) *)
    check (field "id" string) (String.isPrefix "bytes") "not bytes" $
      JSONDecode.map (fn s =>
        let val m = Option.valOf (Int.fromString (String.extract(s, 5, NONE)))
        in mk_JT_BytesM(mk_num_from_int m) end) $
      field "id" string,
    (* Named types *)
    JSONDecode.map mk_JT_Named (field "id" string)
  ],

  (* Subscript node - for String[N], Bytes[N], DynArray[T, N], etc. *)
  check_ast_type "Subscript" $
  achoose "Subscript type" [
    (* String[N] *)
    check (field "value" (check_ast_type "Name" $ field "id" string))
          (fn s => s = "String") "not String" $
    JSONDecode.map mk_JT_String $
      field "slice" $ check_ast_type "Int" $ field "value" numtm,

    (* Bytes[N] *)
    check (field "value" (check_ast_type "Name" $ field "id" string))
          (fn s => s = "Bytes") "not Bytes" $
    JSONDecode.map mk_JT_Bytes $
      field "slice" $ check_ast_type "Int" $ field "value" numtm,

    (* DynArray[T, N] *)
    check (field "value" (check_ast_type "Name" $ field "id" string))
          (fn s => s = "DynArray") "not DynArray" $
    JSONDecode.map (fn (vt, len) => mk_JT_DynArray(vt, len)) $
    field "slice" $ check_ast_type "Tuple" $ field "elements" $
      tuple2 (sub 0 (delay d_ast_type),
              sub 1 $ achoose "DynArray len" [
                check_ast_type "Int" $ field "value" numtm,
                field "folded_value" $ check_ast_type "Int" $ field "value" numtm
              ]),

    (* Static array T[N] *)
    JSONDecode.map (fn (vt, len) => mk_JT_StaticArray(vt, len)) $
    tuple2 (field "value" (delay d_ast_type),
            field "slice" $ achoose "array len" [
              check_ast_type "Int" $ field "value" numtm,
              field "folded_value" $ check_ast_type "Int" $ field "value" numtm
            ])
  ],

  (* Tuple type *)
  check_ast_type "Tuple" $
    JSONDecode.map mk_JT_Tuple $
    field "elements" (array (delay d_ast_type)),

  (* indexed(...) call - unwrap the inner type *)
  check_ast_type "Call" $
    check (field "func" (tuple2 (field "ast_type" string, field "id" string)))
          (fn p => p = ("Name", "indexed")) "not indexed" $
    field "args" $ sub 0 (delay d_ast_type),

  (* null type *)
  null JT_None_tm
]

val ast_type = delay d_ast_type

(* ===== Operator Decoders ===== *)

val json_binop : term decoder = achoose "binop" [
  check_ast_type "Add" $ succeed JBop_Add_tm,
  check_ast_type "Sub" $ succeed JBop_Sub_tm,
  check_ast_type "Mult" $ succeed JBop_Mult_tm,
  check_ast_type "Div" $ succeed JBop_Div_tm,
  check_ast_type "FloorDiv" $ succeed JBop_FloorDiv_tm,
  check_ast_type "Mod" $ succeed JBop_Mod_tm,
  check_ast_type "Pow" $ succeed JBop_Pow_tm,
  check_ast_type "And" $ succeed JBop_And_tm,
  check_ast_type "Or" $ succeed JBop_Or_tm,
  check_ast_type "BitAnd" $ succeed JBop_BitAnd_tm,
  check_ast_type "BitOr" $ succeed JBop_BitOr_tm,
  check_ast_type "BitXor" $ succeed JBop_BitXor_tm,
  check_ast_type "LShift" $ succeed JBop_LShift_tm,
  check_ast_type "RShift" $ succeed JBop_RShift_tm,
  check_ast_type "Eq" $ succeed JBop_Eq_tm,
  check_ast_type "NotEq" $ succeed JBop_NotEq_tm,
  check_ast_type "Lt" $ succeed JBop_Lt_tm,
  check_ast_type "LtE" $ succeed JBop_LtE_tm,
  check_ast_type "Gt" $ succeed JBop_Gt_tm,
  check_ast_type "GtE" $ succeed JBop_GtE_tm,
  check_ast_type "In" $ succeed JBop_In_tm,
  check_ast_type "NotIn" $ succeed JBop_NotIn_tm
]

val json_unaryop : term decoder = achoose "unaryop" [
  check_ast_type "USub" $ succeed JUop_USub_tm,
  check_ast_type "Not" $ succeed JUop_Not_tm,
  check_ast_type "Invert" $ succeed JUop_Invert_tm
]

val json_boolop : term decoder = achoose "boolop" [
  check_ast_type "And" $ succeed JBoolop_And_tm,
  check_ast_type "Or" $ succeed JBoolop_Or_tm
]

(* ===== Expression Decoder ===== *)

fun d_json_expr () : term decoder = achoose "expr" [
  (* Int literal - type may be absent for array indices/sizes *)
  check_ast_type "Int" $
    JSONDecode.map (fn (v, ty) => mk_JE_Int(v, ty)) $
    tuple2 (field "value" inttm,
            orElse(field "type" json_type, succeed JT_None_tm)),

  (* Decimal literal *)
  check_ast_type "Decimal" $
    JSONDecode.map mk_JE_Decimal (field "value" string),

  (* String literal *)
  check_ast_type "Str" $
    JSONDecode.map (fn (len, v) => mk_JE_Str(len, v)) $
    tuple2 (field "type" (field "length" numtm), field "value" string),

  (* Bytes/HexBytes literal *)
  check (field "ast_type" string)
        (fn s => s = "Bytes" orelse s = "HexBytes") "not bytes" $
    JSONDecode.map (fn (len, v) => mk_JE_Bytes(len, v)) $
    tuple2 (field "type" (check (field "name" string) (fn s => s = "Bytes") "not Bytes type" $
                          field "length" numtm),
            field "value" string),

  (* Hex literal (fixed bytes) *)
  check_ast_type "Hex" $
    JSONDecode.map mk_JE_Hex (field "value" string),

  (* Bool literal (NameConstant) *)
  check_ast_type "NameConstant" $
    JSONDecode.map mk_JE_Bool (field "value" bool),

  (* Name with folded_value (constant) *)
  check_ast_type "Name" $
    JSONDecode.map (fn (v, ty) => mk_JE_Int(v, ty)) $
    tuple2 (field "folded_value" $
              check_ast_type "Int" $ field "value" inttm,
            orElse(field "type" json_type, succeed JT_None_tm)),

  (* Name - extract typeclass and source_id for module references *)
  (* source_id < 0 means main module (NONE), >= 0 means imported module *)
  check_ast_type "Name" $
    JSONDecode.map (fn (id, (tc, src_id_opt)) => mk_JE_Name(id, tc, src_id_opt)) $
    tuple2 (field "id" string,
            tuple2 (try (field "type" $ field "typeclass" string),
                    orElse (JSONDecode.map (fn n =>
                              if n < 0 then optionSyntax.mk_none numSyntax.num
                              else optionSyntax.mk_some (numSyntax.mk_numeral (Arbnum.fromLargeInt (IntInf.toLarge n))))
                              (field "type" $ field "type_decl_node" $ field "source_id" intInf),
                            succeed (optionSyntax.mk_none numSyntax.num)))),

  (* Attribute *)
  check_ast_type "Attribute" $
    JSONDecode.map (fn (e, attr) => mk_JE_Attribute(e, attr)) $
    tuple2 (field "value" (delay d_json_expr), field "attr" string),

  (* Subscript *)
  check_ast_type "Subscript" $
    JSONDecode.map (fn (e1, e2) => mk_JE_Subscript(e1, e2)) $
    tuple2 (field "value" (delay d_json_expr), field "slice" (delay d_json_expr)),

  (* BinOp *)
  check_ast_type "BinOp" $
    JSONDecode.map (fn (v, ty) => mk_JE_Int(v, ty)) $
    tuple2 (field "folded_value" $
              check_ast_type "Int" $ field "value" inttm,
            orElse(field "type" json_type, succeed JT_None_tm)),

  check_ast_type "BinOp" $
    JSONDecode.map (fn (l, op_tm, r) => mk_JE_BinOp(l, op_tm, r)) $
    tuple3 (field "left" (delay d_json_expr),
            field "op" json_binop,
            field "right" (delay d_json_expr)),

  (* Compare (treated like BinOp) *)
  check_ast_type "Compare" $
    JSONDecode.map (fn (v, ty) => mk_JE_Int(v, ty)) $
    tuple2 (field "folded_value" $
              check_ast_type "Int" $ field "value" inttm,
            orElse(field "type" json_type, succeed JT_None_tm)),

  check_ast_type "Compare" $
    JSONDecode.map (fn (l, op_tm, r) => mk_JE_BinOp(l, op_tm, r)) $
    tuple3 (field "left" (delay d_json_expr),
            field "op" json_binop,
            field "right" (delay d_json_expr)),

  (* BoolOp *)
  check_ast_type "BoolOp" $
    JSONDecode.map (fn (op_tm, es) => mk_JE_BoolOp(op_tm, es)) $
    tuple2 (field "op" json_boolop,
            field "values" (array (delay d_json_expr))),

  (* UnaryOp *)
  check_ast_type "UnaryOp" $
    JSONDecode.map (fn (op_tm, e) => mk_JE_UnaryOp(op_tm, e)) $
    tuple2 (field "op" json_unaryop,
            field "operand" (delay d_json_expr)),

  (* IfExp *)
  check_ast_type "IfExp" $
    JSONDecode.map (fn (test, body, els) => mk_JE_IfExp(test, body, els)) $
    tuple3 (field "test" (delay d_json_expr),
            field "body" (delay d_json_expr),
            field "orelse" (delay d_json_expr)),

  (* Tuple *)
  check_ast_type "Tuple" $
    JSONDecode.map mk_JE_Tuple (field "elements" (array (delay d_json_expr))),

  (* List *)
  check_ast_type "List" $
    JSONDecode.map (fn (es, ty) => mk_JE_List(es, ty)) $
    tuple2 (field "elements" (array (delay d_json_expr)),
            field "type" json_type),

  (* Call - also extract source_id from func.type.type_decl_node for module calls *)
  (* Vyper convention: -1 = main module, -2 = builtin, >= 0 = imported module *)
  (* We map negative source_ids to NONE (main module) *)
  check_ast_type "Call" $
    JSONDecode.map (fn ((func, args, kwargs), (ty, src_id_opt)) => mk_JE_Call(func, args, kwargs, ty, src_id_opt)) $
    tuple2 (tuple3 (field "func" (delay d_json_expr),
                    field "args" (array (delay d_json_expr)),
                    orElse(field "keywords" (array (delay d_json_keyword)), succeed [])),
            tuple2 (field "type" json_type,
                    orElse (JSONDecode.map (fn n =>
                              if n < 0 then optionSyntax.mk_none numSyntax.num
                              else optionSyntax.mk_some (numSyntax.mk_numeral (Arbnum.fromLargeInt (IntInf.toLarge n))))
                              (field "func" $ field "type" $ field "type_decl_node" $ field "source_id" intInf),
                            succeed (optionSyntax.mk_none numSyntax.num))))
]
and d_json_keyword () : term decoder =
  JSONDecode.map (fn (arg, v) => mk_JKeyword(arg, v)) $
  tuple2 (field "arg" string, field "value" (delay d_json_expr))

val json_expr = delay d_json_expr
val json_keyword = delay d_json_keyword

(* ===== Target Decoders ===== *)

fun d_json_base_target () : term decoder = achoose "base_target" [
  (* self.x -> TopLevelName (NONE, x) *)
  check_ast_type "Attribute" $
    check (field "value" (tuple2 (field "ast_type" string, field "id" string)))
          (fn p => p = ("Name", "self")) "not self" $
    JSONDecode.map (fn attr => mk_JBT_TopLevelName (mk_nsid_none attr)) (field "attr" string),

  (* Name *)
  check_ast_type "Name" $
    JSONDecode.map mk_JBT_Name (field "id" string),

  (* Attribute (non-self) *)
  check_ast_type "Attribute" $
    JSONDecode.map (fn (bt, attr) => mk_JBT_Attribute(bt, attr)) $
    tuple2 (field "value" (delay d_json_base_target), field "attr" string),

  (* Subscript *)
  check_ast_type "Subscript" $
    JSONDecode.map (fn (bt, e) => mk_JBT_Subscript(bt, e)) $
    tuple2 (field "value" (delay d_json_base_target), field "slice" json_expr)
]

val json_base_target = delay d_json_base_target

fun d_json_target () : term decoder = achoose "target" [
  (* Tuple target *)
  check_ast_type "Tuple" $
    JSONDecode.map mk_JTgt_Tuple (field "elements" (array (delay d_json_target))),

  (* Base target *)
  JSONDecode.map mk_JTgt_Base json_base_target
]

val json_target = delay d_json_target

(* ===== Iterator Decoder ===== *)

(* Internal representation for iterator parsing *)
datatype iter_parse = RangeParse of term list * term option | ArrayParse of term * term

val json_iter_internal : iter_parse decoder = achoose "iter" [
  (* range(...) call *)
  check_ast_type "Call" $
    check (field "func" (field "id" string)) (fn s => s = "range") "not range" $
    achoose "range variants" [
      (* range with explicit bound keyword *)
      check (field "keywords" $ sub 0 $ field "arg" string) (fn s => s = "bound") "not bounded" $
      JSONDecode.map (fn (args, bound) => RangeParse(args, SOME bound)) $
      tuple2 (field "args" (array json_expr),
              field "keywords" $ sub 0 $ field "value" $
                achoose "bound value" [
                  field "folded_value" $ field "value" numtm,
                  field "value" numtm
                ]),
      (* range without explicit bound *)
      JSONDecode.map (fn args => RangeParse(args, NONE)) $
      field "args" (array json_expr)
    ],

  (* Array iteration *)
  JSONDecode.map (fn (e, ty) => ArrayParse(e, ty)) $
  tuple2 (json_expr, field "type" json_type)
]

fun iter_parse_to_term (RangeParse(args, boundopt)) =
      mk_JIter_Range(mk_list(args, json_expr_ty), boundopt)
  | iter_parse_to_term (ArrayParse(e, ty)) =
      mk_JIter_Array(e, ty)

(* ===== Statement Decoder ===== *)

fun d_json_stmt () : term decoder = achoose "stmt" [
  check_ast_type "Pass" $ succeed JS_Pass_tm,
  check_ast_type "Break" $ succeed JS_Break_tm,
  check_ast_type "Continue" $ succeed JS_Continue_tm,

  (* Expr (including append which shows up as Call inside Expr) *)
  check_ast_type "Expr" $
    field "value" $
    achoose "expr stmt" [
      (* append call *)
      check_ast_type "Call" $
        check (field "func" $ field "type" $ tuple2 (field "name" string, field "typeclass" string))
              (fn p => p = ("append", "member_function")) "not append" $
        JSONDecode.map (fn (tgt, e) => mk_JS_Append(tgt, e)) $
        tuple2 (field "func" $ field "value" json_base_target,
                field "args" $ sub 0 json_expr),
      (* other expression statement *)
      JSONDecode.map mk_JS_Expr json_expr
    ],

  (* Return *)
  check_ast_type "Return" $
    JSONDecode.map mk_JS_Return (field "value" (nullable json_expr)),

  (* Raise *)
  check_ast_type "Raise" $
    JSONDecode.map mk_JS_Raise (field "exc" (nullable json_expr)),

  (* Assert *)
  check_ast_type "Assert" $
    JSONDecode.map (fn (test, msg) => mk_JS_Assert(test, msg)) $
    tuple2 (field "test" json_expr, field "msg" (nullable json_expr)),

  (* Log - extract source_id from event type for module events *)
  check_ast_type "Log" $
    field "value" $
    check_ast_type "Call" $
    JSONDecode.map (fn ((name, src_id_opt), args) => mk_JS_Log(mk_nsid(src_id_opt, name), args)) $
    tuple2 (field "func" $ check_ast_type "Name" $
              tuple2 (field "id" string,
                      orElse (JSONDecode.map (fn n =>
                                if n < 0 then optionSyntax.mk_none numSyntax.num
                                else optionSyntax.mk_some (numSyntax.mk_numeral (Arbnum.fromLargeInt (IntInf.toLarge n))))
                                (field "type" $ field "type_decl_node" $ field "source_id" intInf),
                              succeed (optionSyntax.mk_none numSyntax.num))),
            achoose "log args" [
              field "keywords" (array (field "value" json_expr)),
              field "args" (array json_expr)
            ]),

  (* If *)
  check_ast_type "If" $
    JSONDecode.map (fn (test, body, els) => mk_JS_If(test, body, els)) $
    tuple3 (field "test" json_expr,
            field "body" (array (delay d_json_stmt)),
            field "orelse" (array (delay d_json_stmt))),

  (* For *)
  check_ast_type "For" $
    JSONDecode.map (fn ((var, varty), iter_parsed, body) =>
      mk_JS_For(var, varty, iter_parse_to_term iter_parsed, body)) $
    tuple3 (field "target" $ check_ast_type "AnnAssign" $
              tuple2 (field "target" $ check_ast_type "Name" $ field "id" string,
                      field "target" $ field "type" json_type),
            field "iter" json_iter_internal,
            field "body" (array (delay d_json_stmt))),

  (* AugAssign *)
  check_ast_type "AugAssign" $
    JSONDecode.map (fn (tgt, op_tm, v) => mk_JS_AugAssign(tgt, op_tm, v)) $
    tuple3 (field "target" json_base_target,
            field "op" json_binop,
            field "value" json_expr),

  (* AnnAssign *)
  check_ast_type "AnnAssign" $
    JSONDecode.map (fn (var, ty, v) => mk_JS_AnnAssign(var, ty, v)) $
    tuple3 (field "target" $ check_ast_type "Name" $ field "id" string,
            field "target" $ field "type" json_type,
            field "value" json_expr),

  (* Assign *)
  check_ast_type "Assign" $
    JSONDecode.map (fn (tgt, v) => mk_JS_Assign(tgt, v)) $
    tuple2 (field "target" json_target, field "value" json_expr)
]

val json_stmt = delay d_json_stmt

(* ===== Value Type Decoder (for HashMaps) ===== *)

fun d_json_value_type () : term decoder = achoose "value_type" [
  (* Nested hashmap *)
  check (field "typeclass" string) (fn s => s = "hashmap") "not hashmap" $
    JSONDecode.map (fn (kt, vt) => mk_JVT_HashMap(kt, vt)) $
    tuple2 (field "key_type" json_type, field "value_type" (delay d_json_value_type)),

  (* Regular type *)
  JSONDecode.map mk_JVT_Type json_type
]

val json_value_type = delay d_json_value_type

(* ===== Top-level Decoder ===== *)

val json_arg : term decoder = achoose "json_arg" [
  (* New format: ast_type = "arg" with "arg" field for name and "annotation" for type *)
  check_ast_type "arg" $
    JSONDecode.map (fn (name, ty) => mk_JArg(name, ty)) $
    tuple2 (field "arg" string, field "annotation" ast_type),
  (* Old format: ast_type = "AnnAssign" with nested target *)
  check_ast_type "AnnAssign" $
    JSONDecode.map (fn (name, ty) => mk_JArg(name, ty)) $
    field "target" $
      tuple2 (check_ast_type "Name" $ field "id" string, field "type" json_type)
]

val json_func_type : term decoder =
  JSONDecode.map (fn (argtys, retty) => mk_JFuncType(argtys, retty)) $
  tuple2 (field "argument_types" (array json_type),
          field "return_type" json_type)

val json_toplevel : term decoder = achoose "toplevel" [
  (* FunctionDef *)
  check_ast_type "FunctionDef" $
    JSONDecode.map (fn ((n, d), (a, f), b) =>
      mk_JTL_FunctionDef(n, d, a, f, b)) $
    tuple3 (
      tuple2 (field "name" string,
              field "decorator_list" (array (field "id" string))),
      tuple2 (field "args" $ check_ast_type "arguments" $
                field "args" (array json_arg),
              field "func_type" json_func_type),
      field "body" (array json_stmt)
    ),

  (* VariableDecl for HashMaps *)
  check_ast_type "VariableDecl" $
    check (field "target" $ field "type" $ field "typeclass" string)
          (fn s => s = "hashmap") "not hashmap" $
    JSONDecode.map (fn (n, k, (v, p), t) =>
      mk_JTL_HashMapDecl(n, k, v, p, t)) $
    tuple4 (
      field "target" $ check_ast_type "Name" $ field "id" string,
      field "target" $ field "type" $ field "key_type" json_type,
      tuple2 (
        field "target" $ field "type" $ field "value_type" json_value_type,
        field "is_public" bool
      ),
      field "is_transient" bool
    ),

  (* VariableDecl (non-hashmap) *)
  check_ast_type "VariableDecl" $
    JSONDecode.map (fn ((n, t), (p, i), (tr, v)) =>
      mk_JTL_VariableDecl(n, t, p, i, tr, v)) $
    tuple3 (
      tuple2 (
        field "target" $ check_ast_type "Name" $ field "id" string,
        field "target" $ field "type" json_type
      ),
      tuple2 (field "is_public" bool, field "is_immutable" bool),
      tuple2 (
        field "is_transient" bool,
        andThen (field "is_constant" bool) (fn is_const =>
          if is_const
          then JSONDecode.map SOME (field "value" json_expr)
          else succeed NONE)
      )
    ),

  (* EventDef *)
  check_ast_type "EventDef" $
    JSONDecode.map (fn (name, args) => mk_JTL_EventDef(name, args)) $
    tuple2 (field "name" string,
            field "body" $ orElse(
              array json_arg,
              sub 0 (check_ast_type "Pass" (succeed [])))),

  (* StructDef *)
  check_ast_type "StructDef" $
    JSONDecode.map (fn (name, args) => mk_JTL_StructDef(name, args)) $
    tuple2 (field "name" string, field "body" (array json_arg)),

  (* FlagDef *)
  check_ast_type "FlagDef" $
    JSONDecode.map (fn (name, members) => mk_JTL_FlagDef(name, members)) $
    tuple2 (field "name" string,
            field "body" $ array $
              check_ast_type "Expr" $
              field "value" $
              check_ast_type "Name" $
              field "id" string),

  (* InterfaceDef - just record the name *)
  check_ast_type "InterfaceDef" $
    JSONDecode.map mk_JTL_InterfaceDef (field "name" string),

  (* Import - module import statement *)
  check_ast_type "Import" $
    JSONDecode.map mk_JTL_Import $
    field "import_infos" $ array $
      JSONDecode.map mk_JImportInfo $
      tuple3 (field "alias" string,
              field "path" string,
              field "qualified_module_name" string),

  (* ImportFrom - from X import Y statement *)
  check_ast_type "ImportFrom" $
    JSONDecode.map mk_JTL_Import $
    field "import_infos" $ array $
      JSONDecode.map mk_JImportInfo $
      tuple3 (field "alias" string,
              field "path" string,
              field "qualified_module_name" string),

  (* ExportsDecl - exports declaration *)
  check_ast_type "ExportsDecl" $
    JSONDecode.map mk_JTL_ExportsDecl $
    field "annotation" json_expr,

  (* InitializesDecl - initializes declaration *)
  check_ast_type "InitializesDecl" $
    JSONDecode.map mk_JTL_InitializesDecl $
    field "annotation" json_expr,

  (* UsesDecl - uses declaration *)
  check_ast_type "UsesDecl" $
    JSONDecode.map mk_JTL_UsesDecl $
    field "annotation" json_expr,

  (* ImplementsDecl - implements declaration *)
  check_ast_type "ImplementsDecl" $
    JSONDecode.map mk_JTL_ImplementsDecl $
    field "children" $ sub 0 json_expr
]

(* ===== Module Decoder ===== *)

val json_module : term decoder =
  JSONDecode.map mk_JModule (field "body" (array json_toplevel))

(* ===== Imported Module Decoder ===== *)
(* Decoder for imported modules from the imports array *)

val json_imported_module : term decoder =
  JSONDecode.map mk_JImportedModule $
  tuple3 (field "source_id" numtm,
          field "path" string,
          field "body" (array json_toplevel))

(* Parse complete annotated AST with imports *)
(* Returns JAnnotatedAST with main module and list of imported modules *)
val annotated_ast : term decoder =
  field "annotated_ast" $
  JSONDecode.map mk_JAnnotatedAST $
  tuple2 (field "ast" json_module,
          orElse (field "imports" (array json_imported_module), succeed []))

(* Legacy decoder - just returns the main module without imports *)
val annotated_ast_simple : term decoder =
  field "annotated_ast" $ field "ast" json_module

end
