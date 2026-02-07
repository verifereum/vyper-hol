Theory jsonAST
Ancestors
  string words
Libs
  cv_transLib

(* ===== Type Information ===== *)
(* Mirrors the "type" field in JSON *)

Datatype:
  json_typeclass
  = TC_integer
  | TC_bytes_m
  | TC_static_array
  | TC_dynamic_array
  | TC_struct
  | TC_flag
  | TC_tuple
  | TC_hashmap
  | TC_interface
  | TC_contract_function
  | TC_builtin_function
  | TC_module
  | TC_other string  (* catch-all *)
End

Datatype:
  json_type
  = JT_Named string                           (* name field only, e.g. "bool", "address" *)
  | JT_Integer num bool                       (* bits, is_signed *)
  | JT_BytesM num                             (* m for bytes1..bytes32 *)
  | JT_String num                             (* length *)
  | JT_Bytes num                              (* length *)
  | JT_StaticArray json_type num              (* value_type, length *)
  | JT_DynArray json_type num                 (* value_type, length *)
  | JT_Struct string                          (* name *)
  | JT_Flag string                            (* name *)
  | JT_Tuple (json_type list)                 (* member_types *)
  | JT_HashMap json_type json_type            (* key_type, value_type *)
  | JT_None                                   (* null type *)
End

(* ===== Binary/Unary Operators ===== *)
(* Direct mirror of ast_type for operators *)

Datatype:
  json_binop
  = JBop_Add | JBop_Sub | JBop_Mult | JBop_Div | JBop_FloorDiv
  | JBop_Mod | JBop_Pow
  | JBop_And | JBop_Or | JBop_BitAnd | JBop_BitOr | JBop_BitXor
  | JBop_LShift | JBop_RShift
  | JBop_Eq | JBop_NotEq | JBop_Lt | JBop_LtE | JBop_Gt | JBop_GtE
  | JBop_In | JBop_NotIn
End

Datatype:
  json_unaryop = JUop_USub | JUop_Not | JUop_Invert
End

Datatype:
  json_boolop = JBoolop_And | JBoolop_Or
End

(* ===== Expressions ===== *)
(* Only keep type info where needed for translation *)

Datatype:
  json_expr
  (* Literals - need type for int bounds, string/bytes length *)
  = JE_Int int json_type                               (* value, type for bounds *)
  | JE_Decimal string                                  (* value as string *)
  | JE_Str num string                                  (* length, value *)
  | JE_Bytes num string                                (* length, hex value *)
  | JE_Hex string                                      (* hex value for fixed bytes *)
  | JE_Bool bool                                       (* True/False *)

  (* Variables and access *)
  | JE_Name string (string option) (num option)        (* id, typeclass, source_id for modules *)
  | JE_Attribute json_expr string (string option) (num option)  (* value, attr, result_typeclass, source_id *)
  | JE_Subscript json_expr json_expr                   (* value, slice *)

  (* Operators *)
  | JE_BinOp json_expr json_binop json_expr            (* left, op, right *)
  | JE_BoolOp json_boolop (json_expr list)             (* op, values *)
  | JE_UnaryOp json_unaryop json_expr                  (* op, operand *)
  | JE_IfExp json_expr json_expr json_expr             (* test, body, orelse *)

  (* Compound - need type for array element type, tuple handling *)
  | JE_Tuple (json_expr list)                          (* elements *)
  | JE_List (json_expr list) json_type                 (* elements, type needed for elem type *)

  (* Calls - need type for builtins like concat/slice that embed return length *)
  (* Last field is source_id for module calls, extracted from func.type.type_decl_node *)
  | JE_Call json_expr (json_expr list) (json_keyword list) json_type (num option)

  (* External calls - func_name, arg_types, return_type, args (first is target), keywords *)
  | JE_ExtCall string (json_type list) json_type (json_expr list) (json_keyword list)
  | JE_StaticCall string (json_type list) json_type (json_expr list)
;
  json_keyword = JKeyword string json_expr             (* arg, value *)
End

(* ===== Statements ===== *)

Datatype:
  json_stmt
  = JS_Pass
  | JS_Break
  | JS_Continue
  | JS_Expr json_expr
  | JS_Return (json_expr option)
  | JS_Raise (json_expr option)
  | JS_Assert json_expr (json_expr option)             (* test, msg *)
  | JS_Log (num option # string) (json_expr list)      (* (source_id, event name), args *)
  | JS_If json_expr (json_stmt list) (json_stmt list)  (* test, body, orelse *)
  | JS_For string json_type json_iter (json_stmt list) (* var, var_type, iter, body *)
  | JS_Assign json_target json_expr                    (* target, value *)
  | JS_AnnAssign string json_type json_expr            (* var name, type, value *)
  | JS_AugAssign json_base_target json_binop json_expr (* target, op, value *)
  | JS_Append json_base_target json_expr               (* target, value *)
;
  (* Iterator - need type info for computing bounds *)
  json_iter
  = JIter_Range (json_expr list) (num option)          (* args, explicit bound if given *)
  | JIter_Array json_expr json_type                    (* array expr, array type for bound *)
;
  (* Assignment targets *)
  json_base_target
  = JBT_Name string
  | JBT_TopLevelName (num option # string)             (* (source_id, name) - for self.x and module.x *)
  | JBT_Subscript json_base_target json_expr
  | JBT_Attribute json_base_target string
;
  json_target
  = JTgt_Base json_base_target
  | JTgt_Tuple (json_target list)
End

(* ===== Top-level Declarations ===== *)

Datatype:
  json_decorator = JDec string                         (* decorator name: external, internal, view, etc *)
End

Datatype:
  json_arg = JArg string json_type                     (* arg name, type *)
End

Datatype:
  json_func_type = JFuncType (json_type list) json_type  (* argument_types, return_type *)
End

(* HashMap value types need special handling for nested hashmaps *)
Datatype:
  json_value_type
  = JVT_Type json_type
  | JVT_HashMap json_type json_value_type              (* key_type, value_type *)
End

Datatype:
  json_import_info
  = JImportInfo string num string                      (* alias, source_id, qualified_module_name *)
End

(* ===== Interface Function Signature ===== *)
(* Represents a function signature within an interface definition *)

Datatype:
  json_interface_func
  = JInterfaceFunc string (json_arg list) json_type (string list)
    (* name, args, return_type, decorators (mutability) *)
End

Datatype:
  json_toplevel
  = JTL_FunctionDef string (string list) (json_arg list) json_func_type (json_stmt list)
      (* name, decorators, args, func_type, body *)
  | JTL_VariableDecl string json_type bool bool bool (json_expr option)
      (* name, type, is_public, is_immutable, is_transient, value (for constants) *)
  | JTL_HashMapDecl string json_type json_value_type bool bool
      (* name, key_type, value_type, is_public, is_transient *)
  | JTL_EventDef string (json_arg list)
  | JTL_StructDef string (json_arg list)
  | JTL_FlagDef string (string list)                   (* name, member names *)
  | JTL_InterfaceDef string (json_interface_func list) (* name, function signatures *)
  (* Module-related declarations *)
  | JTL_Import (json_import_info list)                 (* import statement with import infos *)
  | JTL_ExportsDecl json_expr                          (* exports: annotation *)
  | JTL_InitializesDecl json_expr                      (* initializes: annotation *)
  | JTL_UsesDecl json_expr                             (* uses: annotation *)
  | JTL_ImplementsDecl json_expr                       (* implements: interface *)
End

(* ===== Module ===== *)

Datatype:
  json_module = JModule (json_toplevel list)
End

(* ===== Imported Module ===== *)
(* Represents an imported module from the imports array *)

Datatype:
  json_imported_module
  = JImportedModule num string (json_toplevel list)  (* source_id, path, body *)
End

(* ===== Annotated AST ===== *)
(* Full annotated AST with main module and imported modules *)

Datatype:
  json_annotated_ast
  = JAnnotatedAST json_module (json_imported_module list)  (* main ast, imports *)
End

(* ===== Storage Layout ===== *)
(* Maps variable names to their storage slot information *)

Datatype:
  storage_slot_info = <|
    slot : num;       (* starting slot number *)
    n_slots : num;    (* number of slots used *)
    type_str : string (* type as string, e.g. "uint256", "HashMap[int128, W]" *)
  |>
End

(* For immutables stored in code *)
Datatype:
  code_slot_info = <|
    offset : num;     (* byte offset in deployed code *)
    length : num;     (* length in bytes *)
    type_str : string (* type as string *)
  |>
End

(* Complete storage layout for a contract *)
(* Storage keys are (module_alias_opt, var_name):
   - (NONE, "counter") for main module variables
   - (SOME "lib1", "counter") for module lib1's variables *)
Datatype:
  json_storage_layout = <|
    storage : ((string option # string) # storage_slot_info) list;
    transient : ((string option # string) # storage_slot_info) list;
    code : (string # code_slot_info) list  (* immutables - no module nesting *)
  |>
End

(* Datatypes are automatically translated by cv_transLib when defined *)
