Theory sourceConstAST
Ancestors
  integer list string

(* Source-only interface. No runtime types, inferred widths, folded metadata,
   module state, or compiler-supplied replacement expressions occur here.
   Paths must be canonicalized by a later resolver; spelling is not identity. *)
Datatype:
  source_const_unary = SCU_Neg | SCU_Not | SCU_Invert
End

Datatype:
  source_const_binary = SCB_Add | SCB_Sub | SCB_Mul | SCB_Div | SCB_FloorDiv
                      | SCB_Mod | SCB_Pow | SCB_LShift | SCB_RShift
                      | SCB_BitAnd | SCB_BitOr | SCB_BitXor
End

Datatype:
  source_const_boolean = SCB_And | SCB_Or
End

Datatype:
  source_const_compare = SCC_Eq | SCC_NotEq | SCC_Lt | SCC_Le | SCC_Gt | SCC_Ge
                       | SCC_In | SCC_NotIn
End

(* These tags denote resolved builtin identities, never unchecked names.
   Unknown calls retain their callee expression instead. *)
Datatype:
  source_const_builtin = SCB_MethodId | SCB_Len | SCB_Concat | SCB_Keccak256
                       | SCB_Sha256 | SCB_Convert | SCB_Min | SCB_Max
                       | SCB_Abs | SCB_PowMod256 | SCB_Uint256AddMod | SCB_Uint256MulMod
End

(* Decimal tokens are exact coefficient * 10^(-places), not host floats or
   Decimal.to_dict source-text replacements. Hex remains distinct from Bytes.
   Hex retains source spelling: equality ignores case, membership does not.
   SCL_Hex is a token, NOT a compiler-inferred Address/bytesM tag: executable
   consumers independently check length, uniform case or EIP-55 checksum in
   the resolved type context. A decoder validates its lexical shape first. *)
Datatype:
  source_const_literal = SCL_Int int | SCL_Bool bool | SCL_Decimal int num
                       | SCL_String string | SCL_Bytes (num list)
                       | SCL_Hex string
End

(* SCE_BytesType carries a resolved type constructor and original bound:
   T = bytesM, F = Bytes[N]. It is not recognized by an unchecked name. *)
Datatype:
  source_const_expr = SCE_Literal source_const_literal
                    | SCE_Name (string list)
                    | SCE_Dynamic
                    | SCE_BytesType bool source_const_expr
                    | SCE_Unary source_const_unary source_const_expr
                    | SCE_Binary source_const_binary source_const_expr source_const_expr
                    | SCE_Boolean source_const_boolean (source_const_expr list)
                    | SCE_Compare source_const_compare source_const_expr source_const_expr
                    | SCE_List (source_const_expr list)
                    | SCE_Tuple (source_const_expr list)
                    | SCE_Subscript source_const_expr source_const_expr
                    | SCE_Builtin source_const_builtin (source_const_expr list)
                        ((string # source_const_expr) list)
                    | SCE_Call source_const_expr (source_const_expr list)
                        ((string # source_const_expr) list)
                    | SCE_Unsupported string (source_const_expr list)
End

(* Decimal values contain a coefficient scaled by exactly 10^10. All integer
   fields are mathematical integers. Octets use naturals with explicit <256
   validation, not runtime words. Aggregates keep their structural kind.
   Nominal struct identity is a resolved path; no struct folding yet. *)
(* SCV_BytesType is a keyword-only type descriptor, not runtime data. *)
Datatype:
  source_const_value = SCV_Int int | SCV_Bool bool | SCV_Decimal int
                    | SCV_String string | SCV_Bytes (num list)
                    | SCV_Hex string
                    | SCV_BytesType bool num
                    | SCV_List (source_const_value list)
                    | SCV_Tuple (source_const_value list)
                    | SCV_Struct (string list) ((string # source_const_value) list)
End

Datatype:
  source_const_error = SCErr_Domain | SCErr_ZeroDivisor | SCErr_ShiftCount
                     | SCErr_DecimalPrecision | SCErr_StringCharacter
                     | SCErr_Octet | SCErr_EmptyTuple | SCErr_BooleanArity
                     | SCErr_HexToken | SCErr_NegativePower | SCErr_PowerBound
                     | SCErr_Index | SCErr_Arity | SCErr_Keyword | SCErr_Type
                     | SCErr_Overflow
End

Datatype:
  source_const_unsupported = SCS_DecimalOperation | SCS_Power
                           | SCS_Membership | SCS_Subscript
                           | SCS_Builtin source_const_builtin | SCS_Call
                           | SCS_UnresolvedName (string list) | SCS_Syntax string
End

(* Polymorphic so child collection uses exactly the same failure algebra.
   NotConstant is reserved for a genuinely dynamic operand, not failed lookup.
   Required-constant consumers must accept only SC_Value. *)
Datatype:
  source_const_result = SC_Value 'a | SC_NotConstant
                      | SC_Invalid source_const_error
                      | SC_Unsupported source_const_unsupported
End

Datatype:
  source_const_binding = SC_Constant source_const_value | SC_DynamicBinding
End
