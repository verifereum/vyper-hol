Theory sourceTypeDefs
Ancestors
  sourceConstAST sourceConstAnnotation sourceConstEval vyperTypeSystem
  vyperAST vyperValue alist integer list

(* Source name resolution supplies identities, not inferred runtime types.
   In particular the spelling "uint256" has no privileged interpretation. *)
Datatype:
  source_type_constructor = STC_String | STC_Bytes | STC_DynArray | STC_HashMap
                          | STC_Qualifier source_const_qualifier
End

Datatype:
  source_type_identity = STI_Integer bool num | STI_Bool | STI_Decimal
                       | STI_Address | STI_BytesM num
                       | STI_Struct nsid | STI_Flag nsid | STI_Interface
                       | STI_Constructor source_type_constructor
End

Datatype:
  source_type_error = STE_Unresolved (string list)
                    | STE_RequiredConstant
                    | STE_ConstantInvalid source_const_error
                    | STE_ConstantUnsupported source_const_unsupported
                    | STE_IntegerBound | STE_BoundRange | STE_Width
                    | STE_RuntimeType | STE_HashMapKey | STE_ValueType
                    | STE_EmptyTuple | STE_NestedQualifier | STE_Qualifier
                    | STE_InferredClaim | STE_Constructor
End

Datatype:
  source_type_result = ST_Ok 'a | ST_Error source_type_error
End

(* Every successful bound records the ORIGINAL expression and its exact natural
   value. No folded replacement, inferred size or runtime word enters this API. *)
Datatype:
  source_type_resolution = SourceTypeResolution value_type
                            (source_const_qualifier list)
                            ((source_const_expr # num) list)
End

Definition source_type_bind_def:
  source_type_bind (ST_Ok x) f = f x /\
  source_type_bind (ST_Error e) f = ST_Error e
End

Definition source_type_vtype_def:
  source_type_vtype (SourceTypeResolution vt qs bounds) = vt
End

Definition source_type_qualifiers_def:
  source_type_qualifiers (SourceTypeResolution vt qs bounds) = qs
End

Definition source_type_bounds_def:
  source_type_bounds (SourceTypeResolution vt qs bounds) = bounds
End

Definition source_type_bound_result_def:
  source_type_bound_result (SC_Value (SCV_Int i)) =
    (if 0 < i /\ i < &(2 ** 256) then ST_Ok (Num i)
     else ST_Error STE_BoundRange) /\
  source_type_bound_result (SC_Value _) = ST_Error STE_IntegerBound /\
  source_type_bound_result SC_NotConstant = ST_Error STE_RequiredConstant /\
  source_type_bound_result (SC_Invalid e) = ST_Error (STE_ConstantInvalid e) /\
  source_type_bound_result (SC_Unsupported u) = ST_Error (STE_ConstantUnsupported u)
End

Definition source_type_bound_def:
  source_type_bound env e = source_type_bound_result (source_const_eval env e)
End

Definition source_type_identity_def:
  source_type_identity (STI_Integer signed bits) =
    (if 8 <= bits /\ bits <= 256 /\ bits MOD 8 = 0 then
       ST_Ok (if signed then BaseT (IntT bits) else BaseT (UintT bits))
     else ST_Error STE_Width) /\
  source_type_identity STI_Bool = ST_Ok (BaseT BoolT) /\
  source_type_identity STI_Decimal = ST_Ok (BaseT DecimalT) /\
  source_type_identity STI_Address = ST_Ok (BaseT AddressT) /\
  source_type_identity (STI_BytesM n) =
    (if 0 < n /\ n <= 32 then ST_Ok (BaseT (BytesT (Fixed n)))
     else ST_Error STE_Width) /\
  source_type_identity (STI_Struct id) = ST_Ok (StructT id) /\
  source_type_identity (STI_Flag id) = ST_Ok (FlagT id) /\
  source_type_identity STI_Interface = ST_Ok (BaseT AddressT) /\
  source_type_identity (STI_Constructor _) = ST_Error STE_Constructor
End

(* The common annotation AST gives container/qualifier syntax dedicated tags.
   Those tags do NOT grant builtin identity: confirm the canonical source name
   in the resolved environment, rejecting a shadowing user declaration. *)
Definition source_type_constructor_path_def:
  source_type_constructor_path STC_String = ["String"] /\
  source_type_constructor_path STC_Bytes = ["Bytes"] /\
  source_type_constructor_path STC_DynArray = ["DynArray"] /\
  source_type_constructor_path STC_HashMap = ["HashMap"] /\
  source_type_constructor_path (STC_Qualifier SCQ_Constant) = ["constant"] /\
  source_type_constructor_path (STC_Qualifier SCQ_Immutable) = ["immutable"] /\
  source_type_constructor_path (STC_Qualifier SCQ_Public) = ["public"] /\
  source_type_constructor_path (STC_Qualifier SCQ_Transient) = ["transient"] /\
  source_type_constructor_path (STC_Qualifier SCQ_Indexed) = ["indexed"]
End

Definition source_type_require_constructor_def:
  source_type_require_constructor names ctor result =
    if ALOOKUP names (source_type_constructor_path ctor) =
         SOME (STI_Constructor ctor) then result
    else ST_Error STE_Constructor
End

Definition source_type_name_def:
  source_type_name names path =
    case ALOOKUP names path of
    | NONE => ST_Error (STE_Unresolved path)
    | SOME identity => source_type_identity identity
End

(* Inner qualifiers may not silently disappear when a type is embedded.
   HashMap is a value_type, never NoneT masquerading as an ordinary type. *)
Definition source_type_as_type_def:
  source_type_as_type (SourceTypeResolution (Type ty) [] bounds) = ST_Ok ty /\
  source_type_as_type (SourceTypeResolution (HashMapT kt vt) [] bounds) =
    ST_Error STE_ValueType /\
  source_type_as_type _ = ST_Error STE_NestedQualifier
End

Definition source_type_unqualified_def:
  source_type_unqualified (SourceTypeResolution vt qs bounds) =
    (if qs = [] then ST_Ok vt else ST_Error STE_NestedQualifier)
End

(* This is qualifier compatibility, not declaration-placement checking.
   Placement (e.g. indexed only on event fields) belongs to the caller. *)
Definition source_type_qualifier_ok_def:
  source_type_qualifier_ok q qs =
    (~MEM q qs /\
     (MEM q [SCQ_Constant; SCQ_Immutable; SCQ_Transient] ==>
      ~EXISTS (\r. MEM r [SCQ_Constant; SCQ_Immutable; SCQ_Transient]) qs))
End

Definition source_type_add_qualifier_def:
  source_type_add_qualifier q (SourceTypeResolution vt qs bounds) =
    (if source_type_qualifier_ok q qs then
       ST_Ok (SourceTypeResolution vt (q::qs) bounds)
     else ST_Error STE_Qualifier)
End

(* A checked runtime boundary also rejects size/slot overflow of composite
   types. Primitive source-width and positive source-bound checks above are
   stricter than evaluate_type (which alone admits e.g. bytes0 or uint7). *)
Definition source_type_checked_def:
  source_type_checked tenv vt qs bounds =
    if well_formed_vtype tenv vt then
      ST_Ok (SourceTypeResolution vt qs bounds)
    else ST_Error STE_RuntimeType
End
