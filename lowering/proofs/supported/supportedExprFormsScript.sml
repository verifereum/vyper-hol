(* PLAN 5.6 expression side conditions. Typing is a separate hypothesis.
   TOP-LEVEL: supported_binop, valid_conversion, supported_builtin_form,
   supported_type_builtin_form, supported_storage_scalar/array/dynamic_array,
   supported_subscript_base, supported_storage_fields/field_read,
   supported_external_return_type. No expression recursion or evaluator. *)
Theory supportedExprForms
Ancestors
  supportedTypes supportedDecls vyperAST vyperTypeSystem list integer
  compileVyper exprLowering compileEnv

Definition supported_unsigned_type_def:
  supported_unsigned_type (BaseT (UintT n)) = supported_int_width n /\
  supported_unsigned_type _ = F
End

Definition supported_signed_type_def:
  supported_signed_type (BaseT (IntT n)) = supported_int_width n /\
  supported_signed_type _ = F
End


Definition supported_numeric_type_def:
  supported_numeric_type ty <=>
    supported_integer_type ty \/ ty = BaseT DecimalT
End

Definition supported_integer_literal_def:
  supported_integer_literal (Literal _ (IntL n)) = T /\
  supported_integer_literal _ = F
End

Definition supported_nonnegative_literal_def:
  supported_nonnegative_literal (Literal _ (IntL n)) = (0 <= n) /\
  supported_nonnegative_literal _ = F
End

(* Operand type, NOT result type: comparisons have a bool result. Exposing
   the literal facts separately also gives TASK_021 the AugAssign contract. *)
Definition supported_binop_def:
  supported_binop (op : binop) (ty : type) (rhs_ty : type)
    (literal_base : bool) (nonnegative_exponent : bool) <=>
    T
End


Definition supported_literal_elements_def:
  supported_literal_elements tops ty (es : expr list) <=>
    supported_place_type tops ty /\
    case ty of
      ArrayT elem bound => T
    | TupleT tys => T
    | _ => F
End

Definition supported_struct_elements_def:
  supported_struct_elements tops ty fields <=>
    supported_place_type tops ty /\
    case ty of
      StructT id =>
        (FST id <> NONE \/
         case supported_struct_fields tops id of
           SOME declared =>
             EVERY (\(name,e). IS_SOME (ALOOKUP declared name)) fields
         | NONE => F)
    | _ => F
End

Definition supported_builtin_form_def:
  supported_builtin_form tops ty blt es <=>
    case (blt, es) of
      (Bop op, [a; b]) =>
        supported_binop op (expr_type a) (expr_type b)
          (supported_integer_literal a) (supported_nonnegative_literal b)
    | (MakeArray NONE (Fixed n), args) => supported_place_type tops ty
    | (MakeArray (SOME elem) bnd, args) =>
        ty = ArrayT elem bnd /\ supported_place_type tops ty
    | (MakeArray NONE (Dynamic n), args) => F
    | _ => builtin_args_length_ok blt (LENGTH es)
End

Definition supported_type_builtin_form_def:
  supported_type_builtin_form tops ty blt target es <=>
    case (blt, es) of
      (Empty, []) => ty = target /\ supported_value_type tops ty
    | (MaxValue, []) => ty = target /\ supported_numeric_type ty
    | (MinValue, []) => ty = target /\ supported_numeric_type ty
    | (Epsilon, []) => ty = target /\ ty = BaseT DecimalT
    | (Convert, [a]) => ty = target /\ valid_conversion (expr_type a) ty
    | (Extract32, [a; b]) => ty = target
    | (AbiEncode et mid, a::rest) => T
    | (AbiDecode u, [a]) => ty = target
    | _ => F
End

(* ===== Storage-base restrictions ===== *)

Definition supported_storage_scalar_def:
  supported_storage_scalar tops id ty <=>
    supported_storage_type tops ty /\
    (FST id <> NONE \/
     case supported_variable_decl tops id of
      SOME (vis, Storage, declared, SOME slot) => declared = ty
    | SOME (vis, Transient, declared, SOME slot) => declared = ty
    | _ => F)
End

Definition supported_storage_value_def:
  supported_storage_value tops id ty <=>
    supported_storage_type tops ty /\
    (FST id <> NONE \/
     case supported_variable_decl tops id of
      SOME (vis, Storage, declared, SOME slot) => declared = ty
    | SOME (vis, Transient, declared, SOME slot) => declared = ty
    | _ => F)
End

Definition supported_storage_array_def:
  supported_storage_array tops id <=>
    FST id <> NONE \/
    case supported_variable_decl tops id of
      SOME (vis, Storage, ArrayT elem bd, SOME slot) =>
        supported_storage_type tops (ArrayT elem bd)
    | SOME (vis, Transient, ArrayT elem bd, SOME slot) =>
        supported_storage_type tops (ArrayT elem bd)
    | _ => F
End

Definition supported_storage_dynamic_array_def:
  supported_storage_dynamic_array tops id <=>
    FST id <> NONE \/
    case supported_variable_decl tops id of
      SOME (vis, Storage, ArrayT elem (Dynamic n), SOME slot) =>
        supported_storage_type tops elem
    | SOME (vis, Transient, ArrayT elem (Dynamic n), SOME slot) =>
        supported_storage_type tops elem
    | _ => F
End

Definition supported_subscript_base_def:
  supported_subscript_base tops id <=>
    supported_storage_array tops id \/
    case supported_hashmap_decl tops id of
      SOME (vis, transient, kt, vt, SOME slot) =>
        supported_hashmap_key_type kt /\ supported_hashmap_value tops vt
    | _ => F
End

Definition supported_storage_fields_def:
  supported_storage_fields tops id =
    case supported_variable_decl tops id of
      SOME (vis, Storage, StructT sid, SOME slot) =>
        if supported_storage_type tops (StructT sid)
        then supported_struct_fields tops sid else NONE
    | SOME (vis, Transient, StructT sid, SOME slot) =>
        if supported_storage_type tops (StructT sid)
        then supported_struct_fields tops sid else NONE
    | _ => NONE
End

Definition supported_storage_field_read_def:
  supported_storage_field_read tops id field <=>
    FST id <> NONE \/
    case supported_storage_fields tops id of
      SOME fields => MEM field (MAP FST fields)
    | NONE => F
End

(* Reuse the compiler's descriptor lookup. Only its map table is consulted;
   all unrelated environment fields stay opaque. *)
Definition supported_place_info_def:
  supported_place_info tops e =
    place_type ((ARB : compile_env) with ce_hashmap_info := build_hashmap_info tops) e
End

Definition supported_place_root_def:
  supported_place_root tops id <=>
    FST id <> NONE \/
    case supported_variable_decl tops id of
      SOME (vis, Storage, ty, SOME slot) => supported_storage_type tops ty
    | SOME (vis, Transient, ty, SOME slot) => supported_storage_type tops ty
    | SOME (vis, Immutable, ty, offset) => supported_value_type tops ty
    | SOME (vis, Constant e, ty, slot) => T
    | SOME _ => F
    | NONE =>
        (case supported_hashmap_decl tops id of
           SOME (vis, transient, kt, vt, SOME slot) =>
             supported_hashmap_key_type kt /\ supported_hashmap_value tops vt
         | _ => F)
End

(* A qualified root's descriptor is resolved in the checked unit. *)
Definition qualified_place_root_def:
  qualified_place_root (TopLevelName ty id) = (FST id <> NONE) /\
  qualified_place_root (Subscript ty base key) = qualified_place_root base /\
  qualified_place_root (Attribute ty base field) = qualified_place_root base /\
  qualified_place_root _ = F
End

Definition supported_subscript_place_def:
  supported_subscript_place tops base <=>
    qualified_place_root base \/
    case supported_place_info tops base of
      MapPT kt vt => supported_hashmap_key_type kt /\ supported_hashmap_value tops vt
    | ValPT (ArrayT elem bd) => supported_place_type tops (ArrayT elem bd)
    | ValPT (TupleT tys) => supported_place_type tops (TupleT tys)
    | ValPT (StructT id) => supported_place_type tops (StructT id)
    | ValPT (BaseT _) => F
    | ValPT (FlagT _) => F
    | ValPT NoneT => F
End

Definition supported_field_place_def:
  supported_field_place tops ty field <=>
    case ty of
      StructT id =>
        (FST id <> NONE \/
         case supported_struct_fields tops id of
           SOME fields => MEM field (MAP FST fields)
         | NONE => F)
    | _ => F
End

(* The lowering allocates the result with the return type's memory size and
   decodes into it, so every admitted value type may be returned. *)
Definition supported_external_return_type_def:
  supported_external_return_type tops ty <=>
    ty = NoneT \/ supported_value_type tops ty
End

