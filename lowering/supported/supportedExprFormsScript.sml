(* PLAN 5.6 expression side conditions. Typing is a separate hypothesis.
   TOP-LEVEL: supported_binop, supported_conversion, supported_builtin_form,
   supported_type_builtin_form, supported_storage_scalar/array/dynamic_array,
   supported_subscript_base, supported_storage_fields/field_read,
   supported_external_return_type. No expression recursion or evaluator. *)
Theory supportedExprForms
Ancestors
  supportedTypes supportedDecls vyperAST list integer
  compileVyper exprLowering compileEnv

Definition supported_unsigned_type_def:
  supported_unsigned_type (BaseT (UintT n)) = supported_int_width n /\
  supported_unsigned_type _ = F
End

Definition supported_signed_type_def:
  supported_signed_type (BaseT (IntT n)) = supported_int_width n /\
  supported_signed_type _ = F
End

Definition supported_fixed_bytes_type_def:
  supported_fixed_bytes_type (BaseT (BytesT (Fixed n))) =
    (1 <= n /\ n <= 32 /\ n <> 20) /\
  supported_fixed_bytes_type _ = F
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
  supported_binop op ty rhs_ty literal_base nonnegative_exponent <=>
    case op of
      Add => supported_numeric_type ty
    | Sub => supported_numeric_type ty
    | Mul => supported_numeric_type ty
    | Div => supported_numeric_type ty
    | Mod => supported_numeric_type ty
    | Exp => supported_integer_type ty /\
        (literal_base \/ nonnegative_exponent)
    | UnsafeAdd => supported_integer_type ty
    | UnsafeSub => supported_integer_type ty
    | UnsafeMul => supported_integer_type ty
    | UnsafeDiv => supported_integer_type ty
    | And => supported_integer_type ty \/ ty = BaseT BoolT
    | Or => supported_integer_type ty \/ ty = BaseT BoolT
    | XOr => supported_integer_type ty \/ ty = BaseT BoolT
    | ShR => supported_integer_type ty /\ supported_unsigned_type rhs_ty
    | ShL => (ty = BaseT (UintT 256) \/ ty = BaseT (IntT 256)) /\
        supported_unsigned_type rhs_ty
    | Eq => supported_word_type ty
    | NotEq => supported_word_type ty
    | Lt => supported_numeric_type ty
    | LtE => supported_numeric_type ty
    | Gt => supported_numeric_type ty
    | GtE => supported_numeric_type ty
    | Min => supported_numeric_type ty
    | Max => supported_numeric_type ty
    | ExpMod => F
    | In => F
    | NotIn => F
End

Definition supported_short_bytes_type_def:
  supported_short_bytes_type (BaseT (BytesT (Dynamic n))) = (n <= 32) /\
  supported_short_bytes_type _ = F
End

(* Exact directed conversion list, not valid_conversion (which is wider).
   Widths and bytes20 exclusions are inherited from the word classes. *)
Definition supported_conversion_def:
  supported_conversion src dst <=>
    ((supported_integer_type src \/ src = BaseT BoolT) /\
      supported_integer_type dst) \/
    ((supported_integer_type src \/ supported_fixed_bytes_type src) /\
      dst = BaseT BoolT) \/
    (supported_short_bytes_type src /\
      (dst = BaseT BoolT \/ supported_unsigned_type dst)) \/
    (src = BaseT AddressT /\ supported_unsigned_type dst) \/
    (supported_integer_type src /\ dst = BaseT AddressT) \/
    (supported_fixed_bytes_type src /\ supported_unsigned_type dst) \/
    (src = BaseT (BytesT (Fixed 32)) /\ supported_signed_type dst) \/
    (supported_fixed_bytes_type src /\
      (dst = BaseT AddressT \/ dst = BaseT DecimalT \/
       supported_fixed_bytes_type dst)) \/
    (supported_integer_type src /\ dst = BaseT (BytesT (Fixed 32))) \/
    (supported_unsigned_type src /\ dst = BaseT DecimalT) \/
    (supported_signed_type src /\
      (case src of BaseT (IntT n) => n <= 134 | _ => F) /\
      dst = BaseT DecimalT) \/
    (src = BaseT DecimalT /\ supported_integer_type dst)
End

Definition supported_literal_elements_def:
  supported_literal_elements tops ty es <=>
    supported_place_type tops ty /\
    case ty of
      ArrayT elem bound => EVERY (supported_copy_types elem o expr_type) es
    | TupleT tys => supported_tuple_type ty /\
        LIST_REL supported_copy_types tys (MAP expr_type es)
    | _ => F
End

Definition supported_struct_elements_def:
  supported_struct_elements tops ty fields <=>
    supported_place_type tops ty /\
    case ty of
      StructT id =>
        (case supported_struct_fields tops id of
           SOME declared =>
             EVERY (\(name,e).
               case ALOOKUP declared name of
                 SOME dst => supported_copy_types dst (expr_type e)
               | NONE => F) fields
         | NONE => F)
    | _ => F
End

Definition supported_builtin_form_def:
  supported_builtin_form tops ty blt es <=>
    case (blt, es) of
      (Bop op, [a; b]) =>
        supported_binop op (expr_type a) (expr_type b)
          (supported_integer_literal a) (supported_nonnegative_literal b)
    | (Not, [a]) => ty = BaseT BoolT \/ ty = BaseT (UintT 256)
    | (Neg, [a]) => supported_signed_type ty \/ ty = BaseT DecimalT
    | (Abs, [a]) => ty = BaseT (IntT 256)
    | (AsWeiValue d, [a]) => supported_unsigned_type (expr_type a)
    | (AddMod, [a; b; c]) => EVERY (supported_unsigned_type o expr_type) es
    | (MulMod, [a; b; c]) => EVERY (supported_unsigned_type o expr_type) es
    | (PowMod256, [a; b]) => EVERY (supported_unsigned_type o expr_type) es
    | (Env item, []) => item <> MsgGas
    | (Acc item, [a]) => item <> Code
    | (BlockHash, [a]) => T
    | (BlobHash, [a]) => T
    | (ECRecover, [a; b; c; d]) => T
    | (ECAdd, [a; b]) => T
    | (ECMul, [a; b]) => T
    | (MakeArray NONE (Fixed n), args) => supported_literal_elements tops ty args
    | (MakeArray (SOME elem) (Fixed n), args) =>
        ty = ArrayT elem (Fixed n) /\ supported_literal_elements tops ty args
    | _ => F
End

Definition supported_type_builtin_form_def:
  supported_type_builtin_form ty blt target es <=>
    case (blt, es) of
      (Empty, []) => ty = target /\ supported_word_type ty
    | (MaxValue, []) => ty = target /\ supported_numeric_type ty
    | (MinValue, []) => ty = target /\ supported_numeric_type ty
    | (Epsilon, []) => ty = target /\ ty = BaseT DecimalT
    | (Convert, [a]) => ty = target /\ supported_conversion (expr_type a) ty
    | (AbiEncode F (SOME mid), [a]) => LENGTH mid = 4 /\
        (case target of TupleT [t] => supported_tuple_type t | _ => F)
    | (AbiDecode F, [a]) => ty = target /\ supported_tuple_type ty /\
        (case ty of TupleT ts => 2 <= LENGTH ts | _ => F)
    | _ => F
End

(* ===== Storage-base restrictions ===== *)

Definition supported_storage_scalar_def:
  supported_storage_scalar tops id ty <=>
    supported_full_word_type ty /\
    case supported_variable_decl tops id of
      SOME (Private, Storage, declared, SOME slot) => declared = ty
    | SOME (Private, Transient, declared, SOME slot) => declared = ty
    | _ => F
End

Definition supported_storage_value_def:
  supported_storage_value tops id ty <=>
    supported_storage_type tops ty /\
    case supported_variable_decl tops id of
      SOME (Private, Storage, declared, SOME slot) => declared = ty
    | SOME (Private, Transient, declared, SOME slot) => declared = ty
    | _ => F
End

Definition supported_storage_array_def:
  supported_storage_array tops id <=>
    case supported_variable_decl tops id of
      SOME (Private, Storage, ArrayT elem bd, SOME slot) =>
        supported_storage_type tops (ArrayT elem bd)
    | SOME (Private, Transient, ArrayT elem bd, SOME slot) =>
        supported_storage_type tops (ArrayT elem bd)
    | _ => F
End

Definition supported_storage_dynamic_array_def:
  supported_storage_dynamic_array tops id <=>
    case supported_variable_decl tops id of
      SOME (Private, Storage, ArrayT elem (Dynamic n), SOME slot) =>
        supported_full_word_type elem
    | SOME (Private, Transient, ArrayT elem (Dynamic n), SOME slot) =>
        supported_full_word_type elem
    | _ => F
End

Definition supported_subscript_base_def:
  supported_subscript_base tops id <=>
    supported_storage_array tops id \/
    case supported_hashmap_decl tops id of
      SOME (Private, transient, kt, vt, SOME slot) =>
        supported_hashmap_key_type kt /\ supported_hashmap_value tops vt
    | _ => F
End

Definition supported_storage_fields_def:
  supported_storage_fields tops id =
    case supported_variable_decl tops id of
      SOME (Private, Storage, StructT sid, SOME slot) =>
        if supported_storage_type tops (StructT sid)
        then supported_struct_fields tops sid else NONE
    | SOME (Private, Transient, StructT sid, SOME slot) =>
        if supported_storage_type tops (StructT sid)
        then supported_struct_fields tops sid else NONE
    | _ => NONE
End

Definition supported_storage_field_read_def:
  supported_storage_field_read tops id field <=>
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
    case supported_variable_decl tops id of
      SOME (Private, Storage, ty, SOME slot) => supported_storage_type tops ty
    | SOME (Private, Transient, ty, SOME slot) => supported_storage_type tops ty
    | SOME _ => F
    | NONE =>
        (case supported_hashmap_decl tops id of
           SOME (Private, transient, kt, vt, SOME slot) =>
             supported_hashmap_key_type kt /\ supported_hashmap_value tops vt
         | _ => F)
End

Definition supported_subscript_place_def:
  supported_subscript_place tops base <=>
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
        (case supported_struct_fields tops id of
           SOME fields => MEM field (MAP FST fields)
         | NONE => F)
    | _ => F
End

(* The lowering allocates the result with the return type's memory size and
   decodes into it, so every admitted value type may be returned. *)
Definition supported_external_return_type_def:
  supported_external_return_type tops ty <=> supported_value_type tops ty
End

Theorem supported_external_none_rejected:
  ~supported_external_return_type tops NoneT
Proof
  simp[supported_external_return_type_def, supported_value_type_def,
       supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def]
QED

Theorem supported_shift_contract:
  (supported_binop ShL ty rhs lb ne <=>
    (ty = BaseT (UintT 256) \/ ty = BaseT (IntT 256)) /\
      supported_unsigned_type rhs) /\
  (supported_binop Exp ty rhs lb ne <=>
    supported_integer_type ty /\ (lb \/ ne))
Proof
  simp[supported_binop_def]
QED
