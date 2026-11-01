(* PLAN 5.6 type whitelist. TOP-LEVEL: supported_word_type,
   supported_full_word_type, supported_string_type, supported_value_type,
   supported_storage_type, supported_hashmap_key_type, supported_return_type.
   Helpers: supported_int_width, supported_integer_type, supported_scalar_type,
   supported_tuple_type, supported_struct_fields, supported_main_nsid.
   These are syntactic tests, NOT source typing or storage invariants. *)
Theory supportedTypes
Ancestors
  vyperAST list arithmetic

Definition supported_main_nsid_def:
  supported_main_nsid ((module_id, name) : nsid) <=> module_id = NONE
End

Definition supported_int_width_def:
  supported_int_width n <=> 8 <= n /\ n <= 256 /\ n MOD 8 = 0
End

Definition supported_integer_type_def:
  supported_integer_type (BaseT (UintT n)) = supported_int_width n /\
  supported_integer_type (BaseT (IntT n)) = supported_int_width n /\
  supported_integer_type _ = F
End

Definition supported_word_type_def:
  supported_word_type (BaseT (UintT n)) = supported_int_width n /\
  supported_word_type (BaseT (IntT n)) = supported_int_width n /\
  supported_word_type (BaseT BoolT) = T /\
  supported_word_type (BaseT DecimalT) = T /\
  supported_word_type (BaseT AddressT) = T /\
  supported_word_type (BaseT (BytesT (Fixed n))) =
    (1 <= n /\ n <= 32 /\ n <> 20) /\
  supported_word_type _ = F
End

Definition supported_full_word_type_def:
  supported_full_word_type ty <=>
    ty = BaseT (UintT 256) \/ ty = BaseT (IntT 256) \/
    ty = BaseT (BytesT (Fixed 32))
End

(* No extra bound restriction on strings or dynamic arrays in PLAN 5.6.
   Allocation and typing checks belong to their separate boundaries. *)
Definition supported_string_type_def:
  supported_string_type (BaseT (StringT n)) = T /\
  supported_string_type (BaseT (BytesT (Dynamic n))) = T /\
  supported_string_type _ = F
End

Definition supported_scalar_type_def:
  supported_scalar_type ty <=>
    supported_word_type ty \/ supported_string_type ty
End

(* First type declaration wins, as in type_env. An interface/flag of the
   same name blocks a later struct; an arbitrary module never resolves. *)
Definition supported_struct_fields_def:
  supported_struct_fields ([] : toplevel list) (id : nsid) = NONE /\
  supported_struct_fields (top :: rest) (module_id, name) =
    if module_id <> NONE then NONE
    else case top of
      StructDecl s fields =>
        if s = name then SOME fields
        else supported_struct_fields rest (module_id, name)
    | InterfaceDecl s methods =>
        if s = name then NONE
        else supported_struct_fields rest (module_id, name)
    | FlagDecl s members =>
        if s = name then NONE
        else supported_struct_fields rest (module_id, name)
    | _ => supported_struct_fields rest (module_id, name)
End

Definition supported_tuple_type_def:
  supported_tuple_type (TupleT ts) =
    (~NULL ts /\ EVERY supported_scalar_type ts) /\
  supported_tuple_type _ = F
End

(* Structural place types. The fuel bounds only named-struct expansion;
   well-typed acyclic declarations need at most LENGTH tops expansions. Array
   and tuple traversal is structural and consumes no declaration budget. *)
Definition supported_nested_type_def:
  supported_nested_type leaf (fuel : num) tops ty <=>
    leaf ty \/
    case ty of
      ArrayT elem (Fixed n) =>
        0 < n /\ supported_nested_type leaf fuel tops elem
    | ArrayT elem (Dynamic n) => supported_nested_type leaf fuel tops elem
    | TupleT tys => ~NULL tys /\ EVERY (supported_nested_type leaf fuel tops) tys
    | StructT id =>
        (if fuel = 0 then F
        else case supported_struct_fields tops id of
           NONE => F
         | SOME fields =>
             EVERY (supported_nested_type leaf (fuel - 1) tops o SND) fields)
    | _ => F
Termination
  (* `fuel : num` is spelled out in both places: the definition and this
     quotation are typed independently, and an unconstrained numeric type
     here resolves to `rat`, which makes the WF obligation `WF rat$<` and
     so unprovable by WF_TAC's lemmas (they are all about `num`). *)
  WF_REL_TAC `inv_image ($< LEX $<)
    (λ(leaf,fuel,tops,ty). ((fuel : num), type_size ty))` >> rw[] >> simp[]
End

Definition supported_place_type_def:
  supported_place_type tops ty <=>
    supported_nested_type supported_scalar_type (LENGTH tops) tops ty
End

Definition supported_value_type_def:
  supported_value_type tops ty <=>
    supported_scalar_type ty \/
    case ty of
      TupleT ts => ~NULL ts /\ EVERY supported_scalar_type ts
    | ArrayT elem (Fixed n) => supported_word_type elem /\ 0 < n
    | ArrayT elem (Dynamic n) => supported_word_type elem
    | StructT id =>
        (case supported_struct_fields tops id of
           SOME fields => EVERY (supported_word_type o SND) fields
         | NONE => F)
    | _ => F
End

(* Equal aggregate types have identical copy layouts. Other complex subtype
   casts remain guarded until #560. Word casts and bytelike bound changes
   use the existing scalar store paths. Source typing checks compatibility. *)
Definition supported_copy_types_def:
  supported_copy_types dst src <=>
    dst = src \/
    (supported_word_type dst /\ supported_word_type src) \/
    (case (dst,src) of
       (BaseT (StringT _), BaseT (StringT _)) => T
     | (BaseT (BytesT (Dynamic _)), BaseT (BytesT (Dynamic _))) => T
     | _ => F)
End

Definition supported_storage_type_def:
  supported_storage_type tops ty <=>
    supported_nested_type supported_full_word_type (LENGTH tops) tops ty
End

Definition supported_hashmap_key_type_def:
  supported_hashmap_key_type ty <=>
    supported_integer_type ty \/ ty = BaseT BoolT \/ ty = BaseT AddressT \/
    ty = BaseT (BytesT (Fixed 32)) \/ supported_string_type ty
End

(* Map traversal carries the value descriptor through every key. Aggregate
   leaves retain the independent storage-value restrictions. *)
Definition supported_hashmap_value_def:
  supported_hashmap_value tops (Type ty) = supported_storage_type tops ty /\
  supported_hashmap_value tops (HashMapT kt vt) =
    (supported_hashmap_key_type kt /\ supported_hashmap_value tops vt)
End

Definition supported_return_type_def:
  supported_return_type tops ty <=> ty = NoneT \/ supported_value_type tops ty
End

(* ===== Consumer contracts ===== *)

Theorem supported_word_integer_width:
  (supported_word_type (BaseT (UintT n)) <=> supported_int_width n) /\
  (supported_word_type (BaseT (IntT n)) <=> supported_int_width n)
Proof
  simp[supported_word_type_def]
QED

Theorem supported_word_bytes_bounds:
  supported_word_type (BaseT (BytesT (Fixed n))) <=>
    1 <= n /\ n <= 32 /\ n <> 20
Proof
  simp[supported_word_type_def]
QED

Theorem supported_full_word_is_word:
  supported_full_word_type ty ==> supported_word_type ty
Proof
  rw[supported_full_word_type_def] >>
  simp[supported_word_type_def, supported_int_width_def]
QED

Theorem supported_value_tuple_depth:
  supported_value_type tops (TupleT ts) <=>
    ~NULL ts /\ EVERY supported_scalar_type ts
Proof
  simp[supported_value_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def]
QED

Theorem supported_value_array_depth:
  (supported_value_type tops (ArrayT elem (Fixed n)) <=>
     supported_word_type elem /\ 0 < n) /\
  (supported_value_type tops (ArrayT elem (Dynamic n)) <=>
     supported_word_type elem)
Proof
  simp[supported_value_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def]
QED

Theorem supported_struct_fields_other_module:
  module_id <> NONE ==>
    supported_struct_fields tops (module_id, name) = NONE
Proof
  Cases_on `tops` >> simp[supported_struct_fields_def]
QED

Theorem supported_storage_array_depth:
  (supported_storage_type tops (ArrayT elem (Fixed n)) <=>
     supported_storage_type tops elem /\ 0 < n) /\
  (supported_storage_type tops (ArrayT elem (Dynamic n)) <=>
     supported_storage_type tops elem)
Proof
  conj_tac >> rewrite_tac[supported_storage_type_def] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [supported_nested_type_def])) >>
  simp[supported_full_word_type_def, CONJ_COMM]
QED
