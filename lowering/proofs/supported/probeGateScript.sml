(* Gate-off parity probe only, never merged: the supported_program gate's
   definitions with each exclusion clause C made (C \/ probe_lift <row>),
   renamed probe_*, so the native runner can lift rows. *)
Theory probeGate
Ancestors
  supportedProgram probeLift supportedStmts supportedTargets supportedStmtTraverse
  supportedExprTraverse supportedExprs supportedExprForms supportedNames supportedDecls
  supportedTypes vyperTypeContract vyperEventArgCompat vyperExprEffects vyperTypeSystem
  exprLowering compileEnv compileVyper constSubst vyperAST list alist pair integer arithmetic

Definition probe_supported_word_type_def:
  probe_supported_word_type (BaseT (UintT n)) = supported_int_width n /\
  probe_supported_word_type (BaseT (IntT n)) = supported_int_width n /\
  probe_supported_word_type (BaseT BoolT) = T /\
  probe_supported_word_type (BaseT DecimalT) = T /\
  probe_supported_word_type (BaseT AddressT) = T /\
  probe_supported_word_type (BaseT (BytesT (Fixed n))) =
    (1 <= n /\ n <= 32 /\ (n <> 20 \/ probe_lift 38)) /\
  probe_supported_word_type _ = F
End

Definition probe_supported_scalar_type_def:
  probe_supported_scalar_type ty <=>
    probe_supported_word_type ty \/ supported_string_type ty \/
    (probe_lift 1 /\ case ty of FlagT _ => T | _ => F)
End

Definition probe_supported_event_leaf_type_def:
  probe_supported_event_leaf_type ty <=>
    probe_supported_scalar_type ty \/
    case ty of
      FlagT id => T
    | BaseT (BytesT (Fixed n)) => n <= 32
    | _ => F
End

Definition probe_supported_tuple_type_def:
  probe_supported_tuple_type (TupleT ts) =
    (~NULL ts /\ EVERY probe_supported_scalar_type ts) /\
  probe_supported_tuple_type _ = F
End

Definition probe_supported_nested_type_def:
  probe_supported_nested_type leaf (fuel : num) tops ty <=>
    leaf ty \/
    case ty of
      ArrayT elem (Fixed n) =>
        0 < n /\ probe_supported_nested_type leaf fuel tops elem
    | ArrayT elem (Dynamic n) => probe_supported_nested_type leaf fuel tops elem
    | TupleT tys => ~NULL tys /\ EVERY (probe_supported_nested_type leaf fuel tops) tys
    | StructT id =>
        (if fuel = 0 then F
        else case supported_struct_fields tops id of
           NONE => F
         | SOME fields =>
             ~NULL fields /\
             EVERY (probe_supported_nested_type leaf (fuel - 1) tops o SND) fields)
    | _ => F
Termination
  (* `fuel : num` is spelled out in both places: the definition and this
     quotation are typed independently, and an unconstrained numeric type
     here resolves to `rat`, which makes the WF obligation `WF rat$<` and
     so unprovable by WF_TAC's lemmas (they are all about `num`). *)
  WF_REL_TAC `inv_image ($< LEX $<)
    (λ(leaf,fuel,tops,ty). ((fuel : num), type_size ty))` >> rw[] >> simp[]
End

Definition probe_supported_place_type_def:
  probe_supported_place_type tops ty <=>
    probe_supported_nested_type probe_supported_scalar_type (LENGTH tops) tops ty
End

Definition probe_supported_value_type_def:
  probe_supported_value_type tops ty <=>
    probe_supported_scalar_type ty \/
    case ty of
      TupleT ts => ~NULL ts /\ EVERY probe_supported_scalar_type ts
    | ArrayT elem (Fixed n) => probe_supported_word_type elem /\ 0 < n
    | ArrayT elem (Dynamic n) => probe_supported_word_type elem
    | StructT id =>
        (case supported_struct_fields tops id of
           SOME fields =>
             ~NULL fields /\ EVERY (probe_supported_word_type o SND) fields
         | NONE => F)
    | _ => F
End

Definition probe_supported_copy_types_def:
  probe_supported_copy_types dst src <=>
    dst = src \/
    (probe_supported_word_type dst /\ probe_supported_word_type src) \/
    (case (dst,src) of
       (BaseT (StringT _), BaseT (StringT _)) => T
     | (BaseT (BytesT (Dynamic _)), BaseT (BytesT (Dynamic _))) => T
     | _ => F)
End

Definition probe_probe_storage_leaf_def:
  probe_probe_storage_leaf ty <=>
    supported_full_word_type ty \/ (probe_lift 33 /\ probe_supported_scalar_type ty)
End

Definition probe_supported_storage_type_def:
  probe_supported_storage_type tops ty <=>
    probe_supported_nested_type probe_probe_storage_leaf (LENGTH tops) tops ty
End

Definition probe_supported_hashmap_key_type_def:
  probe_supported_hashmap_key_type ty <=>
    supported_integer_type ty \/ ty = BaseT BoolT \/ ty = BaseT AddressT \/
    ty = BaseT (BytesT (Fixed 32)) \/ supported_string_type ty \/ probe_lift 33
End

Definition probe_supported_hashmap_value_def:
  probe_supported_hashmap_value tops (Type ty) = probe_supported_storage_type tops ty /\
  probe_supported_hashmap_value tops (HashMapT kt vt) =
    (probe_supported_hashmap_key_type kt /\ probe_supported_hashmap_value tops vt)
End

Definition probe_supported_return_type_def:
  probe_supported_return_type tops ty <=> ty = NoneT \/ probe_supported_value_type tops ty
End

Definition probe_supported_function_return_def:
  probe_supported_function_return tops External ty =
    (ty = NoneT \/ probe_supported_place_type tops ty) /\
  probe_supported_function_return tops vis ty = probe_supported_return_type tops ty
End

Definition probe_supported_declaration_header_def:
  probe_supported_declaration_header tops top <=>
    case top of
      FunctionDecl vis mut nr rr name args defaults ret fbody =>
        ((vis <> Internal ==> NULL defaults) \/ probe_lift 31) /\
        (* Internal argument copies keep their layout restriction.  External
           arguments are what the checker's assignable_type admits
           (entry_abi_support); probe_supported_program_deploy constrains Deploy's. *)
        ((vis = Internal ==> EVERY (probe_supported_value_type tops o SND) args) \/ probe_lift 36) /\
        (probe_supported_function_return tops vis ret \/ probe_lift 36)
    | VariableDecl vis Storage name ty (SOME slot) =>
        probe_supported_storage_type tops ty \/ probe_lift 33
    | VariableDecl vis Transient name ty (SOME slot) =>
        probe_supported_storage_type tops ty \/ probe_lift 33
    | VariableDecl Private Immutable name ty NONE =>
        probe_supported_value_type tops ty \/ probe_lift 32
    | VariableDecl vis (Constant e) name ty slot => T
    | HashMapDecl vis transient name kt vt (SOME slot) =>
        (probe_supported_hashmap_key_type kt /\ probe_supported_hashmap_value tops vt) \/ probe_lift 33
    | StructDecl name fields =>
        (~NULL fields /\ EVERY (probe_supported_place_type tops o SND) fields) \/ probe_lift 13
    | EventDecl name fields =>
        (* Python rejects more than three indexed fields (EventT) *)
        (EVERY (\f. if SND f then probe_supported_event_leaf_type (SND (FST f))
                    else probe_supported_nested_type probe_supported_event_leaf_type
                           (LENGTH tops) tops (SND (FST f))) fields \/ probe_lift 35) /\
        LENGTH (FILTER I (MAP SND fields)) <= 3
    | InterfaceDecl name methods => T
    | FlagDecl name members => T
    | ErrorDecl name args => T
    | _ => probe_lift 32
End

Definition probe_supported_declaration_headers_def:
  probe_supported_declaration_headers tops <=>
    EVERY (probe_supported_declaration_header tops) tops
End

Definition probe_supported_immutable_type_def:
  probe_supported_immutable_type tops id =
    case supported_variable_decl tops id of
      SOME (Private, Immutable, ty, NONE) =>
        if probe_supported_value_type tops ty \/ probe_lift 32 then SOME ty else NONE
    | SOME (_, Immutable, ty, NONE) => if probe_lift 32 then SOME ty else NONE
    | _ => NONE
End

Definition probe_supported_declaration_names_def:
  probe_supported_declaration_names tops <=>
    (ALL_DISTINCT (supported_function_names tops) /\
    ALL_DISTINCT (supported_event_names tops) /\
    EVERY (supported_function_header_names tops) tops /\
    supported_selectors_distinct tops) \/ probe_lift 37
End

Definition probe_supported_literal_elements_def:
  probe_supported_literal_elements tops ty es <=>
    probe_supported_place_type tops ty /\
    case ty of
      ArrayT elem bound => EVERY (probe_supported_copy_types elem o expr_type) es
    | TupleT tys => probe_supported_tuple_type ty /\
        LIST_REL probe_supported_copy_types tys (MAP expr_type es)
    | _ => F
End

Definition probe_supported_struct_elements_def:
  probe_supported_struct_elements tops ty fields <=>
    probe_supported_place_type tops ty /\
    case ty of
      StructT id =>
        (case supported_struct_fields tops id of
           SOME declared =>
             EVERY (\(name,e).
               case ALOOKUP declared name of
                 SOME dst => probe_supported_copy_types dst (expr_type e)
               | NONE => F) fields
         | NONE => F)
    | _ => F
End

Definition probe_supported_builtin_form_def:
  probe_supported_builtin_form tops ty blt es <=>
    case (blt, es) of
      (Bop op, [a; b]) =>
        supported_binop op (expr_type a) (expr_type b)
          (supported_integer_literal a) (supported_nonnegative_literal b) \/ probe_lift 6
    | (Not, [a]) => ty = BaseT BoolT \/ ty = BaseT (UintT 256) \/ probe_lift 4
    | (Neg, [a]) => supported_signed_type ty \/ ty = BaseT DecimalT \/ probe_lift 4
    | (Abs, [a]) => ty = BaseT (IntT 256) \/ probe_lift 4
    | (AsWeiValue d, [a]) => supported_unsigned_type (expr_type a) \/ probe_lift 4
    | (AddMod, [a; b; c]) => EVERY (supported_unsigned_type o expr_type) es \/ probe_lift 4
    | (MulMod, [a; b; c]) => EVERY (supported_unsigned_type o expr_type) es \/ probe_lift 4
    | (PowMod256, [a; b]) => EVERY (supported_unsigned_type o expr_type) es \/ probe_lift 4
    | (Env item, []) => T
    | (Acc item, [a]) => item <> Code \/ probe_lift 3
    | (BlockHash, [a]) => T
    | (BlobHash, [a]) => T
    | (ECRecover, [a; b; c; d]) => T
    | (ECAdd, [a; b]) => T
    | (ECMul, [a; b]) => T
    | (MakeArray NONE (Fixed n), args) => probe_supported_literal_elements tops ty args \/ probe_lift 4
    | (MakeArray (SOME elem) bnd, args) =>
        (ty = ArrayT elem bnd /\ probe_supported_literal_elements tops ty args) \/ probe_lift 4
    | (Uint2Str n, [a]) => supported_unsigned_type (expr_type a) \/ probe_lift 4
    | (CalldataSlice n, [a]) => T
    | _ => probe_lift 2
End

Definition probe_supported_type_builtin_form_def:
  probe_supported_type_builtin_form tops ty blt target es <=>
    case (blt, es) of
      (Empty, []) => ty = target /\ (probe_supported_value_type tops ty \/ probe_lift 5)
    | (MaxValue, []) => ty = target /\ supported_numeric_type ty
    | (MinValue, []) => ty = target /\ supported_numeric_type ty
    | (Epsilon, []) => ty = target /\ ty = BaseT DecimalT
    | (Convert, [a]) => ty = target /\ valid_conversion (expr_type a) ty
    | (AbiEncode F (SOME mid), [a]) => (LENGTH mid = 4 /\
        (case target of TupleT [t] => probe_supported_tuple_type t | _ => F)) \/ probe_lift 5
    | (AbiDecode F, [a]) => ty = target /\ ((probe_supported_tuple_type ty /\
        (case ty of TupleT ts => 2 <= LENGTH ts | _ => F)) \/ probe_lift 5)
    | _ => probe_lift 5
End

Definition probe_supported_storage_scalar_def:
  probe_supported_storage_scalar tops id ty <=>
    supported_full_word_type ty /\
    case supported_variable_decl tops id of
      SOME (Private, Storage, declared, SOME slot) => declared = ty
    | SOME (Private, Transient, declared, SOME slot) => declared = ty
    | _ => F
End

Definition probe_supported_storage_value_def:
  probe_supported_storage_value tops id ty <=>
    probe_supported_storage_type tops ty /\
    case supported_variable_decl tops id of
      SOME (vis, Storage, declared, SOME slot) => declared = ty
    | SOME (vis, Transient, declared, SOME slot) => declared = ty
    | _ => F
End

Definition probe_supported_storage_array_def:
  probe_supported_storage_array tops id <=>
    case supported_variable_decl tops id of
      SOME (vis, Storage, ArrayT elem bd, SOME slot) =>
        probe_supported_storage_type tops (ArrayT elem bd)
    | SOME (vis, Transient, ArrayT elem bd, SOME slot) =>
        probe_supported_storage_type tops (ArrayT elem bd)
    | _ => F
End

Definition probe_supported_storage_dynamic_array_def:
  probe_supported_storage_dynamic_array tops id <=>
    case supported_variable_decl tops id of
      SOME (Private, Storage, ArrayT elem (Dynamic n), SOME slot) =>
        supported_full_word_type elem
    | SOME (Private, Transient, ArrayT elem (Dynamic n), SOME slot) =>
        supported_full_word_type elem
    | _ => F
End

Definition probe_supported_subscript_base_def:
  probe_supported_subscript_base tops id <=>
    probe_supported_storage_array tops id \/
    case supported_hashmap_decl tops id of
      SOME (vis, transient, kt, vt, SOME slot) =>
        probe_supported_hashmap_key_type kt /\ probe_supported_hashmap_value tops vt
    | _ => F
End

Definition probe_supported_storage_fields_def:
  probe_supported_storage_fields tops id =
    case supported_variable_decl tops id of
      SOME (vis, Storage, StructT sid, SOME slot) =>
        if probe_supported_storage_type tops (StructT sid)
        then supported_struct_fields tops sid else NONE
    | SOME (vis, Transient, StructT sid, SOME slot) =>
        if probe_supported_storage_type tops (StructT sid)
        then supported_struct_fields tops sid else NONE
    | _ => NONE
End

Definition probe_supported_storage_field_read_def:
  probe_supported_storage_field_read tops id field <=>
    case probe_supported_storage_fields tops id of
      SOME fields => MEM field (MAP FST fields)
    | NONE => F
End

Definition probe_supported_place_root_def:
  probe_supported_place_root tops id <=>
    case supported_variable_decl tops id of
      SOME (vis, Storage, ty, SOME slot) => probe_supported_storage_type tops ty
    | SOME (vis, Transient, ty, SOME slot) => probe_supported_storage_type tops ty
    | SOME _ => F
    | NONE =>
        (case supported_hashmap_decl tops id of
           SOME (vis, transient, kt, vt, SOME slot) =>
             probe_supported_hashmap_key_type kt /\ probe_supported_hashmap_value tops vt
         | _ => F)
End

Definition probe_supported_subscript_place_def:
  probe_supported_subscript_place tops base <=>
    case supported_place_info tops base of
      MapPT kt vt => probe_supported_hashmap_key_type kt /\ probe_supported_hashmap_value tops vt
    | ValPT (ArrayT elem bd) => probe_supported_place_type tops (ArrayT elem bd)
    | ValPT (TupleT tys) => probe_supported_place_type tops (TupleT tys)
    | ValPT (StructT id) => probe_supported_place_type tops (StructT id)
    | ValPT (BaseT _) => F
    | ValPT (FlagT _) => F
    | ValPT NoneT => F
End

Definition probe_supported_field_place_def:
  probe_supported_field_place tops ty field <=>
    case ty of
      StructT id =>
        (case supported_struct_fields tops id of
           SOME fields => MEM field (MAP FST fields)
         | NONE => F)
    | _ => F
End

Definition probe_supported_external_return_type_def:
  probe_supported_external_return_type tops ty <=> probe_supported_value_type tops ty
End

Definition probe_supported_pure_expr_def:
  probe_supported_pure_expr tops (Name ty name) = T /\
  probe_supported_pure_expr tops (Literal ty lit) = T /\
  probe_supported_pure_expr tops (TopLevelName ty id) =
    (probe_supported_storage_value tops id ty \/
     probe_supported_immutable_type tops id = SOME ty \/ probe_lift 13) /\
  probe_supported_pure_expr tops (FlagMember ty id member) = probe_lift 1 /\
  (* A non-word ternary is a PHI of two memory pointers (#561: a14-01,
     a10-04).  Tuple ternaries have no parity witness. *)
  probe_supported_pure_expr tops (IfExp ty c a b) =
    (((probe_supported_value_type tops ty /\ ~probe_supported_tuple_type ty) \/ probe_lift 12) /\
     probe_supported_pure_expr tops c /\
     probe_supported_pure_expr tops a /\ probe_supported_pure_expr tops b) /\
  probe_supported_pure_expr tops (StructLit ty id fields) =
    (((supported_main_nsid id /\ probe_supported_struct_elements tops ty fields) \/ probe_lift 14) /\
     probe_supported_pure_fields tops fields) /\
  probe_supported_pure_expr tops (Subscript ty base key) =
    (((probe_supported_place_type tops ty /\ probe_supported_subscript_place tops base) \/ probe_lift 13) /\
     probe_supported_place_expr tops base /\ probe_supported_pure_expr tops key) /\
  probe_supported_pure_expr tops (Attribute ty base field) =
    (((probe_supported_place_type tops ty /\ probe_supported_field_place tops (expr_type base) field) \/ probe_lift 13) /\
     probe_supported_place_expr tops base) /\
  probe_supported_pure_expr tops (Builtin ty blt es) =
    (probe_supported_builtin_form tops ty blt es /\ probe_supported_pure_exprs tops es) /\
  probe_supported_pure_expr tops (TypeBuiltin ty blt target es) =
    (probe_supported_type_builtin_form tops ty blt target es /\ probe_supported_pure_exprs tops es) /\
  probe_supported_pure_expr tops (Pop ty target) = probe_lift 7 /\
  probe_supported_pure_expr tops (Call ty target es default) = probe_lift 7 /\
  probe_supported_pure_exprs tops [] = T /\
  probe_supported_pure_exprs tops (e::es) =
    (probe_supported_pure_expr tops e /\ probe_supported_pure_exprs tops es) /\
  probe_supported_pure_fields tops [] = T /\
  probe_supported_pure_fields tops ((name,e)::fields) =
    (probe_supported_pure_expr tops e /\ probe_supported_pure_fields tops fields) /\
  probe_supported_place_expr tops (Name ty name) = (probe_supported_place_type tops ty \/ probe_lift 13) /\
  probe_supported_place_expr tops (TopLevelName ty id) = (probe_supported_place_root tops id \/ probe_lift 13) /\
  probe_supported_place_expr tops (Subscript ty base key) =
    ((probe_supported_subscript_place tops base \/ probe_lift 13) /\ probe_supported_place_expr tops base /\
     probe_supported_pure_expr tops key) /\
  probe_supported_place_expr tops (Attribute ty base field) =
    ((probe_supported_field_place tops (expr_type base) field \/ probe_lift 13) /\ probe_supported_place_expr tops base) /\
  probe_supported_place_expr tops e = probe_supported_pure_expr tops e
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => 3 * expr_size e
    | INR (INL (_, es)) => 3 * list_size expr_size es
    | INR (INR (INL (_, fields))) =>
        3 * list_size (pair_size (list_size char_size) expr_size) fields
    | INR (INR (INR (_, e))) => 3 * expr_size e + 1)` >>
  simp[expr_size_def, listTheory.list_size_def,
       basicSizeTheory.pair_size_def]
End

Definition probe_probe_effect_row_def:
  probe_probe_effect_row (Call ty RawLog es d) = (8:num) /\
  probe_probe_effect_row (Call ty RawRevert es d) = 8 /\
  probe_probe_effect_row (Call ty (RawCallTarget f) es d) = (if f.rcf_is_delegate then 10 else 9) /\
  probe_probe_effect_row (Call ty (RawCallCalldataTarget f) es d) = 10 /\
  probe_probe_effect_row (Call ty SelfDestructTarget es d) = 10 /\
  probe_probe_effect_row (Call ty (CreateTarget k s r l) es d) = 10 /\
  probe_probe_effect_row (Call ty t es d) = 11 /\
  probe_probe_effect_row (Pop ty t) = 11 /\
  probe_probe_effect_row e = 0
End

Definition probe_supported_effect_expr_def:
  probe_supported_effect_expr tops (Call ty (IntCall id) args NONE) =
    (IS_SOME (supported_function_decl tops id Internal) /\
     (* Internal struct memory-return handling is deferred to #545. *)
     (case ty of StructT _ => probe_lift 11 | _ => T) /\
     probe_supported_pure_exprs tops args) /\
  (* Operands: target :: positional args ++ keyword operands in source
     order. Every operand is pure, so lowering default_return_value= before
     the call matches the semantics, which evaluates it there too. *)
  probe_supported_effect_expr tops
    (Call ty (ExtCall static_call skip_check (name, arg_types, ret) opts) args NONE) =
    (((EVERY probe_supported_word_type arg_types /\
     probe_supported_external_return_type tops ret /\
     (static_call ==> ~MEM EKValue opts)) \/ probe_lift 11) /\
     ALL_DISTINCT opts /\
     LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
     probe_supported_pure_exprs tops args) /\
  probe_supported_effect_expr tops (Call NoneT (Send F) [a; v] NONE) =
    (probe_supported_pure_expr tops a /\ probe_supported_pure_expr tops v) /\
  probe_supported_effect_expr tops (Call NoneT (Send T) [a; v; g] NONE) =
    (probe_supported_pure_expr tops a /\ probe_supported_pure_expr tops v /\
     probe_supported_pure_expr tops g) /\
  probe_supported_effect_expr tops (Pop ty (TopLevelNameTarget id)) =
    (probe_supported_storage_dynamic_array tops id \/ probe_lift 11) /\
  probe_supported_effect_expr tops (Subscript ty base key) =
    (((probe_supported_place_type tops ty /\ probe_supported_subscript_place tops base) \/ probe_lift 13) /\
     ((probe_supported_place_expr tops base /\ probe_supported_effect_expr tops key) \/
      (probe_supported_effect_place_expr tops base /\
       (probe_supported_pure_expr tops key \/ probe_supported_effect_expr tops key)))) /\
  probe_supported_effect_expr tops (Attribute ty base field) =
    (((probe_supported_place_type tops ty /\ probe_supported_field_place tops (expr_type base) field) \/ probe_lift 13) /\
     probe_supported_effect_place_expr tops base) /\
  probe_supported_effect_expr tops e = probe_lift (probe_probe_effect_row e) /\
  probe_supported_effect_place_expr tops (Subscript ty base key) =
    ((probe_supported_subscript_place tops base \/ probe_lift 13) /\
     ((probe_supported_place_expr tops base /\ probe_supported_effect_expr tops key) \/
      (probe_supported_effect_place_expr tops base /\
       (probe_supported_pure_expr tops key \/ probe_supported_effect_expr tops key)))) /\
  probe_supported_effect_place_expr tops (Attribute ty base field) =
    ((probe_supported_field_place tops (expr_type base) field \/ probe_lift 13) /\
     probe_supported_effect_place_expr tops base) /\
  probe_supported_effect_place_expr tops e = F
Termination
  WF_REL_TAC `measure (\x. case x of
      INL (_, e) => expr_size e
    | INR (_, e) => expr_size e)` >> simp[expr_size_def]
End

Definition probe_supported_expr_def:
  probe_supported_expr tops e <=>
    probe_supported_pure_expr tops e \/ probe_supported_effect_expr tops e
End

Definition probe_body_stmt_safe_def:
  probe_body_stmt_safe tops s <=>
    (~supported_stmt_expr_exists expr_evm_run_root s \/ probe_lift 10) /\
    (~supported_stmt_expr_exists call_operands_effect_root s \/ probe_lift 7) /\
    (EVERY (\c. FST c = NONE /\
               IS_SOME (supported_function_decl tops c Internal))
      (int_calls_stmt s) \/ probe_lift 34)
End

Definition probe_body_stmts_safe_def:
  probe_body_stmts_safe tops ss <=> EVERY (probe_body_stmt_safe tops) ss
End

Definition probe_supported_target_info_def:
  probe_supported_target_info tops bindings (NameTarget name) =
    (case ALOOKUP bindings name of
       SOME ty => if probe_supported_place_type tops ty then SOME (ValPT ty) else NONE
     | NONE => NONE) /\
  probe_supported_target_info tops bindings (TopLevelNameTarget id) =
    (if probe_supported_place_root tops id then
       case supported_hashmap_decl tops id of
         SOME (_, _, kt, vt, _) => SOME (MapPT kt vt)
       | NONE =>
           (case supported_variable_decl tops id of
              SOME (_, _, ty, _) => SOME (ValPT ty)
            | NONE => NONE)
     else NONE) /\
  probe_supported_target_info tops bindings (SubscriptTarget base key) =
    (if probe_supported_expr tops key then
       case probe_supported_target_info tops bindings base of
         SOME (MapPT kt vt) => SOME (value_type_place vt)
       | SOME (ValPT (ArrayT elem bound)) => SOME (ValPT elem)
       | _ => NONE
     else NONE) /\
  probe_supported_target_info tops bindings (AttributeTarget base field) =
    (case probe_supported_target_info tops bindings base of
       SOME (ValPT (StructT id)) =>
         (case supported_struct_fields tops id of
            SOME fields => OPTION_MAP ValPT (ALOOKUP fields field)
          | NONE => NONE)
     | _ => NONE)
End

Definition probe_supported_target_pure_def:
  probe_supported_target_pure tops (NameTarget name) = T /\
  probe_supported_target_pure tops (TopLevelNameTarget id) = T /\
  probe_supported_target_pure tops (SubscriptTarget base key) =
    (probe_supported_target_pure tops base /\ probe_supported_pure_expr tops key) /\
  probe_supported_target_pure tops (AttributeTarget base field) =
    probe_supported_target_pure tops base
End

Definition probe_supported_local_word_def:
  probe_supported_local_word bindings name <=>
    case ALOOKUP bindings name of SOME ty => probe_supported_word_type ty | NONE => F
End

Definition probe_supported_scalar_target_def:
  probe_supported_scalar_target tops id <=>
    case supported_variable_decl tops id of
      SOME (Private, Storage, ty, SOME slot) => probe_probe_storage_leaf ty
    | SOME (Private, Transient, ty, SOME slot) => probe_probe_storage_leaf ty
    | _ => F
End

Definition probe_supported_storage_field_write_def:
  probe_supported_storage_field_write tops id fname <=>
    case probe_supported_storage_fields tops id of
      SOME fields => MEM fname (MAP FST fields)
    | NONE => F
End

Definition probe_supported_target_def:
  probe_supported_target tops bindings target <=>
    case target of
      NameTarget name =>
        (case ALOOKUP bindings name of
           SOME ty => probe_supported_value_type tops ty \/ probe_lift 25
         | NONE => F)
    | TopLevelNameTarget id =>
        probe_supported_scalar_target tops id \/
        IS_SOME (probe_supported_immutable_type tops id) \/ probe_lift 25
    | SubscriptTarget (TopLevelNameTarget id) key =>
        (probe_supported_subscript_base tops id \/ probe_lift 25) /\ probe_supported_expr tops key
    | AttributeTarget (TopLevelNameTarget id) fname =>
        probe_supported_storage_field_write tops id fname \/ probe_lift 25
    | _ => probe_lift 25
End

Definition probe_supported_assignment_def:
  probe_supported_assignment tops bindings target e <=>
    probe_supported_expr tops e /\
    (probe_lift 25 \/ case target of
    | BaseTarget bt =>
        probe_supported_target tops bindings bt \/
        (case probe_supported_target_info tops bindings bt of
           SOME (ValPT ty) => probe_supported_place_type tops ty /\
             probe_supported_copy_types ty (expr_type e)
         | _ => F)
    | TupleTarget targets =>
        EVERY (\g. case g of
          BaseTarget bt => probe_supported_target tops bindings bt
        | TupleTarget _ => F) targets)
End

Definition probe_supported_aug_target_def:
  probe_supported_aug_target tops bindings target <=>
    case probe_supported_target_info tops bindings target of
      SOME (ValPT ty) => probe_supported_word_type ty
    | _ => F
End

Definition probe_supported_append_target_def:
  probe_supported_append_target tops (TopLevelNameTarget id) =
    (probe_supported_storage_dynamic_array tops id \/
     ?vis mut elem dn slot.
       supported_variable_decl tops id =
         SOME (vis, mut, ArrayT elem (Dynamic dn), SOME slot) /\
       (mut = Storage \/ mut = Transient) /\
       ~supported_full_word_type elem) /\
  probe_supported_append_target tops (NameTarget name) = T /\
  probe_supported_append_target tops (SubscriptTarget target key) =
    probe_supported_target_pure tops (SubscriptTarget target key) /\
  probe_supported_append_target tops (AttributeTarget target fname) =
    probe_supported_target_pure tops target
End

Definition probe_supported_string_reason_def:
  probe_supported_string_reason tops (Literal _ (StringL text)) = T /\
  probe_supported_string_reason tops e =
    ((probe_supported_pure_expr tops e /\
     case expr_type e of BaseT (StringT _) => T | _ => F) \/ probe_lift 26)
End

Definition probe_supported_assert_reason_def:
  probe_supported_assert_reason tops AssertBare = T /\
  probe_supported_assert_reason tops AssertUnreachable = T /\
  probe_supported_assert_reason tops (AssertReason e) = probe_supported_string_reason tops e /\
  probe_supported_assert_reason tops (AssertCustomError err) = probe_lift 21
End

Definition probe_supported_raise_reason_def:
  probe_supported_raise_reason tops RaiseBare = T /\
  probe_supported_raise_reason tops RaiseUnreachable = T /\
  probe_supported_raise_reason tops (RaiseReason e) = probe_supported_string_reason tops e /\
  probe_supported_raise_reason tops (RaiseCustomError err) = probe_lift 21
End

Definition probe_supported_log_exact_def:
  probe_supported_log_exact tops id es <=>
    probe_supported_pure_exprs tops es /\
    case supported_event_fields tops id of
      SOME fields => MAP expr_type es = MAP (SND o FST) fields
    | NONE => F
End

Definition probe_supported_log_def:
  probe_supported_log tops id es <=>
    (probe_supported_pure_exprs tops es \/ (probe_lift 26 /\ EVERY (probe_supported_expr tops) es)) /\
    (probe_lift 26 \/ case supported_event_fields tops id of
      SOME fields => LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) es fields
    | NONE => F)
End

Definition probe_supported_iterator_def:
  probe_supported_iterator tops ty (Range a b) n =
    (case (a,b) of
       (Literal _ (IntL start), Literal _ (IntL range_end)) =>
         supported_integer_type ty /\ start <= range_end /\ n = Num (range_end - start)
     | _ => probe_supported_pure_expr tops a /\ probe_supported_pure_expr tops b /\ 0 < n) /\
  probe_supported_iterator tops ty (Array e) n =
    (case e of
       Name (ArrayT elem (Fixed m)) name => elem = ty /\ n = m
     | Name (ArrayT elem (Dynamic c)) name => elem = ty /\ c <= n
     | Name _ _ => F
     | TopLevelName (ArrayT elem bd) nid =>
         elem = ty /\ bound_length bd <= n /\
         (IS_SOME (probe_supported_immutable_type tops nid) \/
          probe_supported_storage_value tops nid (ArrayT elem bd))
     | TopLevelName _ _ => F
     | _ => probe_supported_expr tops e /\
            ~supported_expr_exists (\x. ?t c l r. x = IfExp t c l r) e /\
            (!tgt nid. loop_iterator_place e = SOME tgt ==>
                       FST (place_access tgt []) <> TopLevelNameTarget nid) /\
            (!t fid args drv. e = Call t (IntCall fid) args drv ==>
               ?m nr rr ps ds b.
                 supported_function_decl tops fid Internal =
                   SOME (m,nr,rr,ps,ds,t,b)) /\
            ?bd. expr_type e = ArrayT ty bd /\ bound_length bd <= n)
End

Definition probe_supported_stmt_def:
  probe_supported_stmt tops bindings Pass = T /\
  probe_supported_stmt tops bindings Break = T /\
  probe_supported_stmt tops bindings Continue = T /\
  probe_supported_stmt tops bindings (Expr e) = probe_supported_expr tops e /\
  probe_supported_stmt tops bindings (Return NONE) = T /\
  probe_supported_stmt tops bindings (Return (SOME e)) = probe_supported_expr tops e /\
  probe_supported_stmt tops bindings (AnnAssign name ty e) =
    ((probe_supported_place_type tops ty \/ probe_lift 13) /\
     (probe_supported_copy_types ty (expr_type e) \/ arg_type_fits (expr_type e) ty \/ probe_lift 27) /\
     probe_supported_expr tops e) /\
  probe_supported_stmt tops bindings (Assign target e) =
    probe_supported_assignment tops bindings target e /\
  probe_supported_stmt tops bindings (AugAssign ty target op e) =
    ((probe_supported_target tops bindings target \/ probe_supported_aug_target tops bindings target \/ probe_lift 25) /\
     probe_supported_expr tops e /\
     (supported_binop op ty (expr_type e) F (supported_nonnegative_literal e) \/ probe_lift 6)) /\
  probe_supported_stmt tops bindings (Append target e) =
    ((probe_supported_pure_expr tops e \/ (probe_lift 26 /\ probe_supported_expr tops e)) /\
     (probe_lift 22 \/ probe_supported_append_target tops target /\
     case target of
       TopLevelNameTarget id =>
         probe_supported_storage_dynamic_array tops id \/
         (?vis mut dn slot.
           supported_variable_decl tops id =
             SOME (vis, mut, ArrayT (expr_type e) (Dynamic dn), SOME slot))
     | _ =>
         supported_full_word_type (expr_type e) /\
         ~supported_target_exists (\key. ~pure_expr key) target /\
         ?dn. probe_supported_target_info tops bindings target =
           SOME (ValPT (ArrayT (expr_type e) (Dynamic dn))))) /\
  probe_supported_stmt tops bindings (If c yes no) =
    ((probe_supported_pure_expr tops c \/ (probe_lift 26 /\ probe_supported_expr tops c)) /\ probe_supported_stmts tops bindings yes /\
     probe_supported_stmts tops bindings no) /\
  probe_supported_stmt tops bindings (Assert c reason) =
    ((probe_supported_pure_expr tops c \/ (probe_lift 26 /\ probe_supported_expr tops c)) /\ probe_supported_assert_reason tops reason) /\
  probe_supported_stmt tops bindings (Raise reason) = probe_supported_raise_reason tops reason /\
  probe_supported_stmt tops bindings (Log id es) = probe_supported_log tops id es /\
  probe_supported_stmt tops bindings (For name ty iter n loop_body) =
    ((supported_type_namespace ty \/ probe_lift 34) /\ (probe_supported_iterator tops ty iter n \/ probe_lift 23) /\
     probe_supported_stmts tops bindings loop_body /\
     (~supported_stmts_expr_exists expr_internal_call_root loop_body \/ probe_lift 24)) /\
  probe_supported_stmts tops bindings [] = T /\
  probe_supported_stmts tops bindings (s::ss) =
    (probe_supported_stmt tops bindings s /\ probe_supported_stmts tops bindings ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,_,s) => stmt_size s | INR (_,_,ss) => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
End

Definition probe_supported_return_layout_def:
  probe_supported_return_layout ret (Return (SOME e)) =
    (probe_supported_copy_types ret (expr_type e) \/ probe_lift 27) /\
  probe_supported_return_layout ret (If c yes no) =
    (probe_supported_return_layouts ret yes /\ probe_supported_return_layouts ret no) /\
  probe_supported_return_layout ret (For name ty iter n loop_body) =
    probe_supported_return_layouts ret loop_body /\
  probe_supported_return_layout ret stmt = T /\
  probe_supported_return_layouts ret [] = T /\
  probe_supported_return_layouts ret (s::ss) =
    (probe_supported_return_layout ret s /\ probe_supported_return_layouts ret ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,s) => stmt_size s | INR (_,ss) => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
End

Definition probe_supported_function_body_def:
  probe_supported_function_body tops vis args fbody <=>
    let locals = supported_stmts_bindings T fbody;
        loops = supported_stmts_bindings F fbody;
        bindings = args ++ locals ++ loops
    in ((ALL_DISTINCT (MAP FST args) /\
       EVERY (\n. ~MEM n (MAP FST args)) (MAP FST locals ++ MAP FST loops)) \/ probe_lift 37) /\
       probe_supported_stmts tops bindings fbody /\
       probe_body_stmts_safe tops fbody /\
       ((vis = Internal ==>
         ~supported_stmts_expr_exists expr_internal_call_root fbody) \/ probe_lift 24)
End

Definition probe_supported_default_expression_def:
  probe_supported_default_expression tops e <=>
    probe_supported_expr tops e /\
    ((~supported_expr_exists expr_nonmain_type_root e /\
    ~supported_expr_exists expr_msg_gas_root e) \/ probe_lift 31)
End

Definition probe_supported_declaration_body_def:
  probe_supported_declaration_body tops (FunctionDecl vis mut nr rr name args defaults ret fbody) =
    (vis <> Deploy ==>
       probe_supported_function_body tops vis args fbody /\
       (* omitted defaults are compiled into each caller's fbody *)
       EVERY (probe_supported_default_expression tops) defaults /\
       probe_supported_pure_exprs tops defaults /\
       probe_supported_return_layouts ret fbody) /\
  probe_supported_declaration_body tops (VariableDecl vis mut name ty slot) = T /\
  probe_supported_declaration_body tops (HashMapDecl vis trans name kt vt slot) = T /\
  probe_supported_declaration_body tops (StructDecl name fields) = T /\
  probe_supported_declaration_body tops (EventDecl name fields) = T /\
  probe_supported_declaration_body tops (InterfaceDecl name methods) = T /\
  probe_supported_declaration_body tops (FlagDecl name members) = T /\
  probe_supported_declaration_body tops (ErrorDecl name args) = T
End

Definition probe_supported_program_def:
  probe_supported_program tops <=>
    probe_supported_declaration_headers tops /\ probe_supported_declaration_names tops /\
    (ALL_DISTINCT (supported_internal_function_names tops) \/ probe_lift 37) /\
    EVERY (probe_supported_declaration_body tops) tops /\
    EVERY (probe_supported_pure_expr tops o SND) (module_consts_env tops [])
End

Definition probe_supported_deploy_declaration_def:
  probe_supported_deploy_declaration tops top <=>
    case top of
      FunctionDecl Deploy mut nr rr name args defaults ret stmts =>
        (EVERY (probe_supported_value_type tops o SND) args \/ probe_lift 36) /\
        probe_supported_function_body tops Deploy args stmts /\
        probe_supported_return_layouts ret stmts
    | _ => T
End

Definition probe_supported_program_deploy_def:
  probe_supported_program_deploy tops <=>
    EVERY (probe_supported_deploy_declaration tops) tops
End
