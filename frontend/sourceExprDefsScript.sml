Theory sourceExprDefs
Ancestors
  sourceSyntax sourceResolve sourceTypeResolve sourceConstValue
  sourceConstEval sourceConstBuiltin sourceConstValueStructured
  vyperTypeSystem vyperAST alist integer finite_map

(* Opt-in expression API. Original nodes are validated BEFORE constant
   replacement. Runtime checking is additional evidence, not source acceptance.
   The declaration/constant environments must be independently constructed. *)

(* EVAL's quantifier conversion handles lambda predicates but can leave the
   eta-contracted equality predicate produced by bytes-bound and place checks.
   This closed logical identity keeps those validated checks computational. *)
Theorem source_expr_exists_equality[compute]:
  $? ($= (x:'a))
Proof
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >> simp[]
QED

(* Runtime bindings carry the actual independently resolved expression: locals,
   storage/immutable reads and environment builtins must not all become Name.
   Non-folder intrinsics and type operands are also keyed by declaration ID,
   never recognized by source spelling. SR_Function/SR_Type gate their use. *)
Datatype:
  source_expr_intrinsic = SE_AbiEncode | SE_AbiDecode | SE_RawCall | SE_RawRevert
End

Datatype:
  source_expr_binding = SE_Runtime expr | SE_Type type
                      | SE_Intrinsic source_expr_intrinsic
                      | SE_Function nsid (type list) num type
                      | SE_Interface (interface_func list)
                      | SE_InterfaceValue expr (interface_func list)
End

Definition source_expr_checked_def:
  source_expr_checked env ty e =
    if expr_type e = ty /\ well_typed_expr env e then SC_Value e
    else SC_Invalid SCErr_Type
End

Definition source_expr_reify_def:
  source_expr_reify env ty v =
    case sourceConstValueStructured$source_const_reify FEMPTY env.type_defs ty v of
      NONE => SC_Unsupported (SCS_Syntax "reification/type-fit")
    | SOME e => source_expr_checked env ty e
End

(* Failure is never converted into a runtime fallback. Only NotConstant may
   retain a validated dynamic expression. In particular source division by
   zero cannot be concealed by a dynamic sibling or Boolean short circuit. *)
Definition source_expr_finish_def:
  source_expr_finish env constants ty resolved e =
    source_const_then (source_expr_checked env ty e) (\checked.
      case source_const_eval constants resolved of
        SC_Value v => source_expr_reify env ty v
      | SC_NotConstant => SC_Value checked
      | SC_Invalid err => SC_Invalid err
      | SC_Unsupported why => SC_Unsupported why)
End

Definition source_expr_binary_def:
  source_expr_binary SCB_Add = (Add : binop) /\
  source_expr_binary SCB_Sub = Sub /\
  source_expr_binary SCB_Mul = Mul /\
  source_expr_binary SCB_Div = Div /\
  source_expr_binary SCB_FloorDiv = Div /\
  source_expr_binary SCB_Mod = Mod /\
  source_expr_binary SCB_Pow = Exp /\
  source_expr_binary SCB_LShift = ShL /\
  source_expr_binary SCB_RShift = ShR /\
  source_expr_binary SCB_BitAnd = And /\
  source_expr_binary SCB_BitOr = Or /\
  source_expr_binary SCB_BitXor = XOr
End

(* Stricter than runtime binop typing: / is decimal-only, // integer-only,
   shifts require 256 bits. Unsupported fixed-bytes operations are not guessed.
   well_typed_expr also checks the normalized power operand domain. *)
Definition source_expr_binary_domain_def:
  source_expr_binary_domain op ty =
    (well_typed_binop ty (source_expr_binary op) ty ty /\
     case op of
       SCB_Div => ty = BaseT DecimalT
     | SCB_FloorDiv => is_int_type ty
     | SCB_LShift => ty = BaseT (UintT 256) \/ ty = BaseT (IntT 256)
     | SCB_RShift => ty = BaseT (UintT 256) \/ ty = BaseT (IntT 256)
     | SCB_BitAnd => is_int_type ty
     | SCB_BitOr => is_int_type ty
     | SCB_BitXor => is_int_type ty
     | _ => T)
End

Definition source_expr_unary_def:
  source_expr_unary SCU_Neg = (Neg : builtin) /\
  source_expr_unary SCU_Not = Not /\
  source_expr_unary SCU_Invert = Not
End

Definition source_expr_unary_domain_def:
  source_expr_unary_domain SCU_Neg ty =
    (case ty of BaseT DecimalT => T | BaseT (IntT n) => T | _ => F) /\
  source_expr_unary_domain SCU_Not ty = (ty = BaseT BoolT) /\
  source_expr_unary_domain SCU_Invert ty = (ty = BaseT (UintT 256))
End

Definition source_expr_compare_def:
  source_expr_compare SCC_Eq = SOME (Eq : binop) /\
  source_expr_compare SCC_NotEq = SOME NotEq /\
  source_expr_compare SCC_Lt = SOME Lt /\
  source_expr_compare SCC_Le = SOME LtE /\
  source_expr_compare SCC_Gt = SOME Gt /\
  source_expr_compare SCC_Ge = SOME GtE /\
  source_expr_compare _ = NONE
End

(* Source literal classes must not be conflated merely because reification
   could produce a well-typed BytesL. A 20-byte hex token may denote AddressT
   only with its EIP-55 checksum; bytesM instead requires uniform letter case.
   Length, case and checksum are checked independently of runtime type fit. *)
Definition source_expr_literal_domain_def:
  source_expr_literal_domain (SCL_Int _) ty = is_int_type ty /\
  source_expr_literal_domain (SCL_Bool _) ty = (ty = BaseT BoolT) /\
  source_expr_literal_domain (SCL_Decimal _ _) ty = (ty = BaseT DecimalT) /\
  source_expr_literal_domain (SCL_String _) ty =
    (case ty of BaseT (StringT n) => T | _ => F) /\
  source_expr_literal_domain (SCL_Bytes _) ty =
    (case ty of BaseT (BytesT (Dynamic n)) => T | _ => F) /\
  source_expr_literal_domain (SCL_Hex s) ty =
    (case ty of
       BaseT AddressT => source_const_address_hex s
     | BaseT (BytesT (Fixed n)) => source_const_fixed_hex s /\ LENGTH s = 2 + 2 * n
     | _ => F)
End

(* A conservative source-derived operand type, never inferred JSON metadata.
   Contextual arithmetic still uses its requested type; this helper is used
   for comparisons, sized builtin arguments and subscript receivers. *)
Definition source_expr_value_type_def:
  source_expr_value_type (SCV_Int n) =
    SOME (BaseT (if n < 0 then IntT 256 else UintT 256)) /\
  source_expr_value_type (SCV_Bool b) = SOME (BaseT BoolT) /\
  source_expr_value_type (SCV_Decimal n) = SOME (BaseT DecimalT) /\
  source_expr_value_type (SCV_String s) = SOME (BaseT (StringT (LENGTH s))) /\
  source_expr_value_type (SCV_Bytes bs) = SOME (BaseT (BytesT (Dynamic (LENGTH bs)))) /\
  source_expr_value_type (SCV_Hex s) =
    (if source_const_address_hex s then SOME (BaseT AddressT)
     else if source_const_fixed_hex s then
       SOME (BaseT (BytesT (Fixed ((LENGTH s - 2) DIV 2))))
     else NONE) /\
  source_expr_value_type (SCV_List vs) =
    (case vs of [] => NONE | v::rest =>
      OPTION_MAP (\ty. ArrayT ty (Fixed (LENGTH vs))) (source_expr_value_type v)) /\
  source_expr_value_type (SCV_Tuple vs) =
    OPTION_MAP TupleT (OPT_MMAP source_expr_value_type vs) /\
  source_expr_value_type _ = NONE
Termination
  WF_REL_TAC `measure source_const_value_size` >> simp[] >>
  rpt strip_tac >> res_tac >> simp[]
End

Definition source_expr_path_def:
  source_expr_path (SX_Name n) = SOME [n] /\
  source_expr_path (SX_Attribute e n) =
    OPTION_MAP (\path. path ++ [n]) (source_expr_path e) /\
  source_expr_path _ = NONE
End

Definition source_expr_variable_def:
  source_expr_variable scopes table variables e =
    case source_expr_path e of NONE => NONE | SOME names =>
      case source_resolve_name scopes table names of
        SOME (path,SR_Dynamic) =>
          (case ALOOKUP variables path of SOME (SE_Runtime e) => SOME e
           | SOME (SE_InterfaceValue e fs) => SOME e | _ => NONE)
      | _ => NONE
End

(* Callable evidence is supplied by source declaration signatures, not JSON
   function metadata or the caller's expected return type. *)
Definition source_expr_callable_def:
  source_expr_callable scopes table bindings callee =
    case source_expr_path callee of NONE => NONE | SOME p =>
      case source_resolve_name scopes table p of
        SOME (key,SR_Function) => ALOOKUP bindings key
      | SOME (key,SR_Type) => ALOOKUP bindings key
      | SOME (key,SR_Module) => (case ALOOKUP bindings key of
          SOME (SE_Interface fs) => SOME (SE_Interface fs) | _ => NONE)
      | _ => NONE
End

(* Resolve the callee independently of its operands. Runtime struct fields in
   an argument do not erase the declaration identity of keccak256, for example.
   Every original operand/keyword is still checked by the builder. *)
Definition source_expr_builtin_identity_def:
  source_expr_builtin_identity scopes table callee =
    case source_expr_path callee of NONE => NONE | SOME names =>
      case source_resolve_name scopes table names of
        SOME (path,SR_Builtin b) => SOME b | _ => NONE
End

Definition source_expr_interface_def:
  source_expr_interface scopes table bindings (SX_Call iface [target] []) =
    (case source_expr_callable scopes table bindings iface of
       SOME (SE_Interface fs) => SOME (target,fs) | _ => NONE) /\
  source_expr_interface scopes table bindings receiver =
    (case source_expr_path receiver of NONE => NONE | SOME p =>
      case source_resolve_name scopes table p of SOME (key,SR_Dynamic) =>
        (case ALOOKUP bindings key of SOME (SE_InterfaceValue e fs) => SOME (receiver,fs)
         | _ => NONE)
      | _ => NONE)
End

Definition source_expr_external_signature_def:
  source_expr_external_signature scopes table bindings
      (SX_Call (SX_Attribute receiver name) args kws) =
    (case source_expr_interface scopes table bindings receiver of
      SOME (target,fs) =>
        (case FIND (\(id,params,ret,mut). id = name) fs of
          SOME (id,params,ret,mut) => SOME (name,MAP SND params,ret,mut,target,args,kws)
        | NONE => NONE)
    | _ => NONE) /\
  source_expr_external_signature scopes table bindings _ = NONE
End

Definition source_expr_intrinsic_def:
  source_expr_intrinsic scopes table bindings callee =
    case source_expr_path callee of NONE => NONE | SOME names =>
      case source_resolve_name scopes table names of
        SOME (path,SR_Function) =>
          (case ALOOKUP bindings path of SOME (SE_Intrinsic b) => SOME b | _ => NONE)
      | _ => NONE
End

(* A method on an interface-valued source variable is not a module path.
   Its descriptor licenses only this runtime form; recursive build still
   validates the original receiver, every argument and keyword. *)
(* Runtime member syntax also needs a candidate when the receiver is an
   independently resolved source variable, not a module namespace. This grants
   no field/type evidence: infer/build consult the nominal environment and
   recursively check that receiver, then source_expr_checked validates the field. *)
(* The constant resolver cannot represent runtime struct fields or pop places.
   These structural candidates carry NO type or successful value evidence.
   Build must recursively validate the original children and resolved callee;
   missing names and invalid constant operands still reject. This is not a
   retry through the erased JSON translator. *)
Definition source_expr_external_candidate_def[simp]:
  source_expr_external_candidate scopes table bindings (SX_ExtCall call) =
    (case source_expr_external_signature scopes table bindings call of
      SOME signature => SOME (SCE_Unsupported "runtime-external" []) | _ => NONE) /\
  source_expr_external_candidate scopes table bindings (SX_StaticCall call) =
    (case source_expr_external_signature scopes table bindings call of
      SOME signature => SOME (SCE_Unsupported "runtime-external" []) | _ => NONE) /\
  source_expr_external_candidate scopes table bindings (SX_Attribute receiver name) =
    (case source_expr_variable scopes table bindings receiver of
       SOME e => SOME SCE_Dynamic
     | NONE => case source_expr_callable scopes table bindings receiver of
         SOME (SE_Type (FlagT id)) => SOME SCE_Dynamic
       | _ => NONE) /\
  source_expr_external_candidate scopes table bindings (SX_List children) =
    SOME SCE_Dynamic /\
  source_expr_external_candidate scopes table bindings (SX_Binary op l r) = SOME SCE_Dynamic /\
  source_expr_external_candidate scopes table bindings (SX_Compare op l r) = SOME SCE_Dynamic /\
  source_expr_external_candidate scopes table bindings (SX_Subscript e i) = SOME SCE_Dynamic /\
  source_expr_external_candidate scopes table bindings (SX_Call callee args kws) =
    (if source_expr_intrinsic scopes table bindings callee = SOME SE_RawRevert then NONE
     else SOME SCE_Dynamic) /\
  source_expr_external_candidate scopes table bindings _ = NONE
End

Theorem source_expr_revert_candidate_preserved[simp]:
  source_expr_path callee = SOME names /\
  source_resolve_name scopes table names = SOME (path,SR_Function) /\
  ALOOKUP bindings path = SOME (SE_Intrinsic SE_RawRevert) ==>
  source_expr_external_candidate scopes table bindings (SX_Call callee args kws) = NONE
Proof
  simp[source_expr_external_candidate_def, source_expr_intrinsic_def]
QED

Theorem source_expr_runtime_candidate_not_constant[simp]:
  source_const_eval constants SCE_Dynamic = SC_NotConstant
Proof
  simp[source_const_eval_def]
QED

Definition source_expr_candidate_def[simp]:
  source_expr_candidate scopes table bindings original =
    case source_resolve_candidate scopes table original of
      SOME resolved => SOME resolved
    | NONE => source_expr_external_candidate scopes table bindings original
End

Definition source_expr_call_hint_def:
  source_expr_call_hint scopes table bindings (SX_Call callee args kws) =
    (case source_expr_callable scopes table bindings callee of
      SOME (SE_Function id params defaults ret) => SOME ret
    | SOME (SE_Interface fs) => SOME (BaseT AddressT)
    | _ => NONE) /\
  source_expr_call_hint scopes table bindings (SX_ExtCall call) =
    OPTION_MAP (\(name,params,ret,mut,target,args,kws). ret)
      (source_expr_external_signature scopes table bindings call) /\
  source_expr_call_hint scopes table bindings (SX_StaticCall call) =
    OPTION_MAP (\(name,params,ret,mut,target,args,kws). ret)
      (source_expr_external_signature scopes table bindings call) /\
  source_expr_call_hint scopes table bindings _ = NONE
End

Definition source_expr_hint_def:
  source_expr_hint scopes table constants variables e =
    case source_expr_variable scopes table variables e of
      SOME e => SOME (expr_type e)
    | NONE => case source_expr_call_hint scopes table variables e of
        SOME ty => SOME ty
      | NONE => case source_resolve_candidate scopes table e of
          NONE => NONE
        | SOME resolved => case source_const_eval constants resolved of
            SC_Value v => source_expr_value_type v
          | _ => NONE
End

Definition source_expr_builtin_def:
  source_expr_builtin SCB_Len = SOME Len /\
  source_expr_builtin SCB_Keccak256 = SOME Keccak256 /\
  source_expr_builtin SCB_Abs = SOME Abs /\
  source_expr_builtin SCB_Min = SOME (Bop Min) /\
  source_expr_builtin SCB_Max = SOME (Bop Max) /\
  source_expr_builtin SCB_PowMod256 = SOME PowMod256 /\
  source_expr_builtin SCB_Uint256AddMod = SOME AddMod /\
  source_expr_builtin SCB_Uint256MulMod = SOME MulMod /\
  source_expr_builtin _ = NONE
End

Definition source_expr_argument_type_def:
  source_expr_argument_type scopes table constants variables ty b arg =
    if b = SCB_Len \/ b = SCB_Keccak256 \/ b = SCB_MethodId then
      source_expr_hint scopes table constants variables arg
    else if b = SCB_Abs then SOME (BaseT (IntT 256))
    else if b = SCB_PowMod256 \/ b = SCB_Uint256AddMod \/ b = SCB_Uint256MulMod
      then SOME (BaseT (UintT 256))
    else SOME ty
End

Definition source_expr_method_type_def:
  source_expr_method_type ty v =
    case (ty,v) of
      (BaseT (BytesT (Fixed 4)),SCV_Hex _) => T
    | (BaseT (BytesT (Dynamic n)),SCV_Bytes bs) => LENGTH bs = 4 /\ 4 <= n
    | _ => F
End

(* Source type/range validation is independent of reification. Mathematical
   annotation consumers may use bounded=F for intermediates. Executable trees,
   including range/index/keyword expressions, use bounded=T, as the pin does.
   No runtime AST is constructed to certify the original constant tree. *)
Definition source_expr_fits_def:
  source_expr_fits tenv ty (SCV_List vs) =
    (case ty of ArrayT et bd => compatible_bound bd (LENGTH vs) /\
       EVERY (source_expr_fits tenv et) vs | _ => F) /\
  source_expr_fits tenv ty (SCV_Tuple vs) =
    (case ty of TupleT ts => LIST_REL (source_expr_fits tenv) ts vs | _ => F) /\
  source_expr_fits tenv ty v =
    (case source_const_value_literal v of
       SOME lit => well_formed_type tenv ty /\ well_typed_literal ty lit
     | NONE => F)
Termination
  WF_REL_TAC `measure (\(tenv,ty,v). source_const_value_size v)` >>
  simp[] >> rpt strip_tac >> res_tac >> simp[]
End

Definition source_expr_const_hint_def:
  source_expr_const_hint constants e =
    case source_const_eval constants e of
      SC_Value v => source_expr_value_type v | _ => NONE
End

Definition source_expr_const_argument_type_def:
  source_expr_const_argument_type constants ty b arg =
    if b = SCB_Len \/ b = SCB_Keccak256 \/ b = SCB_MethodId then
      source_expr_const_hint constants arg
    else if b = SCB_Abs then SOME (BaseT (IntT 256))
    else if b = SCB_PowMod256 \/ b = SCB_Uint256AddMod \/ b = SCB_Uint256MulMod
      then SOME (BaseT (UintT 256))
    else SOME ty
End

Definition source_expr_original_def:
  source_expr_original 0 tenv constants bounded ty original = F /\
  source_expr_original (SUC fuel) tenv constants bounded ty original =
    (case source_const_eval constants original of
       SC_Value v => (~bounded \/ source_expr_fits tenv ty v) /\
         (case original of
          | SCE_Literal lit => source_expr_literal_domain lit ty
          | SCE_Name path => T
          | SCE_Unary op child =>
              (source_expr_unary_domain op ty \/
               (op = SCU_Neg /\ is_int_type ty /\ v = SCV_Int 0)) /\
              source_expr_original fuel tenv constants bounded ty child
          | SCE_Binary op left right => source_expr_binary_domain op ty /\
              source_expr_original fuel tenv constants bounded ty left /\
              (if op = SCB_LShift \/ op = SCB_RShift then
                 (* Counts have their own candidate type, not the LHS width or
                    signedness. Check the unsigned source domain independently
                    from bounded arithmetic before canonical-value coercion. *)
                 source_expr_original fuel tenv constants F (BaseT (UintT 256)) right /\
                 (source_expr_original fuel tenv constants bounded (BaseT (UintT 256)) right \/
                  source_expr_original fuel tenv constants bounded (BaseT (IntT 256)) right) /\
                 (case source_const_eval constants right of SC_Value cv =>
                    source_expr_fits tenv (BaseT (UintT 256)) cv | _ => F)
               else source_expr_original fuel tenv constants bounded ty right)
          | SCE_Boolean op children => ty = BaseT BoolT /\
              EVERY (source_expr_original fuel tenv constants bounded (BaseT BoolT)) children
          | SCE_Compare op left right => ty = BaseT BoolT /\
              (if op = SCC_In \/ op = SCC_NotIn then
                (case source_expr_const_hint constants right of
                   SOME (ArrayT et bd) =>
                     source_expr_original fuel tenv constants bounded et left /\
                     source_expr_original fuel tenv constants bounded (ArrayT et bd) right
                 | _ => F)
               else case source_expr_const_hint constants left of NONE => F | SOME et =>
                 source_expr_original fuel tenv constants bounded et left /\
                 source_expr_original fuel tenv constants bounded et right)
          | SCE_List children =>
              (case ty of ArrayT et bd => compatible_bound bd (LENGTH children) /\
                EVERY (source_expr_original fuel tenv constants bounded et) children
               | _ => F)
          | SCE_Tuple children =>
              (case ty of TupleT ts =>
                LIST_REL (source_expr_original fuel tenv constants bounded) ts children
               | _ => F)
          | SCE_Subscript receiver index =>
              (case source_expr_const_hint constants receiver of NONE => F | SOME et =>
                source_expr_original fuel tenv constants bounded et receiver /\
                source_expr_original fuel tenv constants bounded (BaseT (UintT 256)) index)
          | SCE_Builtin b args keywords =>
              EVERY (\arg. case source_expr_const_argument_type constants ty b arg of
                NONE => F | SOME et => source_expr_original fuel tenv constants bounded et arg) args /\
              (if b = SCB_MethodId then source_expr_method_type ty v /\
                 (case keywords of [] => T
                  | [(key,SCE_BytesType fixed bound)] => key = "output_type" /\
                      source_expr_original fuel tenv constants F (BaseT (UintT 256)) bound
                  | _ => F)
               else keywords = [] /\
                 (case source_expr_builtin b of NONE => F | SOME builtin =>
                   well_typed_builtin_app ty builtin
                     (MAP (\arg. THE (source_expr_const_argument_type constants ty b arg)) args)))
          | _ => F)
     | _ => F)
Termination
  WF_REL_TAC `measure (\(fuel,tenv,constants,bounded,ty,original). fuel)` >> simp[]
End

(* Shared executable required-constant entry. Annotation bounds instead use
   source_type_resolve and mathematical source evaluation. Missing is the caller's
   option; a present invalid/dynamic expression is NEVER a default. *)
Definition source_expr_required_def:
  source_expr_required fuel tenv scopes table constants ty original =
    case source_resolve_candidate scopes table original of
      NONE => SC_Unsupported (SCS_Syntax "required-constant-resolution")
    | SOME resolved => case source_const_eval constants resolved of
        SC_Value v =>
          if source_expr_original fuel tenv constants T ty resolved /\
             source_expr_fits tenv ty v then SC_Value v else SC_Invalid SCErr_Type
      | SC_NotConstant => SC_Invalid SCErr_Domain
      | SC_Invalid err => SC_Invalid err
      | SC_Unsupported why => SC_Unsupported why
End

(* Type operands are checked against resolved declaration identities, not the
   result type requested by the caller or the spelling of a type name. *)
Definition source_expr_type_operand_def:
  source_expr_type_operand scopes table bindings (SX_Name name) ty =
    (case source_resolve_name scopes table [name] of
       SOME (path,kind) =>
         (case kind of SR_Type => T | SR_FixedBytes n => T | _ => F) /\
         ALOOKUP bindings path = SOME (SE_Type ty)
     | _ => F) /\
  source_expr_type_operand scopes table bindings (SX_Tuple children) ty =
    (case ty of TupleT ts => children <> [] /\
      LIST_REL (source_expr_type_operand scopes table bindings) children ts | _ => F) /\
  source_expr_type_operand scopes table bindings _ ty = F
Termination
  WF_REL_TAC `measure (\(scopes,table,bindings,e,ty). source_expr_size e)` >>
  simp[] >> rpt strip_tac >> res_tac >> simp[]
End

Definition source_expr_keyword_bool_def:
  source_expr_keyword_bool fuel tenv scopes table constants keywords key default =
    case ALOOKUP keywords key of NONE => SC_Value default | SOME original =>
      source_const_then
        (source_expr_required fuel tenv scopes table constants (BaseT BoolT) original)
        (\v. case v of SCV_Bool b => SC_Value b | _ => SC_Invalid SCErr_Type)
End

Definition source_expr_selector_def:
  source_expr_selector fuel tenv scopes table constants keywords =
    case ALOOKUP keywords "method_id" of NONE => SC_Value NONE | SOME original =>
      case source_resolve_candidate scopes table original of
        NONE => SC_Unsupported (SCS_Syntax "selector-resolution")
      | SOME resolved =>
        case source_const_eval constants resolved of
          SC_NotConstant => SC_Invalid SCErr_Domain
        | result => source_const_then result (\v.
          case source_expr_value_type v of NONE => SC_Invalid SCErr_Type | SOME ty =>
            source_const_then
              (source_expr_required fuel tenv scopes table constants ty original) (\_.
                case v of
                  SCV_Bytes bs => if LENGTH bs = 4 then SC_Value (SOME (MAP (n2w : num -> word8) bs))
                                  else SC_Invalid SCErr_Type
                | SCV_Hex s =>
                    if LENGTH s = 10 then SC_Value
                      (SOME (MAP (n2w : num -> word8) (source_const_hex_decode (DROP 2 s))))
                    else SC_Invalid SCErr_Type
                | _ => SC_Invalid SCErr_Type))
End
