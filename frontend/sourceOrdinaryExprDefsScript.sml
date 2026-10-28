Theory sourceOrdinaryExprDefs
Ancestors
  sourceOrdinaryBridge sourceExprElaborate sourceExprDefs sourceResolve
  sourceSyntax sourceConstEval sourceConstBuiltin jsonToVyperExpr jsonToVyperType jsonAST
  vyperTypeSystem vyperAST ASCIInumbers words list option alist integer

(* The projection reads syntax, never compiler replacement values or types.
   Its result must equal the independently parsed original source. Fuel bounds
   both this check and normalization; exhausted fuel cannot accept a claim. *)
Definition source_ordinary_binary_def:
  source_ordinary_binary JBop_Add = SOME SCB_Add /\
  source_ordinary_binary JBop_Sub = SOME SCB_Sub /\
  source_ordinary_binary JBop_Mult = SOME SCB_Mul /\
  source_ordinary_binary JBop_Div = SOME SCB_Div /\
  source_ordinary_binary JBop_FloorDiv = SOME SCB_FloorDiv /\
  source_ordinary_binary JBop_Mod = SOME SCB_Mod /\
  source_ordinary_binary JBop_Pow = SOME SCB_Pow /\
  source_ordinary_binary JBop_LShift = SOME SCB_LShift /\
  source_ordinary_binary JBop_RShift = SOME SCB_RShift /\
  source_ordinary_binary JBop_BitAnd = SOME SCB_BitAnd /\
  source_ordinary_binary JBop_BitOr = SOME SCB_BitOr /\
  source_ordinary_binary JBop_BitXor = SOME SCB_BitXor /\
  source_ordinary_binary _ = NONE
End

Definition source_ordinary_compare_def:
  source_ordinary_compare JBop_Eq = SOME SCC_Eq /\
  source_ordinary_compare JBop_NotEq = SOME SCC_NotEq /\
  source_ordinary_compare JBop_Lt = SOME SCC_Lt /\
  source_ordinary_compare JBop_LtE = SOME SCC_Le /\
  source_ordinary_compare JBop_Gt = SOME SCC_Gt /\
  source_ordinary_compare JBop_GtE = SOME SCC_Ge /\
  source_ordinary_compare JBop_In = SOME SCC_In /\
  source_ordinary_compare JBop_NotIn = SOME SCC_NotIn /\
  source_ordinary_compare _ = NONE
End

Definition source_ordinary_unary_def:
  source_ordinary_unary JUop_USub = SCU_Neg /\
  source_ordinary_unary JUop_Not = SCU_Not /\
  source_ordinary_unary JUop_Invert = SCU_Invert
End

Definition source_ordinary_boolean_def:
  source_ordinary_boolean JBoolop_And = SCB_And /\
  source_ordinary_boolean JBoolop_Or = SCB_Or
End

(* Exact decimal token projection, not an evaluator or ten-place truncation.
   The independent source parser performs lexical validation. Equality with
   its original term prevents the permissive legacy numeric parser from
   changing the source coefficient or fractional precision. *)
Definition source_ordinary_decimal_def:
  source_ordinary_decimal token =
    let (base,exponent) = split_at_e token;
        (neg,mantissa) = strip_sign base;
        (whole,frac) = split_at_dot mantissa;
        digits = FILTER isDigit (whole ++ frac);
        places = LENGTH (FILTER isDigit frac);
        coefficient = if neg then - &(num_from_dec_string digits)
                      else &(num_from_dec_string digits);
        (eneg,edigits) = strip_sign exponent;
        power = num_from_dec_string (FILTER isDigit edigits)
    in if eneg then SCL_Decimal coefficient (places + power)
       else SCL_Decimal (coefficient * 10 ** (power - places)) (places - power)
End

Definition source_ordinary_projection_def:
  source_ordinary_projection 0 annotated = NONE /\
  source_ordinary_projection (SUC fuel) annotated =
    let project = source_ordinary_projection fuel in
    let projects = OPT_MMAP project in
    let keywords = \kws. OPT_MMAP (\kw. case kw of JKeyword k v =>
          OPTION_MAP (\e. (k,e)) (project v)) kws in
    case annotated of
      JE_Folded original replacement => project original
    | JE_Int n ty => SOME (SX_Literal (SCL_Int n))
    | JE_Bool b => SOME (SX_Literal (SCL_Bool b))
    | JE_Str n s => SOME (SX_Literal (SCL_String s))
    | JE_GenericStr s => SOME (SX_Literal (SCL_String s))
    | JE_Bytes n s => SOME (SX_Literal (SCL_Bytes
        (MAP w2n (hex_string_to_bytes (FILTER isHexDigit (strip_0x s))))))
    | JE_Hex s ty => SOME (SX_Literal (SCL_Hex s))
    | JE_Decimal s => SOME (SX_Literal (source_ordinary_decimal s))
    | JE_Ellipsis => SOME SX_Ellipsis
    | JE_Name name tc src ty => SOME (SX_Name name)
    | JE_Attribute e name tc btn btc src ty => OPTION_MAP
        (\e. SX_Attribute e name) (project e)
    | JE_Subscript e i ty => source_resolve_two SX_Subscript (project e) (project i)
    | JE_UnaryOp op e ty => OPTION_MAP (SX_Unary (source_ordinary_unary op)) (project e)
    | JE_BinOp l op r ty => (case source_ordinary_binary op of NONE => NONE
        | SOME b => source_resolve_two (SX_Binary b) (project l) (project r))
    | JE_Compare l op r => (case source_ordinary_compare op of NONE => NONE
        | SOME b => source_resolve_two (SX_Compare b) (project l) (project r))
    | JE_BoolOp op es => OPTION_MAP (SX_Boolean (source_ordinary_boolean op)) (projects es)
    | JE_List es ty => OPTION_MAP SX_List (projects es)
    | JE_Tuple es => OPTION_MAP SX_Tuple (projects es)
    | JE_IfExp c l r ty => (case (project c,project l,project r) of
        (SOME c,SOME l,SOME r) => SOME (SX_IfExp c l r) | _ => NONE)
    | JE_NamedExpr l r => source_resolve_two SX_NamedExpr (project l) (project r)
    | JE_Call callee args kws ty src =>
        (case (project callee,projects args,keywords kws) of
           (SOME f,SOME es,SOME ks) => SOME (SX_Call f es ks) | _ => NONE)
    | JE_ExtCall name src ats ty target args kws =>
        (case (project target,projects args,keywords kws) of
           (SOME t,SOME es,SOME ks) => SOME (SX_ExtCall
             (SX_Call (SX_Attribute t name) es ks)) | _ => NONE)
    | JE_StaticCall name src ats ty target args kws =>
        (case (project target,projects args,keywords kws) of
           (SOME t,SOME es,SOME ks) => SOME (SX_StaticCall
             (SX_Call (SX_Attribute t name) es ks)) | _ => NONE)
Termination
  WF_REL_TAC `measure (\(fuel,annotated). fuel)` >> simp[]
End

(* Closed inherited legacy dispatch manifest, NOT Source builtin semantics.
   These names have make_builtin_call branches but no Source prelude identity.
   All #543 builtin/intrinsic names stay on their existing verified route.
   The matched original spelling plus builtin_function claim is the explicit
   inherited identity boundary, like ctx's existing type/import claims. *)
Definition source_ordinary_residual_builtins_def:
  source_ordinary_residual_builtins =
    ["floor";"ceil";"blockhash";"blobhash";"ecrecover";"ecadd";"ecmul";
     "epsilon";"unsafe_add";"unsafe_sub";"unsafe_mul";"unsafe_div";
     "send";"raw_log";"selfdestruct";"create_minimal_proxy_to";
     "create_forwarder_to";"create_copy_of";"create_from_blueprint";
     "raw_create";"as_wei_value";"uint2str";"extract32"]
End

(* Even a dangling/shadowing lexical identity blocks inherited dispatch.
   Qualified, folded, mismatched and unknown designators fail closed. *)
Definition source_ordinary_residual_callable_def:
  source_ordinary_residual_callable scopes (SX_Name name) (JE_Name id tc src ty) =
    (name = id /\ tc = SOME "builtin_function" /\
     MEM name source_ordinary_residual_builtins /\
     source_resolve_lexical scopes name = NONE) /\
  source_ordinary_residual_callable scopes _ _ = F
End

(* Legacy environment namespaces are designators ONLY in Attribute dispatch.
   Their absent Source-prelude entries do not authorize unresolved value names.
   Metadata and original spelling must agree; even dangling lexical shadows
   block this inherited identity, rather than reaching legacy spelling dispatch. *)
Definition source_ordinary_environment_root_def:
  source_ordinary_environment_root (SX_Name name) = MEM name ["block";"tx";"chain"] /\
  source_ordinary_environment_root _ = F
End

Definition source_ordinary_environment_designator_def:
  source_ordinary_environment_designator scopes (SX_Name name) (JE_Name id tc src ty) =
    (source_ordinary_environment_root (SX_Name name) /\ name = id /\
     tc = NONE /\ ty = JT_Named NONE name /\
     source_resolve_lexical scopes name = NONE) /\
  source_ordinary_environment_designator scopes _ _ = F
End

(* Inherited result-type claims, not source type inference. Locals/storage are
   canonicalized by the existing bindings/translation context. *)
Definition source_ordinary_claim_type_def:
  source_ordinary_claim_type 0 ctx fallback annotated = fallback /\
  source_ordinary_claim_type (SUC fuel) ctx fallback annotated =
    case annotated of
      JE_Folded original replacement => source_ordinary_claim_type fuel ctx fallback original
    | JE_Int n ty => translate_type (expr_type_ctx ctx) ty
    | JE_Hex s ty => expr_type (translate_expr ctx annotated)
    | JE_Name n tc src ty => expr_type (translate_expr ctx annotated)
    | JE_Decimal s => BaseT DecimalT
    | JE_Str n s => BaseT (StringT n)
    | JE_GenericStr s => BaseT (StringT (LENGTH s))
    | JE_Bytes n s => BaseT (BytesT (Dynamic n))
    | JE_Bool b => BaseT BoolT
    | JE_Attribute e n tc btn btc src ty => expr_type (translate_expr ctx annotated)
    | JE_Subscript e i ty => translate_type (expr_type_ctx ctx) ty
    | JE_UnaryOp op e ty => translate_type (expr_type_ctx ctx) ty
    | JE_BinOp l op r ty => translate_type (expr_type_ctx ctx) ty
    | JE_Compare l op r => BaseT BoolT
    | JE_BoolOp op es => BaseT BoolT
    | JE_IfExp c l r ty => translate_type (expr_type_ctx ctx) ty
    | JE_List es ty => translate_type (expr_type_ctx ctx) ty
    | JE_Tuple es => TupleT (MAP (source_ordinary_claim_type fuel ctx fallback) es)
    | JE_Call f args kws ty src => translate_type (signature_type_ctx ctx src) ty
    | JE_ExtCall n src ats ty t args kws => translate_type (signature_type_ctx ctx src) ty
    | JE_StaticCall n src ats ty t args kws => translate_type (signature_type_ctx ctx src) ty
    | _ => fallback
Termination
  WF_REL_TAC `measure (\(fuel,ctx,fallback,annotated). fuel)` >> simp[]
End

Definition source_ordinary_expected_def:
  source_ordinary_expected expected e =
    if expr_type e = expected then SC_Value e else SC_Invalid SCErr_Type
End

(* Only evaluator-supported syntax can request whole-subtree evaluation.
   Runtime calls/attributes/conditionals are classified BEFORE Source is run;
   their children will still be visited eagerly. No failure enables a retry. *)
Definition source_ordinary_evaluable_def:
  source_ordinary_evaluable (SCE_Literal lit) = T /\
  source_ordinary_evaluable (SCE_Name path) = T /\
  source_ordinary_evaluable SCE_Dynamic = T /\
  source_ordinary_evaluable (SCE_BytesType fixed e) = source_ordinary_evaluable e /\
  source_ordinary_evaluable (SCE_Unary op e) = source_ordinary_evaluable e /\
  source_ordinary_evaluable (SCE_Binary op l r) =
    (source_ordinary_evaluable l /\ source_ordinary_evaluable r) /\
  source_ordinary_evaluable (SCE_Compare op l r) =
    (source_ordinary_evaluable l /\ source_ordinary_evaluable r) /\
  source_ordinary_evaluable (SCE_Boolean op es) = EVERY source_ordinary_evaluable es /\
  source_ordinary_evaluable (SCE_List es) = EVERY source_ordinary_evaluable es /\
  source_ordinary_evaluable (SCE_Tuple es) = EVERY source_ordinary_evaluable es /\
  source_ordinary_evaluable (SCE_Subscript e i) =
    (source_ordinary_evaluable e /\ source_ordinary_evaluable i) /\
  source_ordinary_evaluable (SCE_Builtin b args kws) =
    (IS_SOME (source_const_builtin_arity b) /\
     EVERY source_ordinary_evaluable args /\
     EVERY (\(k,v). source_ordinary_evaluable v) kws) /\
  source_ordinary_evaluable _ = F
Termination
  WF_REL_TAC `measure source_const_expr_size` >> simp[] >>
  rpt strip_tac >> res_tac >> simp[]
End

Definition source_ordinary_fold_def:
  source_ordinary_fold fuel env scopes table constants bindings expected original =
    case source_resolve_candidate scopes table original of
      NONE => SC_NotConstant
    | SOME candidate =>
        if ~source_ordinary_evaluable candidate then SC_NotConstant else
        case source_const_eval constants candidate of
          SC_Value v => source_expr_elaborate fuel env scopes table constants bindings expected original
        | SC_NotConstant => SC_NotConstant
        | SC_Invalid err => SC_Invalid err
        | SC_Unsupported why => SC_Unsupported why
End

(* Required constants never accept NotConstant. This is the same Source
   validation used by bounds, ABI flags/selectors and tuple indices. *)
Definition source_ordinary_required_def:
  source_ordinary_required fuel env scopes table constants bindings expected original =
    source_const_then
      (source_expr_required fuel env.type_defs scopes table constants expected original)
      (source_expr_reify env expected)
End
