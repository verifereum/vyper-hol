Theory sourceOrdinaryExprElaborate
Ancestors
  sourceOrdinaryExprDefs sourceOrdinaryBridge sourceExprElaborate sourceExprDefs
  sourceResolve sourceSyntax sourceConstEval jsonToVyperExpr jsonToVyperType
  jsonAST vyperTypeSystem vyperAST option list pair alist

(* Child types are explicit inherited claims. Prefer independently constructed
   runtime bindings when present; never infer a literal type from a replacement. *)
Definition source_ordinary_child_def:
  source_ordinary_child build fuel scopes table bindings ctx fallback original annotated =
    build (case source_expr_variable scopes table bindings original of
             SOME e => expr_type e
           | NONE => source_ordinary_claim_type fuel ctx fallback annotated)
      original annotated
End

Definition source_ordinary_descriptor_def:
  source_ordinary_descriptor fuel scopes table bindings expected original annotated =
    if source_ordinary_projection fuel annotated = SOME original /\
       source_expr_type_hint scopes table bindings original = SOME expected then
      SC_Value (Literal NoneT (BoolL T))
    else SC_Invalid SCErr_Type
End

(* epsilon's inherited identity is checked by source_ordinary_call before
   arguments are visited. Its index-zero type operand uses the same descriptor
   validation as existing type builtins; it is never a runtime Name child. *)
Definition source_ordinary_argument_def:
  source_ordinary_argument build fuel env scopes table constants bindings ctx
      expected callee index original annotated =
    if (index = 1 /\
        (source_expr_intrinsic scopes table bindings callee = SOME SE_AbiDecode \/
         source_expr_builtin_identity scopes table callee = SOME SCB_Convert)) \/
       (index = 0 /\
        (source_expr_named scopes table callee "empty" \/
         source_expr_named scopes table callee "min_value" \/
         source_expr_named scopes table callee "max_value" \/
         (callee = SX_Name "epsilon" /\
          source_resolve_lexical scopes "epsilon" = NONE))) then
      source_ordinary_descriptor fuel scopes table bindings expected original annotated
    else if index = 2 /\ source_expr_named scopes table callee "slice" then
      source_ordinary_required fuel env scopes table constants bindings (BaseT (UintT 256)) original
    else source_ordinary_child build fuel scopes table bindings ctx expected original annotated
End

Definition source_ordinary_keyword_def:
  source_ordinary_keyword build fuel env scopes table constants bindings ctx
      expected callee key original annotated =
    let intrinsic = source_expr_intrinsic scopes table bindings callee in
    if (intrinsic = SOME SE_AbiEncode /\ key = "ensure_tuple") \/
       (intrinsic = SOME SE_AbiDecode /\ key = "unwrap_tuple") \/
       (intrinsic = SOME SE_RawCall /\
        MEM key ["is_delegate_call";"is_static_call";"revert_on_failure"]) \/
       MEM key ["skip_contract_check";"revert_on_failure";"raw_args"] then
      source_ordinary_required fuel env scopes table constants bindings (BaseT BoolT) original
    else if key = "max_outsize" \/ key = "code_offset" then
      source_ordinary_required fuel env scopes table constants bindings (BaseT (UintT 256)) original
    else if intrinsic = SOME SE_AbiEncode /\ key = "method_id" then
      source_const_then
        (source_expr_selector fuel env.type_defs scopes table constants [(key,original)])
        (\mid. case mid of SOME bs =>
           SC_Value (Literal (BaseT (BytesT (Fixed 4))) (BytesL bs))
         | NONE => SC_Invalid SCErr_Type)
    else if key = "output_type" then
      source_ordinary_descriptor fuel scopes table bindings expected original annotated
    else source_ordinary_child build fuel scopes table bindings ctx expected original annotated
End

(* Pop receiver identity is structural, before child normalization. Resolve
   named/qualified roots through the source runtime environment; projections
   grant no typing evidence and do not evaluate their indices. *)
Definition source_ordinary_pop_receiver_def:
  source_ordinary_pop_receiver scopes table bindings receiver =
    if IS_SOME (source_expr_variable scopes table bindings receiver) then T
    else case receiver of
      SX_Subscript recv index => source_ordinary_pop_receiver scopes table bindings recv
    | SX_Attribute recv attr => source_ordinary_pop_receiver scopes table bindings recv
    | _ => F
Termination
  WF_REL_TAC `measure (\(scopes,table,bindings,receiver). source_expr_size receiver)` >> simp[]
End

(* Callable lookup does not evaluate the call. Only pop admits a structural
   place receiver; other dynamic methods retain their existing lookup. *)
Definition source_ordinary_callable_def:
  source_ordinary_callable scopes table bindings callee =
    ((case source_expr_path callee of
       SOME names => IS_SOME (source_resolve_name scopes table names)
     | NONE => F) \/
    (case callee of SX_Attribute receiver name =>
       IS_SOME (source_expr_variable scopes table bindings receiver) \/
       IS_SOME (source_expr_interface scopes table bindings receiver) \/
       (name = "pop" /\ source_ordinary_pop_receiver scopes table bindings receiver)
     | _ => F))
End

(* Inherited residual builtin identity is checked before dispatch, never as
   an evaluator-error retry. Existing Source-resolved calls are unchanged.
   The path-only designator predicate is intentionally unchanged for ordinary
   calls. Pop instead pairs its entire original receiver syntax (including
   subscripts); the special branch below consumes the normalized child once. *)
Definition source_ordinary_call_def:
  source_ordinary_call build fuel env scopes table constants bindings ctx expected
      original callee source_args source_keywords func args kws ty src =
    if ~(case func of JE_Name name (SOME "builtin_function") fsrc fty =>
           if MEM name source_ordinary_residual_builtins then
             source_ordinary_residual_callable scopes callee func
           else source_ordinary_callable scopes table bindings callee
         | _ => source_ordinary_callable scopes table bindings callee) \/
       ~(case (callee,func) of
           (SX_Attribute receiver "pop",JE_Attribute abase "pop" tc btn btc bsrc bty) =>
             source_ordinary_projection fuel abase = SOME receiver
         | _ => source_ordinary_designator callee func) \/
       LENGTH source_args <> LENGTH args \/ LENGTH source_keywords <> LENGTH kws \/
       ~ALL_DISTINCT (MAP FST source_keywords) then SC_Invalid SCErr_Domain else
    let child = source_ordinary_child build fuel scopes table bindings ctx expected;
        arguments = MAP (\(i,(oexpr,aexpr)).
          (oexpr,source_ordinary_argument build fuel env scopes table constants bindings ctx
            expected callee i oexpr aexpr))
          (ZIP (GENLIST I (LENGTH args),ZIP (source_args,args)));
        keywords = MAP (\((key,oexpr),kw). case kw of JKeyword claim aexpr =>
          (key,(oexpr,if key = claim then
            source_ordinary_keyword build fuel env scopes table constants bindings ctx
              expected callee key oexpr aexpr
            else SC_Invalid SCErr_Keyword))) (ZIP (source_keywords,kws))
    in if is_calldata_len_call func args kws then
      SC_Value (Builtin (BaseT (UintT 256)) CalldataLen [])
    else if is_calldata_slice_call func args then
      if source_keywords <> [] then SC_Invalid SCErr_Keyword else
      (case (source_args,args) of
         ([data;start;len],[ad;astart;alen]) =>
           source_const_combine (\v s. case v of SCV_Int n =>
             if 0 < n then SC_Value (Builtin expected (CalldataSlice (Num n)) [s])
             else SC_Invalid SCErr_Domain | _ => SC_Invalid SCErr_Type)
             (source_expr_required fuel env.type_defs scopes table constants (BaseT (UintT 256)) len)
             (build (BaseT (UintT 256)) start astart)
       | _ => SC_Invalid SCErr_Arity)
    else if is_raw_call_calldata_call func args then
      (case (source_args,args) of
         ([target;data],[atarget;adata]) =>
           source_const_combine (\t ks.
             SC_Value (Call expected (RawCallCalldataTarget (raw_call_flags_of_kwargs ks))
               [t;kwarg_expr "value" ks (Literal (BaseT (UintT 256)) (IntL 0))] NONE))
             (build (BaseT AddressT) target atarget)
             (source_const_collect (MAP (\(key,(syntax,result)).
               source_const_then result (\e. SC_Value (key,e))) keywords))
       | _ => SC_Invalid SCErr_Arity)
    else case (callee,func) of
        (SX_Attribute receiver "pop",JE_Attribute abase "pop" tc btn btc bsrc bty) =>
          if source_args <> [] \/ source_keywords <> [] then SC_Invalid SCErr_Arity else
          source_const_then (child receiver abase) (\e.
            case expr_base_target e of NONE => SC_Invalid SCErr_Type
            | SOME target => SC_Value (translate_call ctx func [] [] ty src (SOME target)))
      | _ => source_ordinary_call_layer ctx original func arguments keywords ty src
End

(* External signature/source identities remain explicit inherited claims.
   Operand normalization, including constant flags, is still recursive. *)
Definition source_ordinary_external_def:
  source_ordinary_external build fuel env scopes table constants bindings ctx expected
      static name src ats ty target atarget os js oks jks =
    let child = source_ordinary_child build fuel scopes table bindings ctx expected in
    if LENGTH os <> LENGTH js \/ LENGTH oks <> LENGTH jks then SC_Invalid SCErr_Arity else
    source_const_combine (\t rest.
      let es = FST rest; ks = SND rest;
          extks = ext_call_kwargs ks;
          sigctx = signature_type_ctx ctx src
      in SC_Value (Call expected
        (ExtCall static (kwarg_bool "skip_contract_check" ks F)
          (name,external_argument_types sigctx ats es,translate_type sigctx ty) (MAP FST extks))
        (t :: es ++ MAP SND extks) NONE))
      (child target atarget)
      (source_const_combine (\es ks. SC_Value (es,ks))
        (source_const_collect (MAP (\(oexpr,aexpr). child oexpr aexpr) (ZIP (os,js))))
        (source_const_collect (MAP (\((key,oexpr),kw). case kw of JKeyword claim aexpr =>
          if key <> claim then SC_Invalid SCErr_Keyword else
          source_const_then
            (if key = "skip_contract_check" then
               source_ordinary_required fuel env scopes table constants bindings (BaseT BoolT) oexpr
             else child oexpr aexpr) (\e. SC_Value (key,e))) (ZIP (oks,jks)))))
End

(* Residual AST construction only: the whole-contract checker remains the
   typing authority. In particular no well_typed_expr is demanded of a dynamic
   concat, call, list, field read, or its normalized children individually. *)
Definition source_ordinary_layer_def:
  source_ordinary_layer build fuel env scopes table constants bindings ctx expected original annotated =
    let child = source_ordinary_child build fuel scopes table bindings ctx expected;
        children = \os js. if LENGTH os = LENGTH js then
          source_const_collect (MAP (\(oexpr,aexpr). child oexpr aexpr) (ZIP (os,js)))
          else SC_Invalid SCErr_Arity
    in case (original,annotated) of
      (SX_Name name,JE_Name id tc src ty) =>
        (case source_resolve_name scopes table [name] of
           NONE => SC_Unsupported (SCS_UnresolvedName [name])
         | SOME (path,SR_Constant) => SC_Unsupported (SCS_Syntax "missing-constant-value")
         | SOME resolved => (case source_expr_variable scopes table bindings original of
             SOME e => SC_Value e | NONE => SC_Value (translate_expr ctx annotated)))
    | (SX_Literal lit,_) => SC_Unsupported (SCS_Syntax "unfolded-literal")
    | (SX_Attribute receiver name,JE_Attribute abase attr tc btn btc src ty) =>
        if source_ordinary_environment_root receiver then
          if source_ordinary_environment_designator scopes receiver abase then
            SC_Value (translate_attribute ctx abase (Literal NoneT (BoolL T))
              attr tc btn btc src ty)
          else SC_Invalid SCErr_Domain
        else (case source_expr_variable scopes table bindings original of
           SOME e => SC_Value e
         | NONE => source_const_then (child receiver abase) (\e.
             SC_Value (translate_attribute ctx abase e attr tc btn btc src ty)))
    | (SX_Unary sop operand,JE_UnaryOp op e ty) =>
        source_const_then (child operand e) (\e. SC_Value (translate_unary ctx op e ty))
    | (SX_Binary sop left right,JE_BinOp l op r ty) =>
        source_const_combine (\le re.
          if sop = SCB_Pow /\ ~power_operands_ok expected le re then SC_Invalid SCErr_Domain
          else SC_Value (Builtin expected (Bop (translate_binop op)) [le;re]))
          (build expected left l)
          (if sop = SCB_LShift \/ sop = SCB_RShift then
             source_expr_shift_count (\ct syntax. build ct syntax r)
               fuel env scopes table constants bindings right
           else build expected right r)
    | (SX_Compare sop left right,JE_Compare l op r) =>
        source_const_combine (\le re. SC_Value
          (Builtin (BaseT BoolT) (Bop (translate_binop op)) [le;re]))
          (child left l) (child right r)
    | (SX_Boolean sop os,JE_BoolOp op js) =>
        source_const_then (children os js) (\es.
          if 2 <= LENGTH es then SC_Value (translate_boolop op es)
          else SC_Invalid SCErr_BooleanArity)
    | (SX_IfExp condition left right,JE_IfExp c l r ty) =>
        source_const_combine (\ce es. SC_Value (IfExp expected ce (FST es) (SND es)))
          (build (BaseT BoolT) condition c)
          (source_const_combine (\le re. SC_Value (le,re))
            (build expected left l) (build expected right r))
    | (SX_List os,JE_List js ty) =>
        source_const_then (children os js) (\es. SC_Value (translate_list ctx ty es))
    | (SX_Tuple os,JE_Tuple js) =>
        source_const_then (children os js) (\es. SC_Value
          (Builtin (TupleT (MAP expr_type es)) (MakeArray NONE (Fixed (LENGTH es))) es))
    | (SX_Subscript receiver index,JE_Subscript abase idx ty) =>
        let rty = case source_expr_variable scopes table bindings receiver of
                    SOME e => expr_type e
                  | NONE => source_ordinary_claim_type fuel ctx expected abase in
        source_const_combine (\e i. SC_Value (Subscript expected e i))
          (child receiver abase)
          (case rty of TupleT ts =>
             source_const_then
               (source_expr_index fuel env scopes table constants bindings (LENGTH ts) index)
               (\n. SC_Value (Literal (BaseT (UintT 256)) (IntL (&n))))
           | _ => child index idx)
    | (SX_Call callee os oks,JE_Call func js jks ty src) =>
        source_ordinary_call build fuel env scopes table constants bindings ctx expected
          original callee os oks func js jks ty src
    | (SX_ExtCall (SX_Call (SX_Attribute target name) os oks),
       JE_ExtCall fname src ats ty atarget js jks) =>
        source_ordinary_external build fuel env scopes table constants bindings ctx expected
          F name src ats ty target atarget os js oks jks
    | (SX_StaticCall (SX_Call (SX_Attribute target name) os oks),
       JE_StaticCall fname src ats ty atarget js jks) =>
        source_ordinary_external build fuel env scopes table constants bindings ctx expected
          T name src ats ty target atarget os js oks jks
    | _ => SC_Unsupported (SCS_Syntax "ordinary-residual-shape")
End

(* TOP-LEVEL. The original and claim tree are paired at EVERY recursive call.
   JE_Folded unwraps only its original; its alleged replacement is unreachable.
   SC_NotConstant is the sole evaluator outcome permitting residual recursion.
   Residual classification itself occurs before invoking the common evaluator. *)
Definition source_ordinary_expr_def:
  source_ordinary_expr 0 env scopes table constants bindings ctx expected original annotated =
    SC_Unsupported (SCS_Syntax "ordinary-expression-fuel") /\
  source_ordinary_expr (SUC fuel) env scopes table constants bindings ctx expected original annotated =
    if source_ordinary_projection (SUC fuel) annotated <> SOME original then
      SC_Invalid SCErr_Domain
    else source_const_then (case annotated of
      JE_Folded retained replacement =>
        source_ordinary_expr fuel env scopes table constants bindings ctx expected original retained
    | _ =>
      let build = source_ordinary_expr fuel env scopes table constants bindings ctx in
      let tuple_index = case (original,annotated) of
        (SX_Subscript receiver index,JE_Subscript abase idx ty) =>
          (case (case source_expr_variable scopes table bindings receiver of
                   SOME e => expr_type e
                 | NONE => source_ordinary_claim_type fuel ctx expected abase) of
             TupleT ts => T | _ => F)
        | _ => F in
      let result = if tuple_index then SC_NotConstant else
        case original of SX_Call callee args kws =>
          if source_expr_builtin_identity scopes table callee = SOME SCB_MethodId then
            (case source_expr_elaborate (SUC fuel) env scopes table constants bindings expected original of
               SC_NotConstant => SC_Invalid SCErr_Domain | r => r)
          else source_ordinary_fold (SUC fuel) env scopes table constants bindings expected original
        | _ => source_ordinary_fold (SUC fuel) env scopes table constants bindings expected original
      in case result of SC_NotConstant =>
           source_ordinary_layer build fuel env scopes table constants bindings ctx expected original annotated
         | r => r)
      (source_ordinary_expected expected)
Termination
  WF_REL_TAC `measure (\(fuel,env,scopes,table,constants,bindings,ctx,expected,original,annotated). fuel)` >> simp[]
End
