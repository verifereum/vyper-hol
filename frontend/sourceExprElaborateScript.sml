Theory sourceExprElaborate
Ancestors
  sourceExprDefs sourceExprCall sourceResolve sourceSyntax sourceTypeResolve sourceConstValue
  sourceConstEval sourceConstValueStructured vyperTypeSystem vyperAST list option
  vyperABI alist finite_map

Definition source_expr_boolean_runtime_def:
  source_expr_boolean_runtime op [] = Literal (BaseT BoolT) (BoolL (op = SCB_And)) /\
  source_expr_boolean_runtime op (e::es) =
    if es = [] then e else IfExp (BaseT BoolT) e
      (if op = SCB_And then source_expr_boolean_runtime op es
       else Literal (BaseT BoolT) (BoolL T))
      (if op = SCB_And then Literal (BaseT BoolT) (BoolL F)
       else source_expr_boolean_runtime op es)
End

Definition source_expr_type_hint_def:
  source_expr_type_hint scopes table bindings (SX_Name name) =
    (case source_resolve_name scopes table [name] of
       SOME (path,kind) =>
         if (case kind of SR_Type => T | SR_FixedBytes n => T | _ => F) then
           (case ALOOKUP bindings path of SOME (SE_Type ty) => SOME ty | _ => NONE)
         else NONE
     | _ => NONE) /\
  source_expr_type_hint scopes table bindings (SX_Tuple children) =
    OPTION_MAP TupleT (OPT_MMAP (source_expr_type_hint scopes table bindings) children) /\
  source_expr_type_hint scopes table bindings (SX_Subscript target (SX_Literal (SCL_Int n))) =
    (if 0 < n then OPTION_MAP (\ty. ArrayT ty (Fixed (Num n)))
       (source_expr_type_hint scopes table bindings target) else NONE) /\
  source_expr_type_hint scopes table bindings _ = NONE
Termination
  WF_REL_TAC `measure (\(scopes,table,bindings,e). source_expr_size e)` >>
  simp[] >> rpt strip_tac >> res_tac >> simp[]
End

(* Inference only supplies candidate operand types. Build checks every original
   operand and keyword, including the independently resolved decode type. *)
Definition source_expr_infer_def:
  source_expr_infer 0 env scopes table constants bindings original = NONE /\
  source_expr_infer (SUC fuel) env scopes table constants bindings original =
    case source_expr_hint scopes table constants bindings original of
      SOME ty => SOME ty
    | NONE => case original of
        SX_Call callee args keywords =>
          (case source_expr_intrinsic scopes table bindings callee of
             SOME SE_AbiEncode =>
               (case (OPT_MMAP (source_expr_infer fuel env scopes table constants bindings) args,
                      source_expr_keyword_bool (SUC fuel) env.type_defs scopes table constants
                        keywords "ensure_tuple" T,
                      source_expr_selector (SUC fuel) env.type_defs scopes table constants keywords) of
                  (SOME ts,SC_Value ensure,SC_Value mid) =>
                    SOME (BaseT (BytesT (Dynamic
                      (vyper_abi_size_bound env.type_defs
                        (case ts of [t] => if ensure then TupleT ts else t | _ => TupleT ts) +
                       abi_encode_method_id_size mid))))
                | _ => NONE)
           | SOME SE_AbiDecode =>
               (case args of [data;target] => source_expr_type_hint scopes table bindings target
                | _ => NONE)
           | SOME SE_RawCall =>
               (case source_expr_raw_flags (SUC fuel) env scopes table constants keywords of
                  SC_Value flags => SOME (source_expr_raw_type flags) | _ => NONE)
           | SOME SE_RawRevert => SOME NoneT
           | _ =>
               if source_expr_named scopes table callee "empty" \/
                  source_expr_named scopes table callee "min_value" \/
                  source_expr_named scopes table callee "max_value" then
                 (case args of [target] => source_expr_type_hint scopes table bindings target
                  | _ => NONE)
               else if source_expr_named scopes table callee "slice" then
                 (case args of [data;start;len] =>
                   (case source_expr_required (SUC fuel) env.type_defs scopes table constants
                     (BaseT (UintT 256)) len of SC_Value (SCV_Int n) =>
                       SOME (BaseT (BytesT (Dynamic (Num n)))) | _ => NONE)
                  | _ => NONE)
               else (case callee of SX_Attribute receiver "pop" =>
                 (case source_expr_place env scopes table bindings receiver of
                    SOME (Type (ArrayT et (Dynamic n))) => SOME et | _ => NONE)
               | _ => case source_resolve_candidate scopes table original of
                  SOME (SCE_Builtin SCB_Convert [arg;target] []) =>
                    (case args of [value;target] =>
                       source_expr_type_hint scopes table bindings target
                     | _ => NONE)
                | _ => NONE))
      | SX_Subscript receiver index =>
          (case source_expr_place env scopes table bindings original of
             SOME (Type ty) => SOME ty
           | SOME (HashMapT kt vt) => SOME NoneT
           | NONE => case source_expr_infer fuel env scopes table constants bindings receiver of
               SOME (ArrayT et bd) => SOME et | _ => NONE)
      | SX_List children =>
          (case children of [] => NONE | child::rest => OPTION_MAP
            (\ty. ArrayT ty (Fixed (LENGTH children)))
            (source_expr_infer fuel env scopes table constants bindings child))
      | SX_Compare op l r => SOME (BaseT BoolT)
      | SX_Attribute receiver name =>
          (case source_expr_infer fuel env scopes table constants bindings receiver of
             SOME (StructT id) => (case FLOOKUP env.type_defs id of
               SOME (StructArgs fields) => ALOOKUP fields name | _ => NONE)
           | _ => case source_expr_callable scopes table bindings receiver of
               SOME (SE_Type (FlagT id)) => SOME (FlagT id) | _ => NONE)
      | SX_Tuple children =>
          OPTION_MAP TupleT (OPT_MMAP
            (source_expr_infer fuel env scopes table constants bindings) children)
      | SX_Unary op child =>
          source_expr_infer fuel env scopes table constants bindings child
      | SX_Binary op left right =>
          if op = SCB_LShift \/ op = SCB_RShift then
            source_expr_infer fuel env scopes table constants bindings left
          else
            (* Literal defaults do not constrain a runtime operand's width. *)
            (case source_resolve_candidate scopes table left of
               SOME resolved =>
                 (case source_const_eval constants resolved of
                    SC_Value v => source_expr_infer fuel env scopes table constants bindings right
                  | _ => source_expr_infer fuel env scopes table constants bindings left)
             | NONE => source_expr_infer fuel env scopes table constants bindings left)
      | _ => NONE
Termination
  WF_REL_TAC `measure (\(fuel,env,scopes,table,constants,bindings,original). fuel)` >> simp[]
End

(* Shift RHS types are independent of the result/LHS type. The pin requires
   an unsigned source domain, but visits a constant arithmetic RHS at its own
   candidate type before using its canonical value. Thus (1-2)+2 is legal here,
   while -(0-1), a signed runtime name and overflowing intermediates are not.
   Both original-tree checks are essential: final-value fit alone is not source
   compatibility. No raw interpreter expression is evaluated or coerced. *)
Definition source_expr_shift_count_def:
  source_expr_shift_count build fuel env scopes table constants bindings original =
    case source_resolve_candidate scopes table original of
      NONE => SC_Unsupported (SCS_Syntax "shift-count-resolution")
    | SOME resolved => case source_const_eval constants resolved of
        SC_Invalid err => SC_Invalid err
      | SC_Unsupported why => SC_Unsupported why
      | SC_Value v =>
          if source_expr_original fuel env.type_defs constants F (BaseT (UintT 256)) resolved /\
             (source_expr_original fuel env.type_defs constants T (BaseT (UintT 256)) resolved \/
              source_expr_original fuel env.type_defs constants T (BaseT (IntT 256)) resolved) /\
             source_expr_fits env.type_defs (BaseT (UintT 256)) v then
            source_expr_reify env (BaseT (UintT 256)) v
          else SC_Invalid SCErr_Type
      | SC_NotConstant =>
          case source_expr_infer fuel env scopes table constants bindings original of
            SOME (BaseT (UintT bits)) => build (BaseT (UintT bits)) original
          | _ => SC_Invalid SCErr_Type
End

(* Deliberately bounded conversion slice: both directions share an exact
   20-octet runtime representation. Wider address destinations need left
   padding, unlike the runtime byte-string cast, and remain unsupported here.
   Source argument inference is independent of the expected destination: in
   particular a checksummed hex literal is an address, not coerced bytes20. *)
(* Constants retain their SOURCE declaration type through the independently
   built signature binding. Their SCV_Hex spelling alone is not a declaration
   type: the zero token, for example, is legal as address or bytes20. *)
Definition source_expr_hex_argument_type_def:
  source_expr_hex_argument_type scopes table constants bindings value =
    case source_expr_path value of
      SOME names =>
        (case source_resolve_name scopes table names of
           SOME (path,SR_Constant) =>
             (case ALOOKUP bindings path of
                SOME (SE_Runtime e) => SOME (expr_type e) | _ => NONE)
         | _ => source_expr_hint scopes table constants bindings value)
    | NONE => source_expr_hint scopes table constants bindings value
End

Definition source_expr_hex_conversion_def:
  source_expr_hex_conversion build env scopes table constants bindings ty args keywords =
    if keywords <> [] then SC_Invalid SCErr_Keyword else
    case args of [value;target] =>
      if source_expr_type_operand scopes table bindings target ty then
        (case source_expr_hex_argument_type scopes table constants bindings value of
           SOME aty =>
             if (aty = BaseT AddressT /\ ty = BaseT (BytesT (Fixed 20))) \/
                (aty = BaseT (BytesT (Fixed 20)) /\ ty = BaseT AddressT) then
               source_const_then (build aty value) (\e.
                 source_expr_checked env ty (TypeBuiltin ty Convert ty [e]))
             else SC_Invalid SCErr_Type
         | NONE => SC_Invalid SCErr_Type)
      else SC_Invalid SCErr_Type
    | _ => SC_Invalid SCErr_Arity
End

(* Runtime-only source forms live behind resolved callable/intrinsic dispatch.
   This preserves those interfaces even for arbitrary explicit test bindings. *)
Definition source_expr_ordinary_call_def:
  source_expr_ordinary_call build fuel env scopes table constants bindings ty callee args keywords =
    if source_expr_named scopes table callee "empty" \/
       source_expr_named scopes table callee "min_value" \/
       source_expr_named scopes table callee "max_value" then
      (case args of [target] =>
         if keywords = [] /\ source_expr_type_hint scopes table bindings target = SOME ty then
           source_expr_checked env ty (TypeBuiltin ty
             (if source_expr_named scopes table callee "empty" then Empty
              else if source_expr_named scopes table callee "min_value" then MinValue else MaxValue) ty [])
         else SC_Invalid SCErr_Type
       | _ => SC_Invalid SCErr_Arity)
    else if source_expr_named scopes table callee "slice" then
      (case args of [data;start;len] =>
         if keywords = [] /\ source_expr_calldata scopes table data then
           source_const_then
             (source_expr_required fuel env.type_defs scopes table constants (BaseT (UintT 256)) len)
             (\v. case v of SCV_Int n =>
                if 0 < n /\ ty = BaseT (BytesT (Dynamic (Num n))) then
                  source_const_then (build (BaseT (UintT 256)) start)
                    (\s. source_expr_checked env ty (Builtin ty (CalldataSlice (Num n)) [s]))
                else SC_Invalid SCErr_Type
              | _ => SC_Invalid SCErr_Type)
         else SC_Invalid SCErr_Type
       | _ => SC_Invalid SCErr_Arity)
    else case callee of SX_Attribute receiver "pop" =>
      if args = [] /\ keywords = [] then
        source_const_then (source_expr_target build scopes table bindings receiver)
          (\bt. source_expr_checked env ty (Pop ty bt))
      else SC_Invalid SCErr_Arity
    | _ => SC_Unsupported SCS_Call
End

(* Fuel exhaustion is explicit Unsupported, never a legacy translation retry.
   Constant replacement requires an independently checked ORIGINAL source tree,
   not successful final literal reification or contextual child reification.
   Dynamic children retain runtime ASTs, evaluation order and short circuiting. *)
Definition source_expr_build_def:
  source_expr_build 0 env scopes table constants bindings ty original =
    SC_Unsupported (SCS_Syntax "expression-fuel") /\
  source_expr_build (SUC fuel) env scopes table constants bindings ty original =
    case source_expr_candidate scopes table bindings original of
    | NONE => SC_Unsupported (SCS_Syntax "expression-resolution")
    | SOME resolved =>
      (case source_const_eval constants resolved of
       | SC_Invalid err => SC_Invalid err
       | SC_Value v =>
           if source_expr_original (SUC fuel) env.type_defs constants T ty resolved then
             source_expr_reify env ty v
           else SC_Invalid SCErr_Type
       | _ => case original of
      | SX_Literal lit =>
          if source_expr_literal_domain lit ty then
            source_const_then (source_const_eval constants resolved)
              (source_expr_reify env ty)
          else SC_Unsupported (SCS_Syntax "source-literal-domain")
      | SX_Name name =>
          (case source_expr_variable scopes table bindings original of
             SOME e => source_expr_finish env constants ty resolved e
           | NONE => source_const_then (source_const_eval constants resolved)
               (source_expr_reify env ty))
      | SX_Attribute receiver name =>
          (case source_expr_variable scopes table bindings original of
             SOME e => source_expr_finish env constants ty resolved e
           | NONE =>
               (case source_expr_callable scopes table bindings receiver of
                  SOME (SE_Type (FlagT id)) =>
                    source_expr_checked env ty (FlagMember ty id name)
                | _ => case source_expr_infer fuel env scopes table constants bindings receiver of
                  NONE => SC_Unsupported (SCS_Syntax "attribute-receiver-type")
                | SOME rty => source_const_then
                    (source_expr_build fuel env scopes table constants bindings rty receiver)
                    (\e. source_expr_checked env ty (Attribute ty e name))))
      | SX_Unary op child =>
          if source_expr_unary_domain op ty then
            source_const_then
              (source_expr_build fuel env scopes table constants bindings ty child)
              (\e. source_expr_finish env constants ty resolved
                (Builtin ty (source_expr_unary op) [e]))
          else SC_Unsupported (SCS_Syntax "source-unary-domain")
      | SX_Binary op left right =>
          if source_expr_binary_domain op ty then
            source_const_combine (\l r.
              source_expr_finish env constants ty resolved
                (Builtin ty (Bop (source_expr_binary op)) [l;r]))
              (source_expr_build fuel env scopes table constants bindings ty left)
              (if op = SCB_LShift \/ op = SCB_RShift then
                 source_expr_shift_count
                   (source_expr_build fuel env scopes table constants bindings)
                   fuel env scopes table constants bindings right
               else source_expr_build fuel env scopes table constants bindings ty right)
          else SC_Unsupported (SCS_Syntax "source-binary-domain")
      | SX_Compare op left right =>
          if op = SCC_In \/ op = SCC_NotIn then
            (case source_expr_infer fuel env scopes table constants bindings right of
               SOME (ArrayT et bd) => source_const_combine (\l r.
                 source_expr_checked env ty (Builtin ty (Bop (if op = SCC_In then In else NotIn)) [l;r]))
                 (source_expr_build fuel env scopes table constants bindings et left)
                 (source_expr_build fuel env scopes table constants bindings (ArrayT et bd) right)
             | SOME (FlagT id) => source_const_combine (\l r.
                 source_expr_checked env ty (Builtin ty (Bop (if op = SCC_In then In else NotIn)) [l;r]))
                 (source_expr_build fuel env scopes table constants bindings (FlagT id) left)
                 (source_expr_build fuel env scopes table constants bindings (FlagT id) right)
             | _ => SC_Invalid SCErr_Type)
          else (case (source_expr_compare op,
                 source_expr_infer fuel env scopes table constants bindings left) of
             (SOME bop,SOME operand_ty) =>
               source_const_combine (\l r.
                 source_expr_finish env constants ty resolved (Builtin ty (Bop bop) [l;r]))
                 (source_expr_build fuel env scopes table constants bindings operand_ty left)
                 (source_expr_build fuel env scopes table constants bindings operand_ty right)
           | _ => SC_Unsupported (SCS_Syntax "comparison-inference"))
      | SX_Boolean op children =>
          source_const_then
            (source_const_collect (MAP
              (source_expr_build fuel env scopes table constants bindings (BaseT BoolT)) children))
            (\es. if 2 <= LENGTH es then source_expr_finish env constants ty resolved
                    (source_expr_boolean_runtime op es)
                  else SC_Invalid SCErr_BooleanArity)
      | SX_IfExp condition left right =>
          source_const_combine (\c es.
            source_expr_checked env ty (IfExp ty c (FST es) (SND es)))
            (source_expr_build fuel env scopes table constants bindings (BaseT BoolT) condition)
            (source_const_combine (\l r. SC_Value (l,r))
              (source_expr_build fuel env scopes table constants bindings ty left)
              (source_expr_build fuel env scopes table constants bindings ty right))
      | SX_List children =>
          (case ty of ArrayT et bd =>
            source_const_then (source_const_collect (MAP
              (source_expr_build fuel env scopes table constants bindings et) children))
              (\es. source_expr_checked env ty
                (Builtin ty (MakeArray (SOME et) bd) es))
           | _ => SC_Invalid SCErr_Type)
      | SX_Tuple children =>
          (case ty of TupleT ts =>
            if LENGTH ts = LENGTH children /\ children <> [] then
              source_const_then (source_const_collect (MAP (\(et,child).
                source_expr_build fuel env scopes table constants bindings et child)
                (ZIP (ts,children)))) (\es. source_expr_finish env constants ty resolved
                  (Builtin ty (MakeArray NONE (Fixed (LENGTH ts))) es))
            else SC_Invalid SCErr_Arity
           | _ => SC_Invalid SCErr_Type)
      | SX_Subscript receiver index =>
          (case source_expr_infer fuel env scopes table constants bindings receiver of
             NONE => SC_Unsupported (SCS_Syntax "subscript-inference")
           | SOME receiver_ty =>
               source_const_combine (\e i. source_expr_checked env ty (Subscript ty e i))
                 (case source_expr_place env scopes table bindings receiver of
                    SOME (HashMapT kt vt) => source_expr_map_place
                      (source_expr_build fuel env scopes table constants bindings)
                      env scopes table bindings receiver
                  | _ => source_expr_build fuel env scopes table constants bindings receiver_ty receiver)
                 (case receiver_ty of TupleT ts =>
                    source_const_then
                      (source_expr_required fuel env.type_defs scopes table constants
                        (BaseT (UintT 256)) index) (\v.
                        case v of SCV_Int i =>
                          if 0 <= i /\ Num i < LENGTH ts then
                            SC_Value (Literal (BaseT (UintT 256)) (IntL i))
                          else SC_Invalid SCErr_Index
                        | _ => SC_Invalid SCErr_Type)
                  | _ => source_expr_build fuel env scopes table constants bindings
                      (case source_expr_place env scopes table bindings receiver of
                         SOME (HashMapT kt vt) => kt | _ => BaseT (UintT 256)) index))
      | SX_Call callee args keywords =>
          (case source_expr_callable scopes table bindings callee of
             SOME (SE_Function id params defaults ret) =>
               source_expr_internal_call
                 (source_expr_build fuel env scopes table constants bindings) env ty
                 (SE_Function id params defaults ret) args keywords
           | SOME (SE_Interface fs) => source_expr_internal_call
                 (source_expr_build fuel env scopes table constants bindings) env ty
                 (SE_Interface fs) args keywords
           | _ => case source_expr_intrinsic scopes table bindings callee of
             SOME SE_AbiEncode =>
               if ~ALL_DISTINCT (MAP FST keywords) \/
                  ~EVERY (\k. k = "ensure_tuple" \/ k = "method_id") (MAP FST keywords)
               then SC_Invalid SCErr_Keyword else
               source_const_combine (\ensure mid.
                 source_const_then (source_const_collect (MAP (\arg.
                   case source_expr_infer fuel env scopes table constants bindings arg of
                     NONE => SC_Unsupported (SCS_Syntax "abi-argument-inference")
                   | SOME aty => source_expr_build fuel env scopes table constants bindings aty arg)
                   args)) (\es. source_expr_checked env ty
                     (TypeBuiltin ty (AbiEncode ensure mid) (TupleT (MAP expr_type es)) es)))
                 (source_expr_keyword_bool fuel env.type_defs scopes table constants keywords "ensure_tuple" T)
                 (source_expr_selector fuel env.type_defs scopes table constants keywords)
           | SOME SE_AbiDecode =>
               if ~ALL_DISTINCT (MAP FST keywords) \/
                  ~EVERY (\k. k = "unwrap_tuple") (MAP FST keywords)
               then SC_Invalid SCErr_Keyword else
               (case args of [data;target] =>
                 if source_expr_type_operand scopes table bindings target ty then
                   source_const_combine (\unwrap e. source_expr_checked env ty
                     (TypeBuiltin ty (AbiDecode unwrap) ty [e]))
                     (source_expr_keyword_bool fuel env.type_defs scopes table constants keywords "unwrap_tuple" T)
                     (case source_expr_infer fuel env scopes table constants bindings data of
                        NONE => SC_Unsupported (SCS_Syntax "abi-data-inference")
                      | SOME dty => source_expr_build fuel env scopes table constants bindings dty data)
                 else SC_Invalid SCErr_Type
                | _ => SC_Invalid SCErr_Arity)
           | SOME SE_RawRevert =>
               if keywords <> [] then SC_Unsupported (SCS_Syntax "raw-revert-keywords") else
               (case args of [data] =>
                 source_const_then
                   (case source_expr_infer fuel env scopes table constants bindings data of
                      NONE => SC_Unsupported (SCS_Syntax "raw-revert-data-inference")
                    | SOME dty => source_expr_build fuel env scopes table constants bindings dty data)
                   (\e. source_expr_checked env ty (Call ty RawRevert [e] NONE))
                | _ => SC_Invalid SCErr_Arity)
           | SOME SE_RawCall =>
               source_const_then (source_expr_raw_flags fuel env scopes table constants keywords) (\flags.
               case args of [target;data] =>
                 source_const_then
                   (source_expr_build fuel env scopes table constants bindings (BaseT AddressT) target) (\t.
                 source_const_then
                   (case ALOOKUP keywords "value" of NONE =>
                      SC_Value (Literal (BaseT (UintT 256)) (IntL 0))
                    | SOME v => source_expr_build fuel env scopes table constants bindings (BaseT (UintT 256)) v) (\v.
                 if ty <> source_expr_raw_type flags then SC_Invalid SCErr_Type else
                 if source_expr_calldata scopes table data then
                   source_expr_checked env ty (Call ty (RawCallCalldataTarget flags) [t;v] NONE)
                 else source_const_then
                   (case source_expr_infer fuel env scopes table constants bindings data of
                      NONE => SC_Unsupported (SCS_Syntax "raw-call-data-inference")
                    | SOME dty => source_expr_build fuel env scopes table constants bindings dty data)
                   (\d. source_expr_checked env ty (Call ty (RawCallTarget flags) [t;d;v] NONE))))
               | _ => SC_Invalid SCErr_Arity)
           | NONE => case source_expr_builtin_identity scopes table callee of
             SOME b =>
               if b = SCB_Convert then source_expr_hex_conversion
                 (source_expr_build fuel env scopes table constants bindings)
                 env scopes table constants bindings ty args keywords
               else source_const_then (source_const_collect (MAP (\arg.
                 case (if b = SCB_Len \/ b = SCB_Keccak256 \/ b = SCB_MethodId then
                   source_expr_infer fuel env scopes table constants bindings arg
                 else source_expr_argument_type scopes table constants bindings ty b arg) of
                   NONE => SC_Unsupported (SCS_Syntax "builtin-argument-inference")
                 | SOME aty => source_expr_build fuel env scopes table constants bindings aty arg)
                 args)) (\es.
                   if b = SCB_MethodId then
                     source_const_then
                       (case keywords of
                          [] => SC_Value ()
                        | [(key,SX_Name n)] => SC_Value ()
                        | [(key,SX_Subscript constructor bound)] =>
                            source_const_then
                              (source_expr_required fuel env.type_defs scopes table constants
                                (BaseT (UintT 256)) bound) (\_. SC_Value ())
                        | _ => SC_Unsupported (SCS_Syntax "method-id-output-type"))
                       (\_. if LENGTH es = 1 /\
                              (case expr_type (HD es) of BaseT (StringT n) => T | _ => F) then
                              source_const_then (source_const_eval constants resolved) (\v.
                                if source_expr_method_type ty v then source_expr_reify env ty v
                                else SC_Invalid SCErr_Type)
                            else SC_Invalid SCErr_Type)
                   else if keywords <> [] then SC_Invalid SCErr_Keyword
                   else case source_expr_builtin b of
                     NONE => SC_Unsupported (SCS_Builtin b)
                   | SOME builtin => source_expr_finish env constants ty resolved
                       (Builtin ty builtin es))
           | _ => source_expr_ordinary_call
               (source_expr_build fuel env scopes table constants bindings)
               fuel env scopes table constants bindings ty callee args keywords)
      | SX_ExtCall call => source_expr_external_call
          (source_expr_build fuel env scopes table constants bindings) fuel env scopes table
          constants bindings ty F call
      | SX_StaticCall call => source_expr_external_call
          (source_expr_build fuel env scopes table constants bindings) fuel env scopes table
          constants bindings ty T call
      | _ => SC_Unsupported (SCS_Syntax "ordinary-expression"))
Termination
  WF_REL_TAC `measure (\(fuel,env,scopes,table,constants,bindings,ty,original). fuel)` >> simp[]
End

(* Clean opt-in entry: no old JSON translator is reachable. *)
Definition source_expr_elaborate_def:
  source_expr_elaborate fuel env scopes table constants bindings ty original =
    source_const_then
      (source_expr_build fuel env scopes table constants bindings ty original)
      (source_expr_checked env ty)
End

Definition source_expr_annotated_def:
  source_expr_annotated fuel env scopes table constants bindings names annotation original =
    source_type_bind (source_type_resolve env.type_defs names constants annotation) (\r.
      source_type_bind (source_type_as_type r) (\ty.
        ST_Ok (source_expr_elaborate fuel env scopes table constants bindings ty original)))
End

(* Executable required constants share resolution, independent original-tree
   validation and the mathematical evaluator, not runtime literal inspection.
   Annotation bounds remain a distinct source_type_resolve context. *)
Definition source_expr_constant_def:
  source_expr_constant fuel env scopes table constants bindings ty original =
    source_expr_required fuel env.type_defs scopes table constants ty original
End

Definition source_expr_flag_def:
  source_expr_flag fuel env scopes table constants bindings original =
    source_const_then
      (source_expr_constant fuel env scopes table constants bindings (BaseT BoolT) original)
      (\v. case v of SCV_Bool b => SC_Value b | _ => SC_Invalid SCErr_Type)
End

Definition source_expr_index_def:
  source_expr_index fuel env scopes table constants bindings count original =
    source_const_then
      (source_expr_constant fuel env scopes table constants bindings (BaseT (UintT 256)) original)
      (\v. case v of SCV_Int i =>
              if 0 <= i /\ Num i < count then SC_Value (Num i) else SC_Invalid SCErr_Index
            | _ => SC_Invalid SCErr_Type)
End

Definition source_expr_range_bound_def:
  source_expr_range_bound fuel env scopes table constants bindings original =
    source_const_then
      (source_expr_constant fuel env scopes table constants bindings (BaseT (UintT 256)) original)
      (\v. case v of SCV_Int i =>
              if 0 < i /\ i < &(2 ** 256) then SC_Value (Num i) else SC_Invalid SCErr_Domain
            | _ => SC_Invalid SCErr_Type)
End
