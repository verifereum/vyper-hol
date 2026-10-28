Theory sourceExprCall
Ancestors
  sourceExprDefs sourceSyntax sourceResolve sourceConstEval sourceConstValue vyperTypeSystem
  vyperAST alist list

(* Call construction is parameterized by the recursive ORIGINAL-source checker.
   It never invokes jsonToVyper or accepts compiler signature/folding claims. *)
(* Candidate place information comes only from resolved source bindings and
   nominal declarations. Recursive build still validates every index/value. *)
Definition source_expr_place_def:
  source_expr_place env scopes table bindings (SX_Subscript receiver index) =
    (case source_expr_place env scopes table bindings receiver of
       SOME (HashMapT kt vt) => SOME vt
     | SOME (Type (ArrayT et bd)) => SOME (Type et)
     | _ => NONE) /\
  source_expr_place env scopes table bindings e =
    (case source_expr_variable scopes table bindings e of
       SOME e => (case type_place_expr env e of
         SOME vt => SOME vt | NONE => SOME (Type (expr_type e)))
     | NONE => NONE)
Termination
  WF_REL_TAC `measure (\(env,scopes,table,bindings,e). source_expr_size e)` >> simp[]
End

(* HashMaps are places, not standalone values: their NoneT annotation is
   legal only inside a validated subscript chain. Never force a bare map
   through well_typed_expr; validate every original index and the whole place. *)
Definition source_expr_map_place_def:
  source_expr_map_place build env scopes table bindings (SX_Subscript receiver index) =
    source_const_combine (\r i.
      case source_expr_place env scopes table bindings (SX_Subscript receiver index) of
        NONE => SC_Invalid SCErr_Type
      | SOME vt => let ty = case vt of Type ty => ty | _ => NoneT in
          let e = Subscript ty r i in
          if type_place_expr env e = SOME vt then SC_Value e else SC_Invalid SCErr_Type)
      (source_expr_map_place build env scopes table bindings receiver)
      (build (case source_expr_place env scopes table bindings receiver of
        SOME (HashMapT kt vt) => kt | _ => BaseT (UintT 256)) index) /\
  source_expr_map_place build env scopes table bindings original =
    (case source_expr_variable scopes table bindings original of
       SOME e => if IS_SOME (type_place_expr env e) then SC_Value e else SC_Invalid SCErr_Type
     | NONE => SC_Invalid SCErr_Type)
Termination
  WF_REL_TAC `measure (\(build,env,scopes,table,bindings,e). source_expr_size e)` >> simp[]
End

Definition source_expr_target_def:
  source_expr_target build scopes table bindings (SX_Subscript receiver index) =
    source_const_combine (\bt i. SC_Value (SubscriptTarget bt i))
      (source_expr_target build scopes table bindings receiver)
      (build (BaseT (UintT 256)) index) /\
  source_expr_target build scopes table bindings (SX_Attribute receiver name) =
    (case source_expr_variable scopes table bindings (SX_Attribute receiver name) of
       SOME (TopLevelName ty id) => SC_Value (TopLevelNameTarget id)
     | _ => source_const_then (source_expr_target build scopes table bindings receiver)
         (\bt. SC_Value (AttributeTarget bt name))) /\
  source_expr_target build scopes table bindings (SX_Name name) =
    (case source_expr_variable scopes table bindings (SX_Name name) of
       SOME (Name ty id) => SC_Value (NameTarget id)
     | SOME (TopLevelName ty id) => SC_Value (TopLevelNameTarget id)
     | _ => SC_Invalid SCErr_Type) /\
  source_expr_target build scopes table bindings _ = SC_Invalid SCErr_Type
Termination
  WF_REL_TAC `measure (\(build,scopes,table,bindings,e). source_expr_size e)` >> simp[]
End

Definition source_expr_named_def:
  source_expr_named scopes table callee name =
    (source_expr_path callee = SOME [name] /\
     source_resolve_name scopes table [name] = SOME (["$builtin";name],SR_Function))
End

Definition source_expr_calldata_def:
  source_expr_calldata scopes table e =
    (source_expr_path e = SOME ["msg";"data"] /\
     source_resolve_name scopes table ["msg";"data"] =
       SOME (["$builtin";"msg";"data"],SR_Dynamic))
End

Definition source_expr_raw_flags_def:
  source_expr_raw_flags fuel env scopes table constants keywords =
    if ~ALL_DISTINCT (MAP FST keywords) \/
       ~EVERY (\k. MEM k ["value";"max_outsize";"is_delegate_call";"is_static_call";
         "revert_on_failure"]) (MAP FST keywords) then SC_Invalid SCErr_Keyword else
    source_const_then
      (case ALOOKUP keywords "max_outsize" of NONE => SC_Value (SCV_Int 0)
       | SOME e => source_expr_required fuel env.type_defs scopes table constants
           (BaseT (UintT 256)) e) (\out.
    source_const_then
      (source_expr_keyword_bool fuel env.type_defs scopes table constants keywords "is_delegate_call" F) (\delegate.
    source_const_then
      (source_expr_keyword_bool fuel env.type_defs scopes table constants keywords "is_static_call" F) (\static.
    source_const_then
      (source_expr_keyword_bool fuel env.type_defs scopes table constants keywords "revert_on_failure" T) (\revert.
        case out of SCV_Int n => if 0 <= n /\ ~(delegate /\ static) then
          SC_Value <| rcf_max_outsize := Num n; rcf_is_delegate := delegate;
            rcf_is_static := static; rcf_revert_on_failure := revert |>
        else SC_Invalid SCErr_Type | _ => SC_Invalid SCErr_Type))))
End

Definition source_expr_raw_type_def:
  source_expr_raw_type flags =
    if flags.rcf_max_outsize = 0 then
      if flags.rcf_revert_on_failure then NoneT else BaseT BoolT
    else if flags.rcf_revert_on_failure then BaseT (BytesT (Dynamic flags.rcf_max_outsize))
    else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic flags.rcf_max_outsize))]
End

Definition source_expr_internal_call_def:
  source_expr_internal_call build env ty binding args keywords =
    case binding of SE_Function id params defaults ret =>
      if keywords <> [] then SC_Invalid SCErr_Keyword else
      if ty <> ret \/ LENGTH params < LENGTH args \/
         LENGTH args < LENGTH params - defaults then SC_Invalid SCErr_Arity else
      source_const_then (source_const_collect
        (MAP (\(aty,arg). build aty arg) (ZIP (TAKE (LENGTH args) params,args))))
        (\es. source_expr_checked env ty (Call ty (IntCall id) es NONE))
    | SE_Interface fs =>
      (case args of [target] => if keywords = [] /\ ty = BaseT AddressT then
        build (BaseT AddressT) target else SC_Invalid SCErr_Keyword
      | _ => SC_Invalid SCErr_Arity)
    | _ => SC_Unsupported SCS_Call
End

Definition source_expr_external_keyword_def:
  source_expr_external_keyword key = if key = "value" then SOME EKValue else
    if key = "gas" then SOME EKGas else
    if key = "default_return_value" then SOME EKDefault else NONE
End

Definition source_expr_external_call_def:
  source_expr_external_call build fuel env scopes table constants bindings ty static original =
    case source_expr_external_signature scopes table bindings original of
      NONE => SC_Unsupported (SCS_Syntax "external-signature")
    | SOME (name,params,ret,mut,target,args,keywords) =>
      if ty <> ret \/ LENGTH args <> LENGTH params then SC_Invalid SCErr_Arity else
      if ~ALL_DISTINCT (MAP FST keywords) \/
         ~EVERY (\k. k = "skip_contract_check" \/
           IS_SOME (source_expr_external_keyword k)) (MAP FST keywords) then
        SC_Invalid SCErr_Keyword else
      if static <> (mut = Pure \/ mut = View) \/
         (MEM "value" (MAP FST keywords) /\ mut <> Payable) then SC_Invalid SCErr_Type else
      let kws = FILTER (\(k,v). k <> "skip_contract_check") keywords in
      let opts = MAP (THE o source_expr_external_keyword o FST) kws in
      source_const_then
        (source_expr_keyword_bool fuel env.type_defs scopes table constants keywords
          "skip_contract_check" F) (\skip.
      source_const_then (build (BaseT AddressT) target) (\t.
      source_const_then (source_const_collect
        (MAP (\(aty,arg). build aty arg) (ZIP (params,args)))) (\es.
      source_const_then (source_const_collect
        (MAP (\(k,v). build
          (ext_call_kw_type ret (THE (source_expr_external_keyword k))) v) kws)) (\ks.
        source_expr_checked env ty
          (Call ty (ExtCall static skip (name,params,ret) opts) (t::es ++ ks) NONE)))))
End
