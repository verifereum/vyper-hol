Theory sourceModuleStmt
Ancestors
  sourceModuleDefs sourceExprElaborate sourceExprDefs sourceResolve sourceSyntax
  sourceConstAST sourceConstEval sourceTypeDefs vyperAST vyperTypeSystem list
Libs
  intLib

Definition source_module_target_def:
  source_module_target 0 ctx e = SM_Error (SME_Declaration "target-fuel") /\
  source_module_target (SUC fuel) ctx e =
    case e of
      SX_Subscript receiver index =>
        source_module_bind (source_module_target fuel ctx receiver) (\bt.
          source_module_bind (source_module_expression fuel ctx (BaseT (UintT 256)) index)
            (\i. SM_Ok (SubscriptTarget bt i)))
    | SX_Attribute receiver name =>
        (case source_expr_variable ctx.sm_scopes ctx.sm_table ctx.sm_bindings e of
           SOME (TopLevelName ty id) => SM_Ok (TopLevelNameTarget id)
         | _ => source_module_bind (source_module_target fuel ctx receiver)
                  (\bt. SM_Ok (AttributeTarget bt name)))
    | SX_Name name =>
        (case source_expr_variable ctx.sm_scopes ctx.sm_table ctx.sm_bindings e of
           SOME (Name ty id) => SM_Ok (NameTarget id)
         | SOME (TopLevelName ty id) => SM_Ok (TopLevelNameTarget id)
         | _ => SM_Error (SME_Declaration "assignment-target"))
    | _ => SM_Error (SME_Declaration "assignment-target")
End

Definition source_module_range_def:
  source_module_range fuel ctx ty args keywords =
    if ~ALL_DISTINCT (MAP FST keywords) then SM_Error (SME_Declaration "range-keywords") else
    let endpoints = case args of
      [stop] => SOME (SX_Literal (SCL_Int 0),stop)
    | [start;stop] => SOME (start,stop)
    | _ => NONE in
    case endpoints of NONE => SM_Error (SME_Declaration "range-arity")
    | SOME (start,stop) =>
      source_module_bind (source_module_expression fuel ctx ty start) (\s.
      source_module_bind (source_module_expression fuel ctx ty stop) (\e.
      source_module_bind (source_module_expr_result
        (case keywords of
           [] => source_expr_range_bound fuel ctx.sm_env ctx.sm_scopes ctx.sm_table
             ctx.sm_constants ctx.sm_bindings (SX_Binary SCB_Sub stop start)
         | [("bound",bound)] => source_expr_range_bound fuel ctx.sm_env ctx.sm_scopes
             ctx.sm_table ctx.sm_constants ctx.sm_bindings bound
         | _ => SC_Invalid SCErr_Keyword)) (\bound. SM_Ok (Range s e,bound))))
End

Definition source_module_iterator_def:
  source_module_iterator fuel ctx ty original =
    case original of SX_Call callee args kws =>
      if source_expr_path callee = SOME ["range"] /\
         source_resolve_name ctx.sm_scopes ctx.sm_table ["range"] =
           SOME (["$builtin";"range"],SR_Function)
      then source_module_range fuel ctx ty args kws
      else SM_Error (SME_Declaration "iterator-call")
    | _ => source_module_bind (source_module_infer fuel ctx original) (\e.
        case expr_type e of ArrayT et bound =>
          if et = ty then SM_Ok (Array e,bound_length bound)
          else SM_Error (SME_Declaration "iterator-type")
        | _ => SM_Error (SME_Declaration "iterator-array"))
End

Definition source_module_log_def:
  source_module_log fuel ctx original =
    case original of SX_Call callee args keywords =>
      (case source_expr_path callee of NONE => SM_Error SME_Resolution
       | SOME path => case source_resolve_name ctx.sm_scopes ctx.sm_table path of
           SOME (id,SR_Type) =>
             (case ALOOKUP ctx.sm_events id of NONE => SM_Error SME_Resolution
              | SOME (event_id,types) =>
                let fields = MAP (LAST o FST) (FILTER (\(path,binding).
                  LENGTH path = SUC (LENGTH id) /\ TAKE (LENGTH id) path = id /\
                  (case binding of SE_Type ty => T | _ => F)) ctx.sm_bindings) in
                let values = if keywords = [] then SOME args else
                  if args = [] /\ ALL_DISTINCT (MAP FST keywords) /\
                     LENGTH fields = LENGTH keywords /\ EVERY (\k. MEM k fields) (MAP FST keywords)
                  then OPT_MMAP (ALOOKUP keywords) fields else NONE in
                case values of NONE => SM_Error (SME_Declaration "event-keywords")
                | SOME values => if LENGTH types = LENGTH values then
                  source_module_bind (source_module_collect (MAP (\(ty,e).
                    source_module_expression fuel ctx ty e) (ZIP (types,values))))
                    (\es. SM_Ok (vyperAST$Log event_id es))
                else SM_Error (SME_Declaration "event-arity"))
         | _ => SM_Error SME_Resolution)
    | _ => SM_Error (SME_Declaration "event-call")
End

Definition source_module_statements_def:
  source_module_statements 0 ctx ret ss = SM_Error (SME_Declaration "statement-fuel") /\
  source_module_statements (SUC fuel) ctx ret [] = SM_Ok ([],ctx) /\
  source_module_statements (SUC fuel) ctx ret (s::ss) =
    source_module_bind (source_module_statement fuel ctx ret s) (\(s',next).
      source_module_bind (source_module_statements fuel next ret ss)
        (\(ss',last). SM_Ok (s'::ss',last))) /\
  source_module_statement 0 ctx ret s = SM_Error (SME_Declaration "statement-fuel") /\
  source_module_statement (SUC fuel) ctx ret s =
    case s of
      SS_Pass => SM_Ok (Pass,ctx)
    | SS_Break => SM_Ok (Break,ctx)
    | SS_Continue => SM_Ok (Continue,ctx)
    | SS_Return NONE => SM_Ok (Return NONE,ctx)
    | SS_Return (SOME e) => source_module_bind (source_module_expression fuel ctx ret e)
        (\r. SM_Ok (Return (SOME r),ctx))
    | SS_Expr e => source_module_bind (source_module_infer fuel ctx e)
        (\r. SM_Ok (Expr r,ctx))
    | SS_Raise NONE => SM_Ok (Raise RaiseBare,ctx)
    | SS_Raise (SOME (SX_Name "UNREACHABLE")) => SM_Ok (Raise RaiseUnreachable,ctx)
    | SS_Raise (SOME e) => source_module_bind (source_module_infer fuel ctx e)
        (\r. SM_Ok (Raise (RaiseReason r),ctx))
    | SS_Assert condition reason =>
        source_module_bind (source_module_expression fuel ctx (BaseT BoolT) condition) (\c.
          case reason of NONE => SM_Ok (Assert c AssertBare,ctx)
          | SOME (SX_Name "UNREACHABLE") => SM_Ok (Assert c AssertUnreachable,ctx)
          | SOME e => source_module_bind (source_module_infer fuel ctx e)
              (\r. SM_Ok (Assert c (AssertReason r),ctx)))
    | SS_AnnAssign name annotation (SOME value) =>
        source_module_bind (source_module_type ctx annotation) (\ty.
        if name IN FDOM ctx.sm_env.var_types then SM_Error (SME_Declaration "duplicate-local") else
        source_module_bind (source_module_expression fuel ctx ty value)
          (\e. SM_Ok (AnnAssign name ty e,
            source_module_annotated_local ctx ctx name annotation ty T)))
    | SS_Assign (SX_Tuple targets) value =>
        source_module_bind (source_module_infer fuel ctx (SX_Tuple targets)) (\old.
        source_module_bind (source_module_collect (MAP (source_module_target fuel ctx) targets)) (\bts.
        source_module_bind (source_module_expression fuel ctx (expr_type old) value)
          (\e. SM_Ok (Assign (TupleTarget (MAP BaseTarget bts)) e,ctx))))
    | SS_Assign target value =>
        source_module_bind (source_module_infer fuel ctx target) (\old.
        source_module_bind (source_module_target fuel ctx target) (\bt.
        source_module_bind (source_module_expression fuel ctx (expr_type old) value)
          (\e. SM_Ok (Assign (BaseTarget bt) e,ctx))))
    | SS_AugAssign target op value =>
        source_module_bind (source_module_infer fuel ctx target) (\old.
        source_module_bind (source_module_target fuel ctx target) (\bt.
        source_module_bind (source_module_expression fuel ctx (expr_type old) value)
          (\e. SM_Ok (AugAssign (expr_type old) bt (source_expr_binary op) e,ctx))))
    | SS_If condition yes no =>
        source_module_bind (source_module_expression fuel ctx (BaseT BoolT) condition) (\c.
        source_module_bind (source_module_statements fuel ctx ret yes) (\(ys,ignored_yes).
        source_module_bind (source_module_statements fuel ctx ret no)
          (\(ns,ignored_no). SM_Ok (If c ys ns,ctx))))
    | SS_For name annotation iterator body =>
        source_module_bind (source_module_type ctx annotation) (\ty.
        if name IN FDOM ctx.sm_env.var_types then SM_Error (SME_Declaration "duplicate-loop-local") else
        source_module_bind (source_module_iterator fuel ctx ty iterator) (\(it,bound).
        source_module_bind (source_module_statements fuel (source_module_local ctx name ty F) ret body)
          (\(bs,ignored). SM_Ok (For name ty it bound bs,ctx))))
    | SS_AnnAssign name annotation NONE =>
        source_module_bind (source_module_type ctx annotation) (\ty.
          if name IN FDOM ctx.sm_env.var_types then SM_Error (SME_Declaration "duplicate-local")
          else SM_Ok (AnnAssign name ty (TypeBuiltin ty Empty ty []),
            source_module_annotated_local ctx ctx name annotation ty T))
    | SS_Log e => source_module_bind (source_module_log fuel ctx e)
        (\log. SM_Ok (log,ctx))
Termination
  WF_REL_TAC `measure (\x. case x of INL (fuel,ctx,ret,ss) => fuel
                                  | INR (fuel,ctx,ret,s) => fuel)` >> simp[]
End
