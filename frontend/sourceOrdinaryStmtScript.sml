Theory sourceOrdinaryStmt
Ancestors
  sourceOrdinaryClaims sourceOrdinaryExprElaborate sourceOrdinaryExprDefs
  sourceModuleSignature sourceModuleDefs sourceExprDefs sourceExprElaborate
  sourceResolve sourceSyntax jsonAST jsonToVyperExpr vyperAST
  sourceConstAST sourceConstEval list option pair alist
Libs
  intLib

(* Roots are occurrence paths in ClaimsLib's source-field zipper, never keys
   made from expression syntax. Runtime type/dispatch claims remain inherited. *)
Definition source_ordinary_root_def:
  source_ordinary_root fuel roots path original =
    case ALOOKUP roots path of NONE => SM_Error (SME_Declaration "missing-occurrence")
    | SOME claims => if source_claims_source claims = original /\
        source_ordinary_projection fuel (source_claims_legacy claims) = SOME original then
        SM_Ok (source_claims_legacy claims)
      else SM_Error (SME_Declaration "occurrence-source")
End

Definition source_ordinary_expression_def:
  source_ordinary_expression fuel roots path ctx legacy ty original =
    source_module_bind (source_ordinary_root fuel roots path original) (\annotated.
      source_module_expr_result (source_ordinary_expr fuel ctx.sm_env ctx.sm_scopes
        ctx.sm_table ctx.sm_constants ctx.sm_bindings legacy ty original annotated))
End

Definition source_ordinary_infer_def:
  source_ordinary_infer fuel roots path ctx legacy original =
    source_module_bind (source_ordinary_root fuel roots path original) (\annotated.
      let ty = case source_expr_variable ctx.sm_scopes ctx.sm_table ctx.sm_bindings original of
        SOME e => expr_type e
      | NONE => source_ordinary_claim_type fuel legacy NoneT annotated
      in source_ordinary_expression fuel roots path ctx legacy ty original)
End

Definition source_ordinary_assignment_target_def:
  source_ordinary_assignment_target 0 e = NONE /\
  source_ordinary_assignment_target (SUC fuel) e =
    case e of Builtin (TupleT ts) (MakeArray NONE bound) es =>
      OPTION_MAP TupleTarget (OPT_MMAP (source_ordinary_assignment_target fuel) es)
    | _ => OPTION_MAP BaseTarget (expr_base_target e)
End

Definition source_ordinary_iterator_def:
  source_ordinary_iterator fuel roots path ctx legacy ty original =
    source_module_bind (source_ordinary_root fuel roots path original) (\annotated.
    case (original,annotated) of
      (SX_Call callee args kws,JE_Call f js jks jt src) =>
        if source_resolve_name ctx.sm_scopes ctx.sm_table ["range"] <>
             SOME (["$builtin";"range"],SR_Function) \/ callee <> SX_Name "range" \/
           LENGTH args <> LENGTH js then SM_Error (SME_Declaration "range-identity") else
        let build = \oexpr aexpr. source_module_expr_result
          (source_ordinary_expr fuel ctx.sm_env ctx.sm_scopes ctx.sm_table
             ctx.sm_constants ctx.sm_bindings legacy ty oexpr aexpr);
            endpoints = case (args,js) of
              ([stop],[astop]) => SOME (SM_Ok (Literal ty (IntL 0)),build stop astop,
                SX_Binary SCB_Sub stop (SX_Literal (SCL_Int 0)))
            | ([start;stop],[astart;astop]) => SOME (build start astart,build stop astop,
                SX_Binary SCB_Sub stop start)
            | _ => NONE in
        case endpoints of NONE => SM_Error (SME_Declaration "range-arity")
        | SOME (start,stop,delta) => source_module_bind start (\s.
          source_module_bind stop (\e.
          source_module_bind (source_module_expr_result
            (case kws of [] => source_expr_range_bound fuel ctx.sm_env ctx.sm_scopes
               ctx.sm_table ctx.sm_constants ctx.sm_bindings delta
             | [("bound",bound)] => source_expr_range_bound fuel ctx.sm_env ctx.sm_scopes
               ctx.sm_table ctx.sm_constants ctx.sm_bindings bound
             | _ => SC_Invalid SCErr_Keyword)) (\bound. SM_Ok (Range s e,bound))))
    | _ => source_module_bind (source_ordinary_infer fuel roots path ctx legacy original) (\e.
        case expr_type e of ArrayT et bound => if et = ty then SM_Ok (Array e,bound_length bound)
          else SM_Error (SME_Declaration "iterator-type")
        | _ => SM_Error (SME_Declaration "iterator-array")))
End

(* Event identity/field order comes from source module signatures. The legacy
   call helper is not invoked for an event; every original argument is visited. *)
Definition source_ordinary_log_def:
  source_ordinary_log fuel roots path ctx legacy original =
    source_module_bind (source_ordinary_root fuel roots path original) (\annotated.
    case (original,annotated) of (SX_Call callee args kws,JE_Call f js jks ty src) =>
      (case source_expr_path callee of NONE => SM_Error SME_Resolution
       | SOME names => case source_resolve_name ctx.sm_scopes ctx.sm_table names of
         SOME (id,SR_Type) => (case ALOOKUP ctx.sm_events id of
           NONE => SM_Error SME_Resolution
         | SOME (event_id,types) =>
           let fields = MAP (LAST o FST) (FILTER (\(p,b). LENGTH p = SUC (LENGTH id) /\
               TAKE (LENGTH id) p = id /\ (case b of SE_Type t => T | _ => F)) ctx.sm_bindings);
               inputs = if kws = [] then SOME (ZIP (args,js)) else
                 if args = [] /\ ALL_DISTINCT (MAP FST kws) /\ LENGTH fields = LENGTH kws /\
                    LENGTH kws = LENGTH jks then
                   OPT_MMAP (ALOOKUP (ZIP (MAP FST kws,ZIP (MAP SND kws,
                     MAP (\kw. case kw of JKeyword k v => v) jks)))) fields
                 else NONE in
           case inputs of NONE => SM_Error (SME_Declaration "event-keywords")
           | SOME inputs => if LENGTH inputs <> LENGTH types then SM_Error (SME_Declaration "event-arity")
             else source_module_bind (source_module_collect (MAP (\(t,(oexpr,aexpr)).
               source_module_expr_result (source_ordinary_expr fuel ctx.sm_env ctx.sm_scopes
                 ctx.sm_table ctx.sm_constants ctx.sm_bindings legacy t oexpr aexpr))
                 (ZIP (types,inputs)))) (\es. SM_Ok (Log event_id es)))
       | _ => SM_Error SME_Resolution)
    | _ => SM_Error (SME_Declaration "event-call"))
End

Definition source_ordinary_statements_def:
  source_ordinary_statements 0 roots path index ctx legacy ret ss =
    SM_Error (SME_Declaration "statement-fuel") /\
  source_ordinary_statements (SUC fuel) roots path index ctx legacy ret [] = SM_Ok ([],ctx,legacy) /\
  source_ordinary_statements (SUC fuel) roots path index ctx legacy ret (s::ss) =
    source_module_bind (source_ordinary_statement fuel roots (path ++ [index]) ctx legacy ret s)
      (\(s',next,nlegacy). source_module_bind
        (source_ordinary_statements fuel roots path (SUC index) next nlegacy ret ss)
        (\(ss',last,llegacy). SM_Ok (s'::ss',last,llegacy))) /\
  source_ordinary_statement 0 roots path ctx legacy ret s = SM_Error (SME_Declaration "statement-fuel") /\
  source_ordinary_statement (SUC fuel) roots path ctx legacy ret s =
    let infer = \n e. source_ordinary_infer fuel roots (path ++ [n]) ctx legacy e;
        build = \n ty e. source_ordinary_expression fuel roots (path ++ [n]) ctx legacy ty e;
        done = \s. SM_Ok (s,ctx,legacy)
    in case s of
      SS_Pass => done Pass | SS_Break => done Break | SS_Continue => done Continue
    | SS_Return NONE => done (Return NONE)
    | SS_Return (SOME e) => source_module_bind (build 0 ret e) (\r. done (Return (SOME r)))
    | SS_Expr (SX_Call (SX_Attribute receiver "append") [value] []) =>
        source_module_bind (source_ordinary_root fuel roots (path ++ [0])
          (SX_Call (SX_Attribute receiver "append") [value] [])) (\a.
        case a of JE_Call (JE_Attribute ar attr tc btn btc src bt) [av] [] ty sid =>
          source_module_bind (source_module_expr_result
            (source_ordinary_expr fuel ctx.sm_env ctx.sm_scopes ctx.sm_table ctx.sm_constants
              ctx.sm_bindings legacy (source_ordinary_claim_type fuel legacy NoneT ar) receiver ar)) (\r.
          case (expr_base_target r,expr_type r) of (SOME target,ArrayT et bound) =>
            source_module_bind (source_module_expr_result
              (source_ordinary_expr fuel ctx.sm_env ctx.sm_scopes ctx.sm_table ctx.sm_constants
                ctx.sm_bindings legacy et value av)) (\v. done (Append target v))
          | _ => SM_Error (SME_Declaration "append-target"))
        | _ => SM_Error (SME_Declaration "append-shape"))
    | SS_Expr e => source_module_bind (infer 0 e) (\r. done (Expr r))
    | SS_Raise NONE => done (Raise RaiseBare)
    | SS_Raise (SOME (SX_Name "UNREACHABLE")) => done (Raise RaiseUnreachable)
    | SS_Raise (SOME e) => source_module_bind (infer 0 e) (\r. done (Raise (RaiseReason r)))
    | SS_Assert c reason => source_module_bind (build 0 (BaseT BoolT) c) (\ce.
        case reason of NONE => done (Assert ce AssertBare)
        | SOME (SX_Name "UNREACHABLE") => done (Assert ce AssertUnreachable)
        | SOME e => source_module_bind (infer 1 e) (\r. done (Assert ce (AssertReason r))))
    | SS_AnnAssign name annotation value => source_module_bind (source_module_type ctx annotation) (\ty.
        source_module_bind (case value of NONE => SM_Ok (TypeBuiltin ty Empty ty [])
          | SOME e => build 2 ty e) (\e.
        SM_Ok (AnnAssign name ty e,source_module_annotated_local ctx ctx name annotation ty T,
          expr_with_local_types legacy ((name,ty)::expr_local_types legacy))))
    | SS_Assign target value => source_module_bind (infer 0 target) (\old.
        source_module_bind (build 1 (expr_type old) value) (\e.
        case source_ordinary_assignment_target fuel old of
          SOME target => done (Assign target e)
        | NONE => SM_Error (SME_Declaration "assignment-target")))
    | SS_AugAssign target op value => source_module_bind (infer 0 target) (\old.
        source_module_bind (build 2 (expr_type old) value) (\e.
        case expr_base_target old of SOME bt => done (AugAssign (expr_type old) bt (source_expr_binary op) e)
        | NONE => SM_Error (SME_Declaration "assignment-target")))
    | SS_If c yes no => source_module_bind (build 0 (BaseT BoolT) c) (\ce.
        source_module_bind (source_ordinary_statements fuel roots (path ++ [1]) 0 ctx legacy ret yes)
          (\(ys,ignored,il). source_module_bind
            (source_ordinary_statements fuel roots (path ++ [2]) 0 ctx legacy ret no)
            (\(ns,ignored,il). done (If ce ys ns))))
    | SS_For name annotation iterator body => source_module_bind (source_module_type ctx annotation) (\ty.
        source_module_bind (source_ordinary_iterator fuel roots (path ++ [1]) ctx legacy ty iterator) (\(it,bound).
        source_module_bind (source_ordinary_statements fuel roots (path ++ [2]) 0
          (source_module_local ctx name ty F)
          (expr_with_local_types legacy ((name,ty)::expr_local_types legacy)) ret body)
          (\(bs,ignored,il). done (For name ty it bound bs))))
    | SS_Log e => source_module_bind (source_ordinary_log fuel roots (path ++ [0]) ctx legacy e) done
Termination
  WF_REL_TAC `measure (\x. case x of INL (fuel,roots,path,index,ctx,legacy,ret,ss) => fuel
    | INR (fuel,roots,path,ctx,legacy,ret,s) => fuel)` >> simp[]
End
