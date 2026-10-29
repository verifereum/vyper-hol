Theory sourceModuleDefs
Ancestors
  sourceExprElaborate sourceExprDefs sourceResolve sourceResolveModules sourceTypeResolve
  sourceTypeDefs sourceConstAnnotation sourceSyntax sourceConstEnv
  vyperTypeContract vyperTypeSystem vyperAST finite_map alist list
Libs
  intLib

(* TOP-LEVEL: explicit phase outcomes and source-derived lexical contexts.
   Inherited nominal identities/type definitions and module-to-runtime IDs are
   explicit trust inputs; no initializer, folded value, or bound is inherited. *)
Datatype:
  source_module_error = SME_Type source_type_error
    | SME_Constant source_const_error | SME_Unsupported source_const_unsupported
    | SME_RequiredConstant | SME_Resolution | SME_Declaration string
    | SME_Dependencies source_const_env_result | SME_Check
End

Datatype:
  source_module_result = SM_Ok 'a | SM_Error source_module_error
End

(* Preserved parser policy, not inferred compiler metadata. Registry order is
   checked against the original program/loader keys before it is consumed. *)
Datatype:
  source_module_policy = SourceModulePolicy bool bool
End

Definition source_module_policy_default_def:
  source_module_policy_default = SourceModulePolicy F F
End

Definition source_module_policy_for_def:
  source_module_policy_for policies owner =
    case ALOOKUP policies owner of SOME p => p | NONE => source_module_policy_default
End

Definition source_module_nonreentrant_default_def:
  source_module_nonreentrant_default (SourceModulePolicy nr declarations) = nr
End

Definition source_module_declaration_only_def:
  source_module_declaration_only (SourceModulePolicy nr declarations) = declarations
End

Definition source_module_bind_def:
  source_module_bind (SM_Ok x) f = f x /\
  source_module_bind (SM_Error e) f = SM_Error e
End

Definition source_module_type_result_def:
  source_module_type_result (ST_Ok x) = SM_Ok x /\
  source_module_type_result (ST_Error e) = SM_Error (SME_Type e)
End

Definition source_module_expr_result_def:
  source_module_expr_result (SC_Value x) = SM_Ok x /\
  source_module_expr_result SC_NotConstant = SM_Error SME_RequiredConstant /\
  source_module_expr_result (SC_Invalid e) = SM_Error (SME_Constant e) /\
  source_module_expr_result (SC_Unsupported e) = SM_Error (SME_Unsupported e)
End

Definition source_module_collect_def:
  source_module_collect [] = SM_Ok [] /\
  source_module_collect (r::rs) = source_module_bind r (\x.
    source_module_bind (source_module_collect rs) (\xs. SM_Ok (x::xs)))
End

Datatype:
  source_module_context = <|
    sm_env : typing_env;
    sm_scopes : ((string # string list) list) list;
    sm_table : (string list # source_resolve_kind) list;
    sm_constants : (string list # source_const_binding) list;
    sm_bindings : (string list # source_expr_binding) list;
    sm_names : (string list # source_type_identity) list;
    sm_events : (string list # (nsid # type list)) list;
    sm_owner : string list
  |>
End

Definition source_module_expression_def:
  source_module_expression fuel ctx ty e = source_module_expr_result
    (source_expr_elaborate fuel ctx.sm_env ctx.sm_scopes ctx.sm_table
      ctx.sm_constants ctx.sm_bindings ty e)
End

Definition source_module_infer_def:
  source_module_infer fuel ctx e =
    case source_expr_infer fuel ctx.sm_env ctx.sm_scopes ctx.sm_table
      ctx.sm_constants ctx.sm_bindings e of
      NONE => SM_Error (SME_Declaration "expression-type")
    | SOME ty => source_module_expression fuel ctx ty e
End

Definition source_module_bound_expr_def:
  source_module_bound_expr ctx e =
    case source_resolve_expr ctx.sm_scopes ctx.sm_table F e of
      NONE => SM_Error SME_Resolution | SOME r => SM_Ok r
End

(* Canonicalize names/bounds against the ORIGINAL source environment before
   type elaboration. Constructor identities are separately checked in sm_names. *)
Definition source_module_annotation_def:
  source_module_annotation ctx (SCA_Name path) =
    (case source_resolve_name ctx.sm_scopes ctx.sm_table path of
       SOME (id,SR_Type) => SM_Ok (SCA_Name id)
     | SOME (id,SR_FixedBytes n) => SM_Ok (SCA_Name id)
     | SOME (id,SR_Module) =>
         if ALOOKUP ctx.sm_names id = SOME STI_Interface then SM_Ok (SCA_Name id)
         else SM_Error SME_Resolution
     | _ => SM_Error SME_Resolution) /\
  source_module_annotation ctx (SCA_String e) =
    source_module_bind (source_module_bound_expr ctx e) (\r. SM_Ok (SCA_String r)) /\
  source_module_annotation ctx (SCA_Bytes e) =
    source_module_bind (source_module_bound_expr ctx e) (\r. SM_Ok (SCA_Bytes r)) /\
  source_module_annotation ctx (SCA_StaticArray a e) =
    source_module_bind (source_module_annotation ctx a) (\a'.
      source_module_bind (source_module_bound_expr ctx e) (\e'. SM_Ok (SCA_StaticArray a' e'))) /\
  source_module_annotation ctx (SCA_DynArray a e) =
    source_module_bind (source_module_annotation ctx a) (\a'.
      source_module_bind (source_module_bound_expr ctx e) (\e'. SM_Ok (SCA_DynArray a' e'))) /\
  source_module_annotation ctx (SCA_HashMap k v) =
    source_module_bind (source_module_annotation ctx k) (\k'.
      source_module_bind (source_module_annotation ctx v) (\v'. SM_Ok (SCA_HashMap k' v'))) /\
  source_module_annotation ctx (SCA_Tuple fields) =
    source_module_bind (source_module_collect (MAP (source_module_annotation ctx) fields))
      (\fs. SM_Ok (SCA_Tuple fs)) /\
  source_module_annotation ctx (SCA_Qualified q a) =
    source_module_bind (source_module_annotation ctx a) (\a'. SM_Ok (SCA_Qualified q a'))
Termination
  WF_REL_TAC `measure (\(ctx,a). source_const_annotation_size a)` >>
  simp[] >> rpt strip_tac >> res_tac >> simp[]
End

Definition source_module_resolve_type_def:
  source_module_resolve_type ctx a =
    source_module_bind (source_module_annotation ctx a) (\a'.
      source_module_type_result
        (source_type_resolve ctx.sm_env.type_defs ctx.sm_names ctx.sm_constants a'))
End

Definition source_module_type_def:
  source_module_type ctx a = source_module_bind (source_module_resolve_type ctx a)
    (\r. source_module_type_result (source_type_as_type r))
End

Definition source_module_local_def:
  source_module_local ctx name ty assignable =
    let id = ctx.sm_owner ++ [name] in
    ctx with <| sm_env := extend_local ctx.sm_env name ty assignable;
      sm_scopes := [(name,id)]::ctx.sm_scopes;
      sm_table := (id,SR_Dynamic)::ctx.sm_table;
      sm_bindings := (id,SE_Runtime (Name ty name))::ctx.sm_bindings |>
End

Definition source_module_interface_fields_def:
  source_module_interface_fields ctx (SCA_Name names) =
    (case source_resolve_name ctx.sm_scopes ctx.sm_table names of
      SOME (key,SR_Type) => (case ALOOKUP ctx.sm_bindings key of
        SOME (SE_Interface fs) => SOME fs | _ => NONE)
    | SOME (key,SR_Module) => (case ALOOKUP ctx.sm_bindings key of
        SOME (SE_Interface fs) => SOME fs | _ => NONE)
    | _ => NONE) /\
  source_module_interface_fields ctx _ = NONE
End

Definition source_module_annotated_local_def:
  source_module_annotated_local annotations ctx name annotation ty assignable =
    let local = source_module_local ctx name ty assignable in
    case source_module_interface_fields annotations annotation of
      NONE => local
    | SOME fs => local with sm_bindings :=
        (local.sm_owner ++ [name],SE_InterfaceValue (Name ty name) fs)::local.sm_bindings
End

Definition source_module_arg_def:
  source_module_arg ctx (SourceArg name NONE) =
    SM_Error (SME_Declaration "missing-argument-annotation") /\
  source_module_arg ctx (SourceArg name (SOME a)) =
    source_module_bind (source_module_type ctx a) (\ty. SM_Ok (name,ty))
End

Definition source_module_args_def:
  source_module_args ctx args = source_module_collect (MAP (source_module_arg ctx) args)
End

Theorem source_module_exists_refl:
  ?(x:'a). y = x
Proof
  qexists_tac `y` >> simp[]
QED

val source_module_exists_equal = save_thm ("source_module_exists_equal",
  CONV_RULE (DEPTH_CONV ETA_CONV) source_module_exists_refl);

Theorem source_module_local_shadows:
  source_resolve_lexical (source_module_local ctx name ty assignable).sm_scopes name =
    SOME (ctx.sm_owner ++ [name])
Proof
  simp[source_module_local_def, source_resolve_lexical_def]
QED
