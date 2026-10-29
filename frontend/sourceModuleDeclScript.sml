Theory sourceModuleDecl
Ancestors
  sourceModuleEnv sourceModuleStmt sourceModuleDefs sourceExprElaborate
  sourceTypeDefs sourceSyntax sourceConstAnnotation sourceConstAST
  vyperTypeContract vyperTypeSystem vyperAST list alist finite_map
Libs
  intLib

Definition source_module_decorators_def:
  source_module_decorators decorators =
    if EVERY (\d. case d of SX_Name n => MEM n
      ["external";"internal";"deploy";"pure";"view";"payable";"nonreentrant";"reentrant";"raw_return";"abstract"]
      | SX_Call (SX_Name "override") [SX_Name alias] [] => T
      | _ => F) decorators then
      SM_Ok (MAP (\d. case d of SX_Name n => n | _ => "override") decorators)
    else SM_Error (SME_Declaration "decorator")
End

Definition source_module_visibility_def:
  source_module_visibility ds = if MEM "external" ds then External
    else if MEM "deploy" ds then Deploy else Internal
End

Definition source_module_mutability_def:
  source_module_mutability ds = if MEM "pure" ds then Pure
    else if MEM "view" ds then View else if MEM "payable" ds then Payable else Nonpayable
End

Definition source_module_return_type_def:
  source_module_return_type ctx NONE = SM_Ok NoneT /\
  source_module_return_type ctx (SOME a) = source_module_type ctx a
End

Definition source_module_variable_def:
  source_module_variable fuel ctx slots name annotation initializer =
    source_module_bind (source_module_resolve_type ctx annotation) (\r.
      let qs = source_type_qualifiers r in
      let vis = if MEM SCQ_Public qs then Public else Private in
      let slot = ALOOKUP slots (ctx.sm_env.current_src,name) in
      if MEM SCQ_Indexed qs then SM_Error (SME_Declaration "indexed-variable") else
      case source_type_vtype r of
        HashMapT kt vt =>
          if initializer <> NONE \/ MEM SCQ_Constant qs \/ MEM SCQ_Immutable qs
          then SM_Error (SME_Declaration "hashmap-initializer")
          else SM_Ok (HashMapDecl vis (MEM SCQ_Transient qs) name kt vt slot)
      | Type ty =>
          if MEM SCQ_Constant qs then
            (case initializer of NONE => SM_Error (SME_Declaration "constant-initializer")
             | SOME e => source_module_bind (source_module_expression fuel ctx ty e)
                 (\value. SM_Ok (VariableDecl vis (Constant value) name ty NONE)))
          else if initializer <> NONE then SM_Error (SME_Declaration "nonconstant-initializer")
          else SM_Ok (VariableDecl vis
            (if MEM SCQ_Immutable qs then Immutable
             else if MEM SCQ_Transient qs then Transient else Storage) name ty
            (if MEM SCQ_Immutable qs then NONE else slot)))
End

Definition source_module_event_field_def:
  source_module_event_field ctx (SourceArg name NONE) =
    SM_Error (SME_Declaration "missing-event-annotation") /\
  source_module_event_field ctx (SourceArg name (SOME annotation)) =
    source_module_bind (source_module_resolve_type ctx annotation) (\r.
      case source_type_vtype r of Type ty =>
        if EVERY ($= SCQ_Indexed) (source_type_qualifiers r) then
          SM_Ok ((name,ty),MEM SCQ_Indexed (source_type_qualifiers r))
        else SM_Error (SME_Declaration "event-qualifier")
      | _ => SM_Error (SME_Declaration "event-field"))
End

Definition source_module_interface_function_def:
  source_module_interface_function ctx (SD_Function name decorators args defaults returns body) =
    source_module_bind (source_module_decorators decorators) (\ds.
    source_module_bind (source_module_args ctx args) (\params.
    source_module_bind (source_module_return_type ctx returns) (\ret.
      case body of [SS_Expr (SX_Name mode)] =>
        if defaults = [] /\ decorators = [] /\ MEM mode ["pure";"view";"nonpayable";"payable"] then
          SM_Ok (name,params,ret,source_module_mutability [mode])
        else SM_Error (SME_Declaration "interface-signature")
      | _ => SM_Error (SME_Declaration "interface-body")))) /\
  source_module_interface_function ctx _ = SM_Error (SME_Declaration "interface-member")
End

(* Signature pass: placeholders occur ONLY in this private phase's defaults;
   their length supplies arity to fn_sigs. No placeholder can reach phase output. *)
Definition source_module_signature_def:
  source_module_signature fuel ctx slots declaration =
    case declaration of
      SD_Variable name annotation initializer =>
        source_module_bind (source_module_variable fuel ctx slots name annotation initializer)
          (\tl. SM_Ok [tl])
    | SD_Function name decorators args defaults returns body =>
        source_module_bind (source_module_decorators decorators) (\ds.
        source_module_bind (source_module_args ctx args) (\params.
        source_module_bind (source_module_return_type ctx returns) (\ret.
          if LENGTH defaults <= LENGTH args /\ ALL_DISTINCT (MAP FST params) then
            SM_Ok [FunctionDecl (source_module_visibility ds) (source_module_mutability ds)
              (MEM "nonreentrant" ds) (MEM "raw_return" ds) name params
              (REPLICATE (LENGTH defaults) (Literal NoneT (IntL 0))) ret []]
          else SM_Error (SME_Declaration "parameters"))))
    | SD_Struct name fields => source_module_bind (source_module_args ctx fields)
        (\fs. SM_Ok [StructDecl name fs])
    | SD_Flag name members => SM_Ok [FlagDecl name members]
    | SD_Event name fields => source_module_bind
        (source_module_collect (MAP (source_module_event_field ctx) fields))
        (\fs. SM_Ok [EventDecl name fs])
    | SD_Interface name ds => source_module_bind
        (source_module_collect (MAP (source_module_interface_function ctx) ds))
        (\fs. SM_Ok [InterfaceDecl name fs])
    | SD_Import imports => SM_Ok []
    (* These are validated against ORIGINAL syntax by source_module_link before
       any body is emitted. Erasure here is private to the signature pass. *)
    | SD_Exports e => SM_Ok []
    | SD_Initializes e => SM_Ok []
    | SD_Uses e => SM_Ok []
    | SD_Implements e => SM_Ok []
End

Definition source_module_signatures_def:
  source_module_signatures fuel ctx slots syntax =
    source_module_bind (source_module_collect
      (MAP (source_module_signature fuel ctx slots) (source_module_declarations syntax)))
      (\tls. SM_Ok (FLAT tls))
End

Definition source_module_function_context_def:
  source_module_function_context ctx name args params =
    FOLDL (\cx (arg,id,ty). case arg of
      SourceArg ignored (SOME annotation) =>
        source_module_annotated_local ctx cx id annotation ty T
    | _ => source_module_local cx id ty T)
      (ctx with sm_owner := ctx.sm_owner ++ [name]) (ZIP (args,params))
End

Definition source_module_body_def:
  source_module_body fuel ctx slots declaration =
    source_module_bind (source_module_signature fuel ctx slots declaration) (\tls.
      case (declaration,tls) of
        (SD_Function name decorators args defaults returns body,
          [FunctionDecl vis mut nr raw id params placeholders ret ignored]) =>
          if MEM (SX_Name "abstract") decorators then SM_Ok [] else
          let fctx = source_module_function_context ctx name args params in
          source_module_bind (source_module_collect
            (MAP (\(ty,e). source_module_expression fuel ctx ty e)
              (ZIP (MAP SND (DROP (LENGTH params - LENGTH defaults) params),defaults)))) (\ds.
          source_module_bind (source_module_statements fuel fctx ret body)
            (\(ss,last). SM_Ok [FunctionDecl vis mut nr raw id params ds ret ss]))
      | _ => SM_Ok tls)
End

(* Module-interface signatures are checked from ORIGINAL .vyi syntax. Their
   private FunctionDecls supply signatures only; they never reach body output.
   In particular no ellipsis is replaced with Pass or a fabricated return. *)
Definition source_module_policy_signature_def:
  source_module_policy_signature fuel ctx slots policy declaration =
    case declaration of SD_Function name decorators args defaults returns body =>
      if source_module_declaration_only policy then
        if body <> [SS_Expr SX_Ellipsis] \/ name = "__init__" \/ name = "__default__" \/
           ~EVERY (\d. MEM d [SX_Name "external"; SX_Name "pure";
             SX_Name "view"; SX_Name "payable"]) decorators \/
           ~EVERY ($= SX_Ellipsis) defaults then
          SM_Error (SME_Declaration "interface-signature")
        else source_module_bind (source_module_args ctx args) (\params.
          source_module_bind (source_module_return_type ctx returns) (\ret.
            if LENGTH defaults <= LENGTH args /\ ALL_DISTINCT (MAP FST params) then
              SM_Ok [FunctionDecl External
                (source_module_mutability (MAP (\d. case d of SX_Name n => n | _ => "") decorators))
                F F name params (REPLICATE (LENGTH defaults) (Literal NoneT (IntL 0))) ret []]
            else SM_Error (SME_Declaration "parameters")))
      else source_module_bind (source_module_signature fuel ctx slots declaration) (\tls.
        SM_Ok (MAP (\tl. case tl of FunctionDecl vis mut nr raw id ps ds ret ss =>
          FunctionDecl vis mut
            (mut <> Pure /\ (nr \/ (source_module_nonreentrant_default policy /\
              vis = External /\ ~MEM (SX_Name "reentrant") decorators))) raw id ps ds ret ss
          | _ => tl) tls))
    | _ => source_module_signature fuel ctx slots declaration
End

Definition source_module_policy_signatures_def:
  source_module_policy_signatures fuel ctx slots policy syntax =
    source_module_bind (source_module_collect
      (MAP (source_module_policy_signature fuel ctx slots policy)
        (source_module_declarations syntax))) (\tls. SM_Ok (FLAT tls))
End

Definition source_module_policy_body_def:
  source_module_policy_body fuel ctx slots policy declaration =
    source_module_bind (source_module_policy_signature fuel ctx slots policy declaration) (\tls.
      case declaration of SD_Function name decorators args defaults returns body =>
        if source_module_declaration_only policy then SM_Ok [] else
        source_module_bind (source_module_body fuel ctx slots declaration) (\bodies.
          SM_Ok (MAP (\tl. case (tls,tl) of
            ([FunctionDecl vis mut nr raw id ps ds ret ss],
             FunctionDecl bv bm bn br bi bp bd bt bs) =>
               FunctionDecl bv bm nr br bi bp bd bt bs
            | _ => tl) bodies))
      | _ => SM_Ok tls)
End

Definition source_module_policy_bodies_def:
  source_module_policy_bodies fuel ctx slots policy syntax =
    source_module_bind (source_module_collect
      (MAP (source_module_policy_body fuel ctx slots policy)
        (source_module_declarations syntax))) (\tls. SM_Ok (FLAT tls))
End

Definition source_module_bodies_def:
  source_module_bodies fuel ctx slots syntax =
    source_module_bind (source_module_collect
      (MAP (source_module_body fuel ctx slots) (source_module_declarations syntax)))
      (\tls. SM_Ok (FLAT tls))
End
