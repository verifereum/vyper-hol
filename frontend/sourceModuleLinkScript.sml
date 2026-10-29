Theory sourceModuleLink
Ancestors
  sourceModuleSignature sourceModuleEnv sourceModuleDefs sourceExprDefs sourceResolveModules
  sourceResolve sourceSyntax sourceConstAnnotation sourceConstAST sourceTypeDefs jsonToVyper jsonAST vyperAST alist list
Libs
  intLib

(* Structural linkage consumes ORIGINAL source, never an executable expression.
   Only the old syntax-only export index algorithms are reused. *)
Definition source_module_link_path_def:
  source_module_link_path (SX_Name n) = SOME (JE_Name n NONE JMissingSource JT_None) /\
  source_module_link_path (SX_Attribute e n) = OPTION_MAP
    (\b. JE_Attribute b n NONE NONE NONE JMissingSource JT_None)
    (source_module_link_path e) /\
  source_module_link_path _ = NONE
End

Definition source_module_export_annotation_def:
  source_module_export_annotation (SX_Tuple es) =
    OPTION_MAP JE_Tuple (OPT_MMAP source_module_link_path es) /\
  source_module_export_annotation e = source_module_link_path e
End

Definition source_module_import_map_def:
  source_module_import_map trust owner syntax = OPT_MMAP (\imp.
    case source_resolve_import_target owner imp of NONE => NONE | SOME key =>
      case ALOOKUP trust.smt_ids key of SOME (SOME sid) =>
        SOME (source_resolve_import_alias imp,sid) | _ => NONE)
    (source_resolve_imports syntax)
End

Definition source_module_public_def:
  source_module_public (SCA_Qualified q a) = (q = SCQ_Public \/ source_module_public a) /\
  source_module_public _ = F
End

Definition source_module_external_names_def:
  source_module_external_names (SourceModule ds) = FLAT (MAP (\d. case d of
    SD_Function name decs args defaults ret body =>
      if MEM (SX_Name "external") decs then [name] else []
  | SD_Variable name a init =>
      if source_module_public a then [name] else []
  | _ => []) ds)
End

Definition source_module_inline_interfaces_def:
  source_module_inline_interfaces (SourceModule ds) = FLAT (MAP (\d. case d of
    SD_Interface name fs => [(name,FLAT (MAP (\f. case f of
      SD_Function n decs args defs ret body => [n] | _ => []) fs))]
  | _ => []) ds)
End

Definition source_module_export_annotations_def:
  source_module_export_annotations (SourceModule ds) = OPT_MMAP
    source_module_export_annotation (FLAT (MAP (\d. case d of
      SD_Exports e => [e] | _ => []) ds))
End

Definition source_module_compact_index_def:
  source_module_compact_index trust (owner,syntax) =
    case (ALOOKUP trust.smt_ids owner,source_module_import_map trust owner syntax,
          source_module_export_annotations syntax) of
      (SOME src,SOME im,SOME anns) => SOME
        ((case src of NONE => 0 | SOME sid => sid),im,
         source_module_external_names syntax,source_module_inline_interfaces syntax,anns)
    | _ => NONE
End

(* Uses/initializes dependency substitutions are checked against the actual
   source module namespace. No missing dependency silently becomes main. *)
Definition source_module_module_ref_def:
  source_module_module_ref ctx e = case source_expr_path e of NONE => NONE | SOME p =>
    case source_resolve_name ctx.sm_scopes ctx.sm_table p of
      SOME (key,SR_Module) =>
        if key <> ctx.sm_owner /\ HD key <> "$builtin" then SOME key else NONE
    | _ => NONE
End

Definition source_module_dependency_def:
  source_module_dependency ctx parent (SX_NamedExpr (SX_Name alias) right) =
    (case source_resolve_alias (SUC (LENGTH ctx.sm_table)) ctx.sm_table (parent ++ [alias]) of
        SOME (key,SR_Module) => source_module_module_ref ctx right = SOME key
      | _ => F) /\
  source_module_dependency ctx parent _ = F
End

Definition source_module_initialize_def:
  source_module_initialize ctx (SX_Subscript base deps) =
    (case source_module_module_ref ctx base of NONE => F | SOME parent =>
      case deps of SX_Tuple es => EVERY (source_module_dependency ctx parent) es
      | _ => source_module_dependency ctx parent deps) /\
  source_module_initialize ctx e = IS_SOME (source_module_module_ref ctx e)
End

Definition source_module_uses_def:
  source_module_uses ctx (SX_Tuple es) = EVERY (\e.
    IS_SOME (source_module_module_ref ctx e)) es /\
  source_module_uses ctx e = IS_SOME (source_module_module_ref ctx e)
End

Definition source_module_export_shape_def:
  source_module_export_shape ctx (SX_Tuple es) =
    EVERY (source_module_export_shape ctx) es /\
  source_module_export_shape ctx (SX_Attribute base name) =
    IS_SOME (source_module_module_ref ctx base) /\
  source_module_export_shape ctx _ = F
Termination
  WF_REL_TAC `measure (source_expr_size o SND)` >> simp[] >>
  rpt strip_tac >> res_tac >> simp[]
End

Definition source_module_structural_decl_def:
  source_module_structural_decl ctx (SD_Exports e) = source_module_export_shape ctx e /\
  source_module_structural_decl ctx (SD_Initializes e) = source_module_initialize ctx e /\
  source_module_structural_decl ctx (SD_Uses e) = source_module_uses ctx e /\
  source_module_structural_decl ctx (SD_Implements e) =
    (case source_expr_path e of NONE => F | SOME p =>
      case source_resolve_name ctx.sm_scopes ctx.sm_table p of
        SOME (key,SR_Module) => T
      | SOME (key,SR_Type) => (case ALOOKUP ctx.sm_names key of
          SOME STI_Interface => T | _ => F)
      | _ => F) /\
  source_module_structural_decl ctx _ = T
End

(* Canonical default trees have separate name-identity constructors. Thus no
   user tuple/string can collide with an identity marker. Node templates retain
   operators, field names, keyword order and every original child. *)
Datatype:
  source_module_default = SMD_Atom source_expr
    | SMD_Module (string list) | SMD_Constant (string list)
    | SMD_Node source_expr (source_module_default list)
End

Definition source_module_default_def:
  source_module_default 0 ctx e = SMD_Atom e /\
  source_module_default (SUC fuel) ctx e =
    let recur = source_module_default fuel ctx in
    case e of
      SX_Name n => (case source_resolve_name ctx.sm_scopes ctx.sm_table [n] of
        SOME (key,SR_Module) => SMD_Module key
      | SOME (key,SR_Constant) => SMD_Constant key | _ => SMD_Atom e)
    | SX_Attribute b n => SMD_Node (SX_Attribute SX_Ellipsis n) [recur b]
    | SX_Subscript b i => SMD_Node (SX_Subscript SX_Ellipsis SX_Ellipsis) [recur b;recur i]
    | SX_Unary op b => SMD_Node (SX_Unary op SX_Ellipsis) [recur b]
    | SX_Binary op l r => SMD_Node (SX_Binary op SX_Ellipsis SX_Ellipsis) [recur l;recur r]
    | SX_Compare op l r => SMD_Node (SX_Compare op SX_Ellipsis SX_Ellipsis) [recur l;recur r]
    | SX_Boolean op es => SMD_Node (SX_Boolean op []) (MAP recur es)
    | SX_List es => SMD_Node (SX_List []) (MAP recur es)
    | SX_Tuple es => SMD_Node (SX_Tuple []) (MAP recur es)
    | SX_Dict es => SMD_Node (SX_Dict []) (FLAT (MAP (\(k,v). [recur k;recur v]) es))
    | SX_Call f args kws => SMD_Node (SX_Call SX_Ellipsis []
        (MAP (\(k,v). (k,SX_Ellipsis)) kws))
        (recur f :: MAP recur args ++ MAP (recur o SND) kws)
    | SX_ExtCall b => SMD_Node (SX_ExtCall SX_Ellipsis) [recur b]
    | SX_StaticCall b => SMD_Node (SX_StaticCall SX_Ellipsis) [recur b]
    | SX_IfExp c l r => SMD_Node (SX_IfExp SX_Ellipsis SX_Ellipsis SX_Ellipsis)
        [recur c;recur l;recur r]
    | SX_NamedExpr l r => SMD_Node (SX_NamedExpr SX_Ellipsis SX_Ellipsis) [recur l;recur r]
    | _ => SMD_Atom e
End

Definition source_module_default_override_def:
  source_module_default_override ctxa ctxb NONE b = T /\
  source_module_default_override ctxa ctxb (SOME a) NONE = F /\
  source_module_default_override ctxa ctxb (SOME SX_Ellipsis) (SOME b) = T /\
  source_module_default_override ctxa ctxb (SOME a) (SOME b) =
    (source_module_default (source_expr_size a + 1) ctxa a =
     source_module_default (source_expr_size b + 1) ctxb b)
End

(* The explicit linkage result is beside the unchanged source, not inferred
   from erased modules. Export expansion uses the existing structural consumer. *)
Definition source_module_indexes_sorted_def:
  source_module_indexes_sorted seen [] = T /\
  source_module_indexes_sorted seen ((sid,im,exts,inlines,anns)::rest) =
    (EVERY (\(_,dep). MEM dep seen) im /\
     source_module_indexes_sorted (sid::seen) rest)
End

Definition source_module_exports_ok_def:
  source_module_exports_ok trust registry exports = EVERY (\(name,sid).
    EXISTS (\(owner,syntax). ALOOKUP trust.smt_ids owner = SOME (SOME sid) /\
      MEM name (source_module_external_names syntax)) registry) exports
End

Definition source_module_link_def:
  source_module_link trust registry constants =
    if ~EVERY (\(owner,syntax). EVERY
       (source_module_structural_decl (source_module_context trust registry constants owner syntax))
       (source_module_declarations syntax)) registry then NONE else
    case OPT_MMAP (source_module_compact_index trust) registry of
      SOME (main::imports) =>
        if ~source_module_indexes_sorted [] imports then NONE else
        let maps = build_import_maps_from_indexes imports in
        let inlines = build_inline_maps_from_indexes imports in
        let exports = build_exports_map_from_indexes maps inlines [] imports in
        let result = extract_exports_with_indexes maps inlines exports main in
        if EVERY (\idx. source_module_exports_ok trust registry
             (compute_index_exports exports maps inlines idx)) imports /\
           source_module_exports_ok trust registry result then SOME result else NONE
    | _ => NONE
End

(* A declaration-only module can be called through its interface, never
   exported as an executable implementation. Nominal declarations stay intact. *)
Definition source_module_policy_link_ok_def:
  source_module_policy_link_ok trust policies exports =
    EVERY (\(key,p). source_module_declaration_only p ==>
      EVERY (\(name,sid). ALOOKUP trust.smt_ids key <> SOME (SOME sid)) exports) policies
End

Theorem source_module_default_not_folded:
  source_module_default 10 ctx
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2))) <>
  source_module_default 10 ctx (SX_Literal (SCL_Int 3))
Proof
  EVAL_TAC
QED

Theorem source_module_link_structural_equations:
  source_module_link trust registry constants = SOME exports ==>
  EVERY (\(owner,syntax). EVERY
    (source_module_structural_decl (source_module_context trust registry constants owner syntax))
    (source_module_declarations syntax)) registry
Proof
  simp[source_module_link_def, combinTheory.o_DEF] >>
  rpt (CASE_TAC >> simp[combinTheory.o_DEF]) >> strip_tac >>
  fs[combinTheory.o_DEF, EVERY_MEM]
QED
