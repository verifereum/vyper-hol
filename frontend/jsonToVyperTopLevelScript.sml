Theory jsonToVyperTopLevel
Ancestors
  integer alist jsonAST vyperAST jsonToVyperType jsonToVyperExpr
Libs
  intLib

Definition translate_visibility_def:
  translate_visibility decs =
    if MEM "external" decs then External
    else if MEM "deploy" decs then Deploy
    else Internal
End


Definition translate_mutability_def:
  translate_mutability decs =
    if MEM "pure" decs then Pure
    else if MEM "view" decs then View
    else if MEM "payable" decs then Payable
    else Nonpayable
End


Definition translate_arg_def:
  translate_arg nominal_index all_import_maps ctx (JArg name ty ann) =
    (name, canonical_decl_type nominal_index all_import_maps ctx ty ann)
End

Definition translate_interface_func_def:
  translate_interface_func nominal_index all_import_maps ctx
      (JInterfaceFunc name args ret_ty decs) =
    (name,
     MAP (translate_arg nominal_index all_import_maps ctx) args,
     elaborate_annotation nominal_index all_import_maps ctx ret_ty,
     translate_mutability decs) : interface_func
End

Definition translate_args_with_types_def:
  translate_args_with_types nominal_index all_import_maps ctx args tys =
    case (args, tys) of
      ([], []) => []
    | (JArg name _ ann :: args', ty :: tys') =>
        (name, canonical_decl_type nominal_index all_import_maps ctx ty ann) ::
        translate_args_with_types nominal_index all_import_maps ctx args' tys'
    | _ => MAP (translate_arg nominal_index all_import_maps ctx) args
End

Definition translate_value_type_def:
  (translate_value_type ctx (JVT_Type ty) = Type (translate_type ctx ty)) ∧
  (translate_value_type ctx (JVT_HashMap key_ty val_ty) =
    HashMapT (translate_type ctx key_ty) (translate_value_type ctx val_ty))
Termination
  WF_REL_TAC `measure (json_value_type_size o SND)` >> simp[]
End

Definition translate_var_mutability_def:
  translate_var_mutability ctx is_immutable is_transient is_constant const_val =
    if is_immutable then Immutable
    else if is_transient then Transient
    else if is_constant then
      (case const_val of
         SOME e => Constant (translate_expr ctx e)
       | NONE => Storage)
    else Storage
End

Definition effective_decorators_def:
  effective_decorators nr_default decs =
    if nr_default ∧ MEM "external" decs ∧
       ¬MEM "nonreentrant" decs ∧ ¬MEM "reentrant" decs
    then decs ++ ["nonreentrant"]
    else decs
End

(* Vyper local declarations are function-scoped and cannot be shadowed. Build
   their canonical types before translating expression uses in the body. *)
Definition collect_local_types_def:
  collect_local_types nominal_index all_import_maps type_ctx [] = [] ∧
  collect_local_types nominal_index all_import_maps type_ctx
      (JS_AnnAssign name inferred ann _ :: rest) =
    (name, canonical_decl_type nominal_index all_import_maps type_ctx inferred ann) ::
    collect_local_types nominal_index all_import_maps type_ctx rest ∧
  collect_local_types nominal_index all_import_maps type_ctx
      (JS_For name inferred ann _ body :: rest) =
    (name, canonical_decl_type nominal_index all_import_maps type_ctx inferred ann) ::
    collect_local_types nominal_index all_import_maps type_ctx body ++
    collect_local_types nominal_index all_import_maps type_ctx rest ∧
  collect_local_types nominal_index all_import_maps type_ctx
      (JS_If _ body orelse :: rest) =
    collect_local_types nominal_index all_import_maps type_ctx body ++
    collect_local_types nominal_index all_import_maps type_ctx orelse ++
    collect_local_types nominal_index all_import_maps type_ctx rest ∧
  collect_local_types nominal_index all_import_maps type_ctx (_ :: rest) =
    collect_local_types nominal_index all_import_maps type_ctx rest
Termination
  WF_REL_TAC `measure (λ(_,_,_,stmts). list_size json_stmt_size stmts)` >> simp[]
End

Definition translate_toplevel_def:
  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_FunctionDef name decs args defaults (JFuncType arg_tys ret_ty) ret_ann body) =
    let decs = effective_decorators nr_default decs in
    let args' = translate_args_with_types nominal_index all_import_maps type_ctx args arg_tys in
    let local_types = args' ++
      collect_local_types nominal_index all_import_maps type_ctx body in
    let body_ctx = expr_with_local_types expr_ctx local_types in
    SOME (FunctionDecl
      (translate_visibility decs)
      (translate_mutability decs)
      (MEM "nonreentrant" decs)
      (MEM "raw_return" decs)
      name
      args'
      (MAP (translate_expr body_ctx) defaults)
      (canonical_decl_type nominal_index all_import_maps type_ctx ret_ty ret_ann)
      (MAP (translate_stmt body_ctx) body))) /\

  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_VariableDecl name ty ann_ty is_public is_immutable is_transient const_val) =
    SOME (VariableDecl
      (if is_public then Public else Private)
      (translate_var_mutability expr_ctx is_immutable is_transient
        (case const_val of SOME _ => T | NONE => F) const_val)
      name
      (canonical_decl_type nominal_index all_import_maps type_ctx ty ann_ty)
      NONE)) /\

  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_HashMapDecl name key_ty val_ty is_public is_transient) =
    SOME (HashMapDecl
      (if is_public then Public else Private)
      is_transient
      name
      (translate_type type_ctx key_ty)
      (translate_value_type type_ctx val_ty)
      NONE)) /\

  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_EventDef name args) =
    SOME (EventDecl name (MAP (λ(a,idx).
      (translate_arg nominal_index all_import_maps type_ctx a, idx)) args))) /\

  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_StructDef name args) =
    SOME (StructDecl name
      (MAP (translate_arg nominal_index all_import_maps type_ctx) args))) /\

  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_FlagDef name members) =
    SOME (FlagDecl name members)) /\

  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_InterfaceDef name funcs) =
    SOME (InterfaceDecl name
      (MAP (translate_interface_func nominal_index all_import_maps type_ctx) funcs))) /\

  (* Module declarations are compiled away - the imported content is already inlined *)
  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_Import _) = NONE) /\
  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_ExportsDecl _) = NONE) /\
  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_InitializesDecl _) = NONE) /\
  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_UsesDecl _) = NONE) /\
  (translate_toplevel nominal_index all_import_maps expr_ctx type_ctx nr_default (JTL_ImplementsDecl _) = NONE)
End


(* ===== Exports Extraction ===== *)

(* Build alias -> source_id map from import info list *)
