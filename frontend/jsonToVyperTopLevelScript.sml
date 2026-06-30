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
  translate_arg main_src_id (JArg name ty) = (name, translate_type main_src_id ty)
End


Definition translate_arg_ctx_def:
  translate_arg_ctx ctx (JArg name ty) = (name, translate_type_ctx ctx ty)
End

Definition translate_interface_func_def:
  translate_interface_func main_src_id (JInterfaceFunc name args ret_ty decs) =
    (name,
     MAP (translate_arg main_src_id) args,
     translate_type main_src_id ret_ty,
     translate_mutability decs) : interface_func
End

Definition translate_interface_func_ctx_def:
  translate_interface_func_ctx ctx (JInterfaceFunc name args ret_ty decs) =
    (name,
     MAP (translate_arg_ctx ctx) args,
     translate_type_ctx ctx ret_ty,
     translate_mutability decs) : interface_func
End


Definition translate_args_with_types_def:
  translate_args_with_types main_src_id args tys =
    case (args, tys) of
      ([], []) => []
    | (JArg name _ :: args', ty :: tys') =>
        (name, translate_type main_src_id ty) ::
        translate_args_with_types main_src_id args' tys'
    | _ => MAP (translate_arg main_src_id) args
End


Definition translate_args_with_types_ctx_def:
  translate_args_with_types_ctx all_import_maps ctx args tys =
    case (args, tys) of
      ([], []) => []
    | (JArg name ann :: args', ty :: tys') =>
        (name, translate_type_with_annotation all_import_maps ctx ty ann) ::
        translate_args_with_types_ctx all_import_maps ctx args' tys'
    | _ => MAP (translate_arg_ctx ctx) args
End

Definition translate_value_type_def:
  (translate_value_type main_src_id (JVT_Type ty) = Type (translate_type main_src_id ty)) /\
  (translate_value_type main_src_id (JVT_HashMap key_ty val_ty) =
    HashMapT (translate_type main_src_id key_ty) (translate_value_type main_src_id val_ty))
Termination
  WF_REL_TAC `measure (json_value_type_size o SND)` >> simp[]
End


Definition translate_value_type_ctx_def:
  (translate_value_type_ctx ctx (JVT_Type ty) = Type (translate_type_ctx ctx ty)) ∧
  (translate_value_type_ctx ctx (JVT_HashMap key_ty val_ty) =
    HashMapT (translate_type_ctx ctx key_ty) (translate_value_type_ctx ctx val_ty))
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


Definition translate_toplevel_def:
  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_FunctionDef name decs args defaults (JFuncType arg_tys ret_ty) ret_ann body) =
    SOME (FunctionDecl
      (translate_visibility decs)
      (translate_mutability decs)
      (MEM "nonreentrant" decs)
      (MEM "raw_return" decs)
      name
      (translate_args_with_types_ctx all_import_maps type_ctx args arg_tys)
      (MAP (translate_expr expr_ctx) defaults)
      (translate_type_with_annotation all_import_maps type_ctx ret_ty ret_ann)
      (MAP (translate_stmt expr_ctx) body))) /\

  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_VariableDecl name ty ann_ty is_public is_immutable is_transient const_val) =
    SOME (VariableDecl
      (if is_public then Public else Private)
      (translate_var_mutability expr_ctx is_immutable is_transient
        (case const_val of SOME _ => T | NONE => F) const_val)
      name
      (translate_type_with_annotation all_import_maps type_ctx ty ann_ty)
      NONE)) /\

  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_HashMapDecl name key_ty val_ty is_public is_transient) =
    SOME (HashMapDecl
      (if is_public then Public else Private)
      is_transient
      name
      (translate_type_ctx type_ctx key_ty)
      (translate_value_type_ctx type_ctx val_ty)
      NONE)) /\

  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_EventDef name args) =
    SOME (EventDecl name (MAP (λ(a,idx). (translate_arg_ctx type_ctx a, idx)) args))) /\

  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_StructDef name args) =
    SOME (StructDecl name (MAP (translate_arg_ctx type_ctx) args))) /\

  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_FlagDef name members) =
    SOME (FlagDecl name members)) /\

  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_InterfaceDef name funcs) =
    SOME (InterfaceDecl name (MAP (translate_interface_func_ctx type_ctx) funcs))) /\

  (* Module declarations are compiled away - the imported content is already inlined *)
  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_Import _) = NONE) /\
  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_ExportsDecl _) = NONE) /\
  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_InitializesDecl _) = NONE) /\
  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_UsesDecl _) = NONE) /\
  (translate_toplevel all_import_maps expr_ctx type_ctx (JTL_ImplementsDecl _) = NONE)
End


(* ===== Exports Extraction ===== *)

(* Build alias -> source_id map from import info list *)
