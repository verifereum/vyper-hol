Theory jsonNominalSources
Ancestors
  list jsonAST jsonToVyperType

(* Vyper's annotated AST names a struct or flag type by its bare name, with no
   declaring source ID ({"name": "S", "typeclass": "struct"}), wherever the
   compiler infers the type: storage and HashMap value types, expressions,
   `empty(...)`, call results.  Translating such a type in the module being
   translated gives a struct declared in an imported module or interface, used
   as `I.S`, a second identity besides the one its qualified annotation gives.

   This pass gives every such inferred type the source ID of its declaration
   when exactly one module of the program declares a struct (or flag) of that
   name.  A name declared in several modules is left without a source, as the
   compiler emitted it. *)

Definition json_nominal_decls_def:
  json_nominal_decls (src_id : int) [] = [] ∧
  json_nominal_decls src_id (JTL_StructDef name _ :: rest) =
    ((StructKind, name), src_id) :: json_nominal_decls src_id rest ∧
  json_nominal_decls src_id (JTL_FlagDef name _ :: rest) =
    ((FlagKind, name), src_id) :: json_nominal_decls src_id rest ∧
  json_nominal_decls src_id (_ :: rest) = json_nominal_decls src_id rest
End

Definition json_imported_nominal_decls_def:
  json_imported_nominal_decls [] = [] ∧
  json_imported_nominal_decls (JImportedModule src_id _ _ _ body :: rest) =
    json_nominal_decls src_id body ++ json_imported_nominal_decls rest
End

Definition nominal_source_def:
  nominal_source decls key =
    case nub (MAP SND (FILTER (λ(k,_). k = key) decls)) of
    | [src_id] => SOME src_id
    | _ => NONE
End

Definition resolve_json_type_def:
  (resolve_json_type decls (JT_Struct NONE name) =
    JT_Struct (nominal_source decls (StructKind, name)) name) ∧
  (resolve_json_type decls (JT_Flag NONE name) =
    JT_Flag (nominal_source decls (FlagKind, name)) name) ∧
  (resolve_json_type decls (JT_StaticArray ty n) =
    JT_StaticArray (resolve_json_type decls ty) n) ∧
  (resolve_json_type decls (JT_DynArray ty n) =
    JT_DynArray (resolve_json_type decls ty) n) ∧
  (resolve_json_type decls (JT_Tuple tys) =
    JT_Tuple (resolve_json_types decls tys)) ∧
  (resolve_json_type decls (JT_HashMap kt vt) =
    JT_HashMap (resolve_json_type decls kt) (resolve_json_type decls vt)) ∧
  (resolve_json_type decls ty = ty) ∧
  (resolve_json_types decls [] = []) ∧
  (resolve_json_types decls (ty :: tys) =
    resolve_json_type decls ty :: resolve_json_types decls tys)
End

Definition resolve_json_expr_def:
  (resolve_json_expr decls (JE_Int n ty) =
    JE_Int n (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_Hex h ty) =
    JE_Hex h (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_Name id tc src ty) =
    JE_Name id tc src (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_Folded e folded) =
    JE_Folded (resolve_json_expr decls e) (resolve_json_expr decls folded)) ∧
  (resolve_json_expr decls (JE_Attribute e attr tc btn btc src ty) =
    JE_Attribute (resolve_json_expr decls e) attr tc btn btc src
      (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_Subscript e idx ty) =
    JE_Subscript (resolve_json_expr decls e) (resolve_json_expr decls idx)
      (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_NamedExpr lhs rhs) =
    JE_NamedExpr (resolve_json_expr decls lhs) (resolve_json_expr decls rhs)) ∧
  (resolve_json_expr decls (JE_BinOp l op r ty) =
    JE_BinOp (resolve_json_expr decls l) op (resolve_json_expr decls r)
      (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_Compare l op r) =
    JE_Compare (resolve_json_expr decls l) op (resolve_json_expr decls r)) ∧
  (resolve_json_expr decls (JE_BoolOp op es) =
    JE_BoolOp op (resolve_json_exprs decls es)) ∧
  (resolve_json_expr decls (JE_UnaryOp op e ty) =
    JE_UnaryOp op (resolve_json_expr decls e) (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_IfExp test yes no ty) =
    JE_IfExp (resolve_json_expr decls test) (resolve_json_expr decls yes)
      (resolve_json_expr decls no) (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_Tuple es) =
    JE_Tuple (resolve_json_exprs decls es)) ∧
  (resolve_json_expr decls (JE_List es ty) =
    JE_List (resolve_json_exprs decls es) (resolve_json_type decls ty)) ∧
  (resolve_json_expr decls (JE_Call func args kws ty src) =
    JE_Call (resolve_json_expr decls func) (resolve_json_exprs decls args)
      (resolve_json_keywords decls kws) (resolve_json_type decls ty) src) ∧
  (resolve_json_expr decls (JE_ExtCall name src tys ret target args kws) =
    JE_ExtCall name src (resolve_json_types decls tys)
      (resolve_json_type decls ret) (resolve_json_expr decls target)
      (resolve_json_exprs decls args) (resolve_json_keywords decls kws)) ∧
  (resolve_json_expr decls (JE_StaticCall name src tys ret target args kws) =
    JE_StaticCall name src (resolve_json_types decls tys)
      (resolve_json_type decls ret) (resolve_json_expr decls target)
      (resolve_json_exprs decls args) (resolve_json_keywords decls kws)) ∧
  (resolve_json_expr decls e = e) ∧
  (resolve_json_exprs decls [] = []) ∧
  (resolve_json_exprs decls (e :: es) =
    resolve_json_expr decls e :: resolve_json_exprs decls es) ∧
  (resolve_json_keywords decls [] = []) ∧
  (resolve_json_keywords decls (JKeyword k e :: kws) =
    JKeyword k (resolve_json_expr decls e) :: resolve_json_keywords decls kws)
End

Definition resolve_json_expr_opt_def:
  resolve_json_expr_opt decls NONE = NONE ∧
  resolve_json_expr_opt decls (SOME e) = SOME (resolve_json_expr decls e)
End

Definition resolve_json_base_target_def:
  (resolve_json_base_target decls (JBT_Subscript bt idx) =
    JBT_Subscript (resolve_json_base_target decls bt)
      (resolve_json_expr decls idx)) ∧
  (resolve_json_base_target decls (JBT_Attribute bt attr) =
    JBT_Attribute (resolve_json_base_target decls bt) attr) ∧
  (resolve_json_base_target decls bt = bt)
End

Definition resolve_json_target_def:
  (resolve_json_target decls (JTgt_Base bt) =
    JTgt_Base (resolve_json_base_target decls bt)) ∧
  (resolve_json_target decls (JTgt_Tuple ts) =
    JTgt_Tuple (resolve_json_targets decls ts)) ∧
  (resolve_json_targets decls [] = []) ∧
  (resolve_json_targets decls (t :: ts) =
    resolve_json_target decls t :: resolve_json_targets decls ts)
End

Definition resolve_json_iter_def:
  (resolve_json_iter decls (JIter_Range args folded bound) =
    JIter_Range (resolve_json_exprs decls args) folded bound) ∧
  (resolve_json_iter decls (JIter_Array e ty) =
    JIter_Array (resolve_json_expr decls e) (resolve_json_type decls ty))
End

Definition resolve_json_stmt_def:
  (resolve_json_stmt decls (JS_Expr e) = JS_Expr (resolve_json_expr decls e)) ∧
  (resolve_json_stmt decls (JS_Return e) =
    JS_Return (resolve_json_expr_opt decls e)) ∧
  (resolve_json_stmt decls (JS_Raise e) =
    JS_Raise (resolve_json_expr_opt decls e)) ∧
  (resolve_json_stmt decls (JS_Assert test msg) =
    JS_Assert (resolve_json_expr decls test) (resolve_json_expr_opt decls msg)) ∧
  (resolve_json_stmt decls (JS_Log event args) =
    JS_Log event (resolve_json_exprs decls args)) ∧
  (resolve_json_stmt decls (JS_If test body orelse) =
    JS_If (resolve_json_expr decls test) (resolve_json_stmts decls body)
      (resolve_json_stmts decls orelse)) ∧
  (resolve_json_stmt decls (JS_For var ty ann iter body) =
    JS_For var (resolve_json_type decls ty) ann (resolve_json_iter decls iter)
      (resolve_json_stmts decls body)) ∧
  (resolve_json_stmt decls (JS_Assign tgt e) =
    JS_Assign (resolve_json_target decls tgt) (resolve_json_expr decls e)) ∧
  (resolve_json_stmt decls (JS_AnnAssign var ty ann e) =
    JS_AnnAssign var (resolve_json_type decls ty) ann
      (resolve_json_expr decls e)) ∧
  (resolve_json_stmt decls (JS_AugAssign bt op e) =
    JS_AugAssign (resolve_json_base_target decls bt) op
      (resolve_json_expr decls e)) ∧
  (resolve_json_stmt decls (JS_Append bt e) =
    JS_Append (resolve_json_base_target decls bt) (resolve_json_expr decls e)) ∧
  (resolve_json_stmt decls s = s) ∧
  (resolve_json_stmts decls [] = []) ∧
  (resolve_json_stmts decls (s :: ss) =
    resolve_json_stmt decls s :: resolve_json_stmts decls ss)
End

Definition resolve_json_arg_def:
  resolve_json_arg decls (JArg name ty ann) =
    JArg name (resolve_json_type decls ty) ann
End

Definition resolve_json_value_type_def:
  (resolve_json_value_type decls (JVT_Type ty) =
    JVT_Type (resolve_json_type decls ty)) ∧
  (resolve_json_value_type decls (JVT_HashMap kt vt) =
    JVT_HashMap (resolve_json_type decls kt) (resolve_json_value_type decls vt))
End

Definition resolve_json_interface_func_def:
  resolve_json_interface_func decls (JInterfaceFunc name args ret decs) =
    JInterfaceFunc name (MAP (resolve_json_arg decls) args) ret decs
End

Definition resolve_json_toplevel_def:
  (resolve_json_toplevel decls
      (JTL_FunctionDef name decs aliases args defaults
        (JFuncType arg_tys ret_ty) ret_ann body) =
    JTL_FunctionDef name decs aliases (MAP (resolve_json_arg decls) args)
      (resolve_json_exprs decls defaults)
      (JFuncType (resolve_json_types decls arg_tys)
        (resolve_json_type decls ret_ty))
      ret_ann (resolve_json_stmts decls body)) ∧
  (resolve_json_toplevel decls
      (JTL_VariableDecl name ty ann is_public is_immutable is_transient value) =
    JTL_VariableDecl name (resolve_json_type decls ty) ann is_public
      is_immutable is_transient (resolve_json_expr_opt decls value)) ∧
  (resolve_json_toplevel decls
      (JTL_HashMapDecl name kt vt is_public is_transient) =
    JTL_HashMapDecl name (resolve_json_type decls kt)
      (resolve_json_value_type decls vt) is_public is_transient) ∧
  (resolve_json_toplevel decls (JTL_EventDef name fields) =
    JTL_EventDef name
      (MAP (λ(arg, indexed). (resolve_json_arg decls arg, indexed)) fields)) ∧
  (resolve_json_toplevel decls (JTL_StructDef name fields) =
    JTL_StructDef name (MAP (resolve_json_arg decls) fields)) ∧
  (resolve_json_toplevel decls (JTL_InterfaceDef name funcs) =
    JTL_InterfaceDef name (MAP (resolve_json_interface_func decls) funcs)) ∧
  (resolve_json_toplevel decls top = top)
End

Definition resolve_json_imported_module_def:
  resolve_json_imported_module decls
      (JImportedModule src_id path resolved_path nr_default body) =
    JImportedModule src_id path resolved_path nr_default
      (MAP (resolve_json_toplevel decls) body)
End

Definition resolve_nominal_sources_def:
  resolve_nominal_sources
      (JAnnotatedAST (JModule main_src_id nr_default body) imports) =
    let decls = json_nominal_decls main_src_id body ++
                json_imported_nominal_decls imports in
    JAnnotatedAST
      (JModule main_src_id nr_default (MAP (resolve_json_toplevel decls) body))
      (MAP (resolve_json_imported_module decls) imports)
End
