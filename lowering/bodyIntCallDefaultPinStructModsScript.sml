Theory bodyIntCallDefaultPinStructMods
Ancestors
  bodyIntCallPinSupportMods exprLowering exprCallBounds compileEnv
  vyperTypeContract vyperAST supportedExprTraverse context list pair

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem struct_fields_module_pin[local]:
  !fields buf off.
    (!name e st. MEM (name,e) fields ==>
      f (ce with ce_module := src) (expr_type e) e st = f ce (expr_type e) e st) ==>
    compile_struct_lit f (ce with ce_module := src) ty fields buf off =
    compile_struct_lit f ce ty fields buf off
Proof
  Induct >- simp[compile_struct_lit_def] >>
  Cases >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >>
  `!buf off. compile_struct_lit f (ce with ce_module := src) ty fields buf off =
             compile_struct_lit f ce ty fields buf off` by
    (rpt gen_tac >> qpat_assum `!buf off. _ ==> _` irule >> first_assum ACCEPT_TAC) >>
  simp[compile_struct_lit_def, lowered_value_type_module_pin,
       unwrap_value_module_pin, compile_store_memory_module_pin,
       comp_bind_def, comp_ignore_bind_def, FUN_EQ_THM]
QED

Theorem runtime_default_struct_body_module_pin:
  runtime_constant_expr mods (StructLit ann nsid fields) /\
  ~supported_expr_exists ^bad_builtin_arity (StructLit ann nsid fields) /\
  (!e ty st. expr_size e < expr_size (StructLit ann nsid fields) /\
    runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
    f (ce with ce_module := src) ty e st = f ce ty e st) ==>
  compile_expr_body f bd td (ce with ce_module := src) ty
    (StructLit ann nsid fields) st =
  compile_expr_body f bd td ce ty (StructLit ann nsid fields) st
Proof
  strip_tac >>
  `!buf off. compile_struct_lit f (ce with ce_module := src) (StructT nsid) fields buf off =
             compile_struct_lit f ce (StructT nsid) fields buf off` by
    (rpt gen_tac >> irule struct_fields_module_pin >> rpt strip_tac >>
     `expr_size e < expr_size (StructLit ann nsid fields)` by
       (irule expr_struct_field_bound >> metis_tac[]) >>
     first_x_assum irule >>
     gvs[runtime_constant_expr_def, supported_expr_exists_def,
         supported_fields_exists_every, EVERY_MEM, EXISTS_MEM, MEM_MAP] >>
     metis_tac[SND]) >>
  once_rewrite_tac[compile_expr_body_def] >> simp[LET_THM]
QED
