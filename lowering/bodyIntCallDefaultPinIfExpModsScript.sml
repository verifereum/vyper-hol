Theory bodyIntCallDefaultPinIfExpMods
Ancestors
  bodyIntCallPinSupportMods exprCallBounds vyperTypeContract
  supportedExprTraverse vyperTypeSystem exprLowering compileEnv

(* Match the arity guard used by runtime_default_compile_vars. *)
val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem runtime_default_ifexp_body_module_pin:
  !mods ce src f bd td ann c a b ty st.
    runtime_constant_expr mods (IfExp ann c a b) /\
    ~supported_expr_exists ^bad_builtin_arity (IfExp ann c a b) /\
    (!e ty s. expr_size e < expr_size (IfExp ann c a b) /\
              runtime_constant_expr mods e /\
              ~supported_expr_exists ^bad_builtin_arity e ==>
      f (ce with ce_module := src) ty e s = f ce ty e s) ==>
    compile_expr_body f bd td (ce with ce_module := src) ty (IfExp ann c a b) st =
    compile_expr_body f bd td ce ty (IfExp ann c a b) st
Proof
  rpt gen_tac >> strip_tac >>
  fs[runtime_constant_expr_def, supported_expr_exists_def] >>
  `(!ty s. f (ce with ce_module := src) ty c s = f ce ty c s) /\
   (!ty s. f (ce with ce_module := src) ty a s = f ce ty a s) /\
   (!ty s. f (ce with ce_module := src) ty b s = f ce ty b s)` by
    (rpt conj_tac >> rpt gen_tac >> first_x_assum irule >>
     simp[expr_ifexp_child_bounds]) >>
  simp[compile_expr_body_def, lower_value_def, comp_bind_def,
       unwrap_value_module_pin, lowered_value_type_module_pin,
       compile_ifexp_arm_module_pin]
QED
