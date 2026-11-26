Theory bodyIntCallDefaultCompilePinAdapterMods
Ancestors
  exprLowering exprCallBounds compileEnv vyperTypeContract vyperContext
  supportedExprTraverse whitelistCheckerConsts

(* Use the same arity guard as runtime_default_compile_vars. *)
val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem runtime_default_compile_module_defaults_size:
  cenv_defaults_size (ce with ce_module := src) = cenv_defaults_size ce
Proof
  simp[cenv_defaults_size_def]
QED

(* The common bound is the expression or dispatcher-list measure plus the
   original defaults size. Equalities are only needed on guarded children. *)
Theorem runtime_default_compile_callback_module_pin:
  (!e ty st. expr_size e < (n:num) /\
     runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
     compile_expr (ce with ce_module := src) ty e st = compile_expr ce ty e st) /\
  (!bi args rt ty st. list_size expr_size args < n /\
     (runtime_constant_builtin bi \/ constant_builtin bi) /\
     builtin_args_length_ok bi (LENGTH args) /\ EVERY (runtime_constant_expr mods) args /\
     ~supported_exprs_exists ^bad_builtin_arity args ==>
     compile_builtin_dispatch (ce with ce_module := src) rt ty bi args st =
     compile_builtin_dispatch ce rt ty bi args st) /\
  (!tb args vt ty rt st. list_size expr_size args < n /\
     constant_type_builtin tb /\ type_builtin_args_length_ok tb (LENGTH args) /\
     EVERY (runtime_constant_expr mods) args /\ ~supported_exprs_exists ^bad_builtin_arity args ==>
     compile_type_builtin_dispatch (ce with ce_module := src) vt ty tb rt args st =
     compile_type_builtin_dispatch ce vt ty tb rt args st) ==>
  (!e ty st. expr_size e < n /\
     runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
     expr_child_callback (n + cenv_defaults_size ce) compile_expr
       (ce with ce_module := src) ty e st =
     expr_child_callback (n + cenv_defaults_size ce) compile_expr ce ty e st) /\
  (!bi args rt ty st. list_size expr_size args < n /\
     (runtime_constant_builtin bi \/ constant_builtin bi) /\
     builtin_args_length_ok bi (LENGTH args) /\ EVERY (runtime_constant_expr mods) args /\
     ~supported_exprs_exists ^bad_builtin_arity args ==>
     builtin_child_callback (n + cenv_defaults_size ce) compile_builtin_dispatch
       (ce with ce_module := src) rt ty bi args st =
     builtin_child_callback (n + cenv_defaults_size ce) compile_builtin_dispatch ce rt ty bi args st) /\
  (!tb args vt ty rt st. list_size expr_size args < n /\
     constant_type_builtin tb /\ type_builtin_args_length_ok tb (LENGTH args) /\
     EVERY (runtime_constant_expr mods) args /\ ~supported_exprs_exists ^bad_builtin_arity args ==>
     type_child_callback (n + cenv_defaults_size ce) compile_type_builtin_dispatch
       (ce with ce_module := src) vt ty tb rt args st =
     type_child_callback (n + cenv_defaults_size ce) compile_type_builtin_dispatch ce vt ty tb rt args st)
Proof
  rpt strip_tac >>
  simp[runtime_default_compile_module_defaults_size]
QED
