Theory bodyIntCallDefaultPinDispatchMods
Ancestors
  exprLowering exprLoweringEquations compileEnv vyperAST vyperTypeContract
  supportedExprTraverse whitelistCheckerConsts bodyIntCallPinSupportMods

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem runtime_default_builtin_expr_body_module_pin:
  runtime_constant_expr mods (Builtin ann bi args) /\
  ~supported_expr_exists ^bad_builtin_arity (Builtin ann bi args) /\
  ((runtime_constant_builtin bi \/ constant_builtin bi) /\
   builtin_args_length_ok bi (LENGTH args) /\
   EVERY (runtime_constant_expr mods) args /\
   ~supported_exprs_exists ^bad_builtin_arity args ==>
   bd (ce with ce_module := src) (expr_type (Builtin ann bi args)) ty bi args st =
   bd ce (expr_type (Builtin ann bi args)) ty bi args st) ==>
  compile_expr_body f bd td (ce with ce_module := src) ty (Builtin ann bi args) st =
  compile_expr_body f bd td ce ty (Builtin ann bi args) st
Proof
  strip_tac >>
  `EVERY (runtime_constant_expr mods) args` by
    (qpat_x_assum `runtime_constant_expr mods (Builtin _ _ _)` mp_tac >>
     simp[runtime_constant_expr_def, listTheory.EVERY_MEM] >>
     metis_tac[constant_expr_runtime_constant]) >>
  `!at a bt b mt m. args <> [Name at a; Name bt b; Name mt m]` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     fs[runtime_constant_expr_def]) >>
  `!at a bt b. args <> [Name at a; Name bt b]` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     fs[runtime_constant_expr_def]) >>
  `runtime_constant_builtin bi \/ constant_builtin bi` by
    fs[runtime_constant_expr_def] >>
  fs[compile_expr_body_builtin_default, supported_expr_exists_def, expr_type_def]
QED

Theorem runtime_default_type_builtin_expr_body_module_pin:
  runtime_constant_expr mods (TypeBuiltin ann tb rt args) /\
  ~supported_expr_exists ^bad_builtin_arity (TypeBuiltin ann tb rt args) /\
  (constant_type_builtin tb /\
   type_builtin_args_length_ok tb (LENGTH args) /\
   EVERY (runtime_constant_expr mods) args /\
   ~supported_exprs_exists ^bad_builtin_arity args ==>
   td (ce with ce_module := src) (expr_type (TypeBuiltin ann tb rt args)) ty tb rt args st =
   td ce (expr_type (TypeBuiltin ann tb rt args)) ty tb rt args st) ==>
  compile_expr_body f bd td (ce with ce_module := src) ty (TypeBuiltin ann tb rt args) st =
  compile_expr_body f bd td ce ty (TypeBuiltin ann tb rt args) st
Proof
  simp[runtime_constant_expr_def, supported_expr_exists_def,
       compile_expr_body_def, expr_type_def]
QED

Theorem runtime_default_type_builtin_body_module_pin:
  constant_type_builtin tb ==>
  compile_type_builtin_dispatch_body f (ce with ce_module := src) vt ty tb rt args st =
  compile_type_builtin_dispatch_body f ce vt ty tb rt args st
Proof
  Cases_on `tb` >> simp[constant_type_builtin_def] >>
  simp[compile_type_builtin_dispatch_body_def, type_memory_bytes_module_pin]
QED
