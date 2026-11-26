Theory bodyIntCallDefaultPinBopMods
Ancestors
  bodyIntCallPinSupportMods bodyIntCallPinActionsMods
  runtimeDefaultCompile whitelistCheckerConsts
  exprLowering exprLoweringProps exprCallBounds compileEnv vyperContext vyperTypeContract
  supportedExprTraverse vyperAST list pair

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem runtime_default_bop_body_module_pin:
  (runtime_constant_builtin (Bop op) \/ constant_builtin (Bop op)) /\
  builtin_args_length_ok (Bop op) (LENGTH args) /\
  EVERY (runtime_constant_expr mods) args /\
  ~supported_exprs_exists ^bad_builtin_arity args /\
  (!e ty st. expr_size e < list_size expr_size args /\
    runtime_constant_expr mods e /\
    ~supported_expr_exists ^bad_builtin_arity e ==>
    f (ce with ce_module := src) ty e st = f ce ty e st) ==>
  compile_builtin_dispatch_body f (ce with ce_module := src) ret ty (Bop op) args st =
  compile_builtin_dispatch_body f ce ret ty (Bop op) args st
Proof
  strip_tac >>
  `!e. MEM e args ==> runtime_constant_expr mods e /\
                      ~supported_expr_exists ^bad_builtin_arity e` by
    (fs[EVERY_MEM, supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
  `!e ty. MEM e args ==>
     f (ce with ce_module := src) ty e = f ce ty e` by
    (simp[FUN_EQ_THM] >> rpt strip_tac >>
     qpat_assum `!e ty st. expr_size e < _ /\ _ ==> _` irule >>
     simp[expr_list_member_bound]) >>
  `!e ty. MEM e args ==>
     lower_value f (ce with ce_module := src) ty e = lower_value f ce ty e` by
    (rpt strip_tac >> irule lower_value_module_pin_cong >> simp[unwrap_value_module_pin]) >>
  `!ann t n elems. MEM (Builtin ann (MakeArray t n) elems) args ==>
     compile_multi_exprs f (ce with ce_module := src) elems = compile_multi_exprs f ce elems` by
    (rpt strip_tac >> irule compile_multi_exprs_module_pin_cong >>
     simp[unwrap_value_module_pin, FUN_EQ_THM] >> rpt strip_tac >>
     qpat_assum `!e ty st. expr_size e < _ /\ _ ==> _` irule >>
     `expr_size (Builtin ann (MakeArray t n) elems) < list_size expr_size args` by
       simp[expr_list_member_bound] >>
     `expr_size e < list_size expr_size elems` by simp[expr_list_member_bound] >>
     `expr_size e < list_size expr_size args` by (fs[expr_size_def] >> decide_tac) >>
     `runtime_constant_expr mods (Builtin ann (MakeArray t n) elems) /\
      ~supported_expr_exists ^bad_builtin_arity (Builtin ann (MakeArray t n) elems)` by simp[] >>
     fs[runtime_constant_expr_def, runtime_constant_builtin_def, constant_builtin_def,
        supported_expr_exists_def, supported_exprs_exists_every, EVERY_MEM, EXISTS_MEM] >>
     metis_tac[constant_expr_runtime_constant]) >>
  `!loc t. elem_size_in_location (ce with ce_module := src) loc t =
     elem_size_in_location ce loc t` by
    simp[elem_size_in_location_def, type_memory_bytes_module_pin] >>
  `!v vv t d. compile_var_array_membership (ce with ce_module := src) v vv t d =
     compile_var_array_membership ce v vv t d` by
    simp[compile_var_array_membership_def] >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  rename1 `compile_builtin_dispatch_body f _ _ _ (Bop op) [lhs;rhs] st = _` >>
  Cases_on `(op = In \/ op = NotIn) /\ is_ArrayT (expr_type rhs)` >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `rhs` >> simp[] >>
  rename1 `Builtin _ bi elems` >>
  Cases_on `?t n. bi = MakeArray t n`
  >- gvs[] >>
  Cases_on `bi` >> simp[] >> fs[]
QED
