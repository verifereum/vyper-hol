Theory bodyIntCallDefaultPinSelectorsMods
Ancestors
  bodyIntCallPinSupportMods exprLowering exprCallBounds compileEnv
  vyperAST vyperContext vyperTypeContract supportedExprTraverse list

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem compile_invert_module_pin[local]:
  compile_invert v ty (ce with ce_module := src) = compile_invert v ty ce
Proof
  Cases_on `ty` >> simp[compile_invert_def]
QED

Theorem compile_acc_selector_pin[local]:
  lower_value f (ce with ce_module := src) (BaseT AddressT) e =
    lower_value f ce (BaseT AddressT) e ==>
  compile_acc f (ce with ce_module := src) e item = compile_acc f ce e item
Proof
  Cases_on `item` >> simp[compile_acc_def, FUN_EQ_THM, LET_THM]
QED

Theorem runtime_default_selector_body_module_pin:
  (runtime_constant_builtin bi \/ constant_builtin bi) /\
  builtin_args_length_ok bi (LENGTH args) /\
  EVERY (runtime_constant_expr mods) args /\
  ~supported_exprs_exists ^bad_builtin_arity args /\
  (!e ty st. expr_size e < list_size expr_size args /\
    runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
    f (ce with ce_module := src) ty e st = f ce ty e st) /\
  (!op. bi <> Bop op) /\ (!elem bnd. bi <> MakeArray elem bnd) /\
  (!d n. bi <> BoolChain d n) ==>
  compile_builtin_dispatch_body f (ce with ce_module := src) ret ty bi args st =
    compile_builtin_dispatch_body f ce ret ty bi args st
Proof
  strip_tac >>
  `EVERY (\e. !ty st. f (ce with ce_module := src) ty e st = f ce ty e st)
    args` by
    (simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
     fs[EVERY_MEM, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[expr_list_member_bound]) >>
  `EVERY (\e. !ty. lower_value f (ce with ce_module := src) ty e =
                   lower_value f ce ty e) args` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     simp[lower_value_def, comp_bind_def, FUN_EQ_THM, unwrap_value_module_pin]) >>
  Cases_on `bi` >> fs[runtime_constant_builtin_def, constant_builtin_def] >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute]
  >~ [`compile_builtin_dispatch_body _ _ _ _ NamedConst _ _`] >-
    simp[compile_builtin_dispatch_body_def, LET_THM]
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Acc _) _ _`] >-
    simp[compile_builtin_dispatch_body_def, LET_THM, compile_acc_selector_pin]
  >~ [`compile_builtin_dispatch_body _ _ _ _ Len _ _`] >-
    simp[compile_builtin_dispatch_body_def, LET_THM] >>
  simp[compile_builtin_dispatch_body_def, LET_THM, compile_invert_module_pin,
       type_memory_bytes_module_pin]
QED
