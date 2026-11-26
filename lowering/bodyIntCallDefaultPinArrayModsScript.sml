Theory bodyIntCallDefaultPinArrayMods
Ancestors
  bodyIntCallPinSupportMods exprLowering exprCallBounds vyperAST
  compileEnv vyperTypeContract vyperTypeSystem supportedExprTraverse list

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem pin_tuple_members[local]:
  !es tys buf off.
    (!e s. MEM e es ==>
      f (ce with ce_module := src) (expr_type e) e s = f ce (expr_type e) e s) ==>
    compile_make_tuple f (ce with ce_module := src) es tys buf off =
    compile_make_tuple f ce es tys buf off
Proof
  Induct >> simp[compile_make_tuple_def] >> gen_tac >> Cases >>
  simp[compile_make_tuple_def] >> rpt strip_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, LET_THM, FUN_EQ_THM,
       type_memory_bytes_module_pin, unwrap_value_module_pin,
       compile_store_memory_module_pin, lowered_value_type_module_pin]
QED

Theorem pin_array_members[local]:
  !es ety stride lw buf idx.
    (!e s. MEM e es ==>
      f (ce with ce_module := src) (expr_type e) e s = f ce (expr_type e) e s) ==>
    compile_make_array_elems f (ce with ce_module := src) es ety stride lw buf idx =
    compile_make_array_elems f ce es ety stride lw buf idx
Proof
  Induct >> simp[compile_make_array_elems_def] >> rpt strip_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, LET_THM, FUN_EQ_THM,
       unwrap_value_module_pin, compile_store_memory_module_pin,
       lowered_value_type_module_pin]
QED

Theorem runtime_default_make_array_body_module_pin:
  (runtime_constant_builtin (MakeArray elem bnd) \/ constant_builtin (MakeArray elem bnd)) /\
  builtin_args_length_ok (MakeArray elem bnd) (LENGTH args) /\
  EVERY (runtime_constant_expr mods) args /\
  ~supported_exprs_exists ^bad_builtin_arity args /\
  (!e ty s. expr_size e < list_size expr_size args /\
    runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
    f (ce with ce_module := src) ty e s = f ce ty e s) ==>
  compile_builtin_dispatch_body f (ce with ce_module := src) ret ty (MakeArray elem bnd) args st =
  compile_builtin_dispatch_body f ce ret ty (MakeArray elem bnd) args st
Proof
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `!e s. MEM e args ==>
    f (ce with ce_module := src) (expr_type e) e s = f ce (expr_type e) e s` by
    (rpt strip_tac >> qpat_assum `!e ty s. _ ==> f _ ty e s = _` irule >>
     simp[expr_list_member_bound] >>
     fs[EVERY_MEM, supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]) >>
  Cases_on `elem`
  >- (`type_memory_bytes (ce with ce_module := src) = type_memory_bytes ce` by
        simp[FUN_EQ_THM, type_memory_bytes_module_pin] >>
      `!tys buf off. compile_make_tuple f (ce with ce_module := src) args tys buf off =
                     compile_make_tuple f ce args tys buf off` by
        (rpt gen_tac >> irule pin_tuple_members >> simp[]) >>
      simp[compile_builtin_dispatch_body_def, LET_THM]) >>
  `!ety stride lw buf idx.
    compile_make_array_elems f (ce with ce_module := src) args ety stride lw buf idx =
    compile_make_array_elems f ce args ety stride lw buf idx` by
    (rpt gen_tac >> irule pin_array_members >> simp[]) >>
  simp[compile_builtin_dispatch_body_def, LET_THM, type_memory_bytes_module_pin,
       compile_make_array_def]
QED
