Theory bodyIntCallDefaultPinBoolChainMods
Ancestors
  bodyIntCallPinSupportMods compileEnv exprLowering exprCallBounds vyperContext
  vyperTypeContract supportedExprTraverse list boolChainOpsCong
  runtimeConstBoolChainOperands ctorCallFreeBoolChain boolChainOperandsSupported

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem runtime_default_bool_chain_body_module_pin:
  (runtime_constant_builtin (BoolChain d n) \/ constant_builtin (BoolChain d n)) /\
  builtin_args_length_ok (BoolChain d n) (LENGTH args) /\
  EVERY (runtime_constant_expr mods) args /\
  ~supported_exprs_exists ^bad_builtin_arity args /\
  (!e t s. expr_size e < list_size expr_size args /\
           runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
           f (ce with ce_module := src) t e s = f ce t e s) ==>
  compile_builtin_dispatch_body f (ce with ce_module := src) ret ty (BoolChain d n) args st =
  compile_builtin_dispatch_body f ce ret ty (BoolChain d n) args st
Proof
  (* Both whitelist alternatives have the same BoolChain compiler action. *)
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC) strip_assume_tac) >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  rename1 `compile_builtin_dispatch_body _ _ _ _ (BoolChain d n) [arg] _ = _` >>
  `~supported_expr_exists ^bad_builtin_arity arg` by
    fs[supported_exprs_exists_every] >>
  `EVERY (runtime_constant_expr mods) (bool_chain_operands d (n - 1) arg)` by
    simp[runtime_constant_bool_chain_operands] >>
  `EVERY (\e. ~supported_expr_exists ^bad_builtin_arity e)
         (bool_chain_operands d (n - 1) arg)` by
    simp[bool_chain_operands_supported] >>
  `expr_size arg < list_size expr_size [arg]` by simp[expr_list_member_bound] >>
  `!r lbl. compile_bool_chain_ops f (ce with ce_module := src) d r lbl
             (bool_chain_operands d (n - 1) arg) =
           compile_bool_chain_ops f ce d r lbl (bool_chain_operands d (n - 1) arg)` by
    (rpt gen_tac >> irule compile_bool_chain_ops_lower_value_cong >>
     qx_gen_tac `e` >> strip_tac >>
     drule bool_chain_operand_size >> strip_tac >>
     `expr_size e < list_size expr_size [arg]` by decide_tac >>
     `runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e` by
       fs[EVERY_MEM] >>
     `!t s. f (ce with ce_module := src) t e s = f ce t e s` by
       (rpt gen_tac >> first_x_assum irule >> simp[]) >>
     simp[lower_value_def, comp_bind_def, FUN_EQ_THM, unwrap_value_module_pin]) >>
  simp[compile_builtin_dispatch_body_def, LET_THM]
QED
