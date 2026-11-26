Theory bodyIntCallDefaultCompilePinMods
Ancestors
  runtimeDefaultCompile bodyIntCallPinSupportMods bodyIntCallPinActionsMods
  bodyIntCallPinBodiesMods bodyIntCallPinCallsMods
  bodyIntCallDefaultPinIfExpMods bodyIntCallDefaultPinStructMods
  bodyIntCallDefaultPinPlacesMods bodyIntCallDefaultPinDispatchMods
  bodyIntCallDefaultPinBopMods bodyIntCallDefaultPinBoolChainMods
  bodyIntCallDefaultPinArrayMods bodyIntCallDefaultPinSelectorsMods
  bodyIntCallDefaultCompilePinAdapterMods
  exprLowering exprLoweringProps exprCallBounds vyperTypeContract
  compileEnv context pair list

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem runtime_default_compile_module_mods[local]:
  (!ce ty e st. runtime_constant_expr mods e /\
    ~supported_expr_exists ^bad_builtin_arity e ==>
    compile_expr (ce with ce_module := src) ty e st =
      compile_expr ce ty e st) /\
  (!ce rt ty bi args st.
    (runtime_constant_builtin bi \/ constant_builtin bi) /\
    builtin_args_length_ok bi (LENGTH args) /\
    EVERY (runtime_constant_expr mods) args /\
    ~supported_exprs_exists ^bad_builtin_arity args ==>
    compile_builtin_dispatch (ce with ce_module := src)
      rt ty bi args st = compile_builtin_dispatch ce rt ty bi args st) /\
  (!ce vt ty tb rt args st.
    constant_type_builtin tb /\
    type_builtin_args_length_ok tb (LENGTH args) /\
    EVERY (runtime_constant_expr mods) args /\
    ~supported_exprs_exists ^bad_builtin_arity args ==>
    compile_type_builtin_dispatch
      (ce with ce_module := src) vt ty tb rt args st =
      compile_type_builtin_dispatch ce vt ty tb rt args st)
Proof
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >> rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp_tac bool_ss [ETA_AX, runtime_default_compile_module_defaults_size] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
  >~ [`compile_expr_body`] >-
    (mp_tac (Q.INST [`n` |-> `expr_size e`] runtime_default_compile_callback_module_pin) >>
     impl_tac >-
       (rpt conj_tac >> rpt strip_tac >> first_assum irule >> fs[]) >>
     strip_tac >> Cases_on `e`
     >~ [`compile_expr_body _ _ _ _ _ (TopLevelName _ _) _`] >-
       (once_rewrite_tac[compile_expr_body_def] >> simp[vyperASTTheory.expr_type_def])
     >~ [`compile_expr_body _ _ _ _ _ (Literal _ _) _`] >-
       (once_rewrite_tac[compile_expr_body_def] >> simp[vyperASTTheory.expr_type_def])
     >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >-
       (irule runtime_default_ifexp_body_module_pin >> asm_rewrite_tac[ETA_AX] >> qexists_tac `mods` >>
        asm_rewrite_tac[])
     >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _`] >-
       (irule runtime_default_struct_body_module_pin >> asm_rewrite_tac[ETA_AX] >> qexists_tac `mods` >>
        asm_rewrite_tac[])
     >~ [`compile_expr_body _ _ _ _ _ (Subscript _ _ _) _`] >-
       (irule runtime_default_subscript_body_module_pin >> asm_rewrite_tac[ETA_AX] >> qexists_tac `mods` >>
        asm_rewrite_tac[])
     >~ [`compile_expr_body _ _ _ _ _ (Attribute _ _ _) _`] >-
       (irule runtime_default_attribute_body_module_pin >> asm_rewrite_tac[ETA_AX] >> qexists_tac `mods` >>
        asm_rewrite_tac[])
     >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >-
       (irule runtime_default_builtin_expr_body_module_pin >> asm_rewrite_tac[ETA_AX] >> qexists_tac `mods` >>
        asm_rewrite_tac[] >> rpt strip_tac >> first_assum irule >>
        simp[vyperASTTheory.expr_size_def])
     >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _`] >-
       (irule runtime_default_type_builtin_expr_body_module_pin >> asm_rewrite_tac[ETA_AX] >> qexists_tac `mods` >>
        asm_rewrite_tac[] >> rpt strip_tac >> first_assum irule >>
        simp[vyperASTTheory.expr_size_def])
     >> fs[runtime_constant_expr_def])
  >~ [`compile_builtin_dispatch_body`] >-
    (`!e ty st. expr_size e < list_size expr_size args /\
        runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
        expr_child_callback (list_size expr_size args + cenv_defaults_size ce) compile_expr
          (ce with ce_module := src) ty e st =
        expr_child_callback (list_size expr_size args + cenv_defaults_size ce) compile_expr
          ce ty e st` by
       (rpt strip_tac >>
        dep_rewrite.DEP_REWRITE_TAC[expr_child_callback_valid] >>
        simp[runtime_default_compile_module_defaults_size] >>
        first_assum irule >> simp[]) >>
     Cases_on `?op. bi = Bop op` >-
       (gvs[Excl "expr_child_callback_def"] >>
        irule runtime_default_bop_body_module_pin >> simp[Excl "expr_child_callback_def"] >>
        qexists_tac `mods` >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
        fs[arithmeticTheory.ADD_COMM, Excl "expr_child_callback_def"])
     >> Cases_on `?d n. bi = BoolChain d n` >-
       (gvs[Excl "expr_child_callback_def"] >>
        irule runtime_default_bool_chain_body_module_pin >> simp[Excl "expr_child_callback_def"] >>
        qexists_tac `mods` >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
        fs[arithmeticTheory.ADD_COMM, Excl "expr_child_callback_def"])
     >> Cases_on `?elem bnd. bi = MakeArray elem bnd` >-
       (gvs[Excl "expr_child_callback_def"] >>
        irule runtime_default_make_array_body_module_pin >> simp[Excl "expr_child_callback_def"] >>
        qexists_tac `mods` >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
        fs[arithmeticTheory.ADD_COMM, Excl "expr_child_callback_def"])
     >> irule runtime_default_selector_body_module_pin >>
        fs[Excl "expr_child_callback_def"] >> qexists_tac `mods` >>
        CONV_TAC (DEPTH_CONV ETA_CONV) >>
        fs[arithmeticTheory.ADD_COMM, Excl "expr_child_callback_def"])
  >> irule runtime_default_type_builtin_body_module_pin >> simp[]
QED

Theorem runtime_default_compile_vars_module_mods:
  (!ce ty e st. runtime_constant_expr mods e /\
    ~supported_expr_exists ^bad_builtin_arity e ==>
    compile_expr (ce with <|ce_vars := vars; ce_module := src|>) ty e st =
      compile_expr ce ty e st) /\
  (!ce rt ty bi args st.
    (runtime_constant_builtin bi \/ constant_builtin bi) /\
    builtin_args_length_ok bi (LENGTH args) /\
    EVERY (runtime_constant_expr mods) args /\
    ~supported_exprs_exists ^bad_builtin_arity args ==>
    compile_builtin_dispatch (ce with <|ce_vars := vars; ce_module := src|>)
      rt ty bi args st = compile_builtin_dispatch ce rt ty bi args st) /\
  (!ce vt ty tb rt args st.
    constant_type_builtin tb /\
    type_builtin_args_length_ok tb (LENGTH args) /\
    EVERY (runtime_constant_expr mods) args /\
    ~supported_exprs_exists ^bad_builtin_arity args ==>
    compile_type_builtin_dispatch
      (ce with <|ce_vars := vars; ce_module := src|>) vt ty tb rt args st =
      compile_type_builtin_dispatch ce vt ty tb rt args st)
Proof
  rpt conj_tac >> rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS)
  >- (Q_TAC (TRANS_TAC EQ_TRANS) `compile_expr (ce with ce_module := src) ty e st` >>
      conj_tac
      >- (irule (cj 1 runtime_default_compile_vars) >> asm_rewrite_tac[] >> qexists_tac `mods` >> asm_rewrite_tac[]) >>
      irule (cj 1 runtime_default_compile_module_mods) >> asm_rewrite_tac[] >> qexists_tac `mods` >> asm_rewrite_tac[])
  >- (Q_TAC (TRANS_TAC EQ_TRANS) `compile_builtin_dispatch (ce with ce_module := src) rt ty bi args st` >>
      conj_tac
      >- (irule (cj 2 runtime_default_compile_vars) >> asm_rewrite_tac[] >> qexists_tac `mods` >> asm_rewrite_tac[]) >>
      irule (cj 2 runtime_default_compile_module_mods) >> asm_rewrite_tac[] >> qexists_tac `mods` >> asm_rewrite_tac[])
  >> (Q_TAC (TRANS_TAC EQ_TRANS) `compile_type_builtin_dispatch (ce with ce_module := src) vt ty tb rt args st` >>
      conj_tac
      >- (irule (cj 3 runtime_default_compile_vars) >> asm_rewrite_tac[] >> qexists_tac `mods` >> asm_rewrite_tac[]) >>
      irule (cj 3 runtime_default_compile_module_mods) >> asm_rewrite_tac[] >> qexists_tac `mods` >> asm_rewrite_tac[])
QED

Theorem compile_expr_module_pin:
  runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
  compile_expr (ce with ce_module := src) ty e st = compile_expr ce ty e st
Proof
  strip_tac >> irule (cj 1 runtime_default_compile_module_mods) >>
  asm_rewrite_tac[] >> qexists_tac `mods` >> asm_rewrite_tac[]
QED

Theorem compile_stage_intcall_args_module_pin:
  EVERY (runtime_constant_expr mods) es /\ ~supported_exprs_exists ^bad_builtin_arity es ==>
  compile_stage_intcall_args compile_expr (ce with ce_module := src) es flags tys si =
  compile_stage_intcall_args compile_expr ce es flags tys si
Proof
  strip_tac >> AP_THM_TAC >>
  irule compile_stage_intcall_args_module_pin_cong >>
  simp[unwrap_value_module_pin, type_memory_bytes_module_pin,
       compile_store_memory_module_pin, FUN_EQ_THM] >> rpt strip_tac >>
  irule compile_expr_module_pin >>
  fs[supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM, EVERY_MEM] >>
  metis_tac[]
QED
