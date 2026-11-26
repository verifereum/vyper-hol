Theory bodyIntCallDefaultErasureMods
Ancestors
  exprLowering exprCallBounds compileEnv vyperTypeContract vyperTypeSystem
  vyperAST vyperContext supportedExprTraverse whitelistCheckerConsts exprLoweringEquations allocLimitsProps
  context list pair gasShadow gasShadowCompileBase gasShadowCompile gasShadowCompileStmtHelpers
  runtimeDefaultCompile gasShadowShape boolChainOpsCong runtimeConstBoolChainOperands
  ctorCallFreeBoolChain boolChainOperandsSupported

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem erasure_type_memory[simp,local]:
  type_memory_bytes (ce with ce_func_defaults := ds) = type_memory_bytes ce
Proof
  irule type_memory_bytes_frame >> simp[]
QED

Theorem erasure_place_type[simp,local]:
  place_type (ce with ce_func_defaults := ds) = place_type ce
Proof
  simp[FUN_EQ_THM] >> gen_tac >> irule place_type_env_cong >> simp[]
QED

Theorem erasure_value_type[simp,local]:
  lowered_value_type (ce with ce_func_defaults := ds) = lowered_value_type ce
Proof
  simp[FUN_EQ_THM] >> rpt gen_tac >> irule lowered_value_type_frame >> simp[]
QED

Theorem erasure_elem_size[simp,local]:
  elem_size_in_location (ce with ce_func_defaults := ds) = elem_size_in_location ce
Proof
  simp[FUN_EQ_THM, elem_size_in_location_def]
QED

Theorem erasure_typed_store[simp,local]:
  (!ce dst dt src st. compile_store_memory_typed (ce with ce_func_defaults := ds) dst dt src st =
                      compile_store_memory_typed ce dst dt src st) /\
  (!ce dst src dts sts doff soff.
    compile_typed_copy_fields (ce with ce_func_defaults := ds) dst src dts sts doff soff =
    compile_typed_copy_fields ce dst src dts sts doff soff) /\
  (!ce dst dt src st n.
    compile_copy_sarray_typed (ce with ce_func_defaults := ds) dst dt src st n =
    compile_copy_sarray_typed ce dst dt src st n) /\
  (!ce dst dt n src st.
    compile_copy_dynarray_typed (ce with ce_func_defaults := ds) dst dt n src st =
    compile_copy_dynarray_typed ce dst dt n src st) /\
  (!ce dst src dfs sfs doff soff.
    compile_struct_typed_copy (ce with ce_func_defaults := ds) dst src dfs sfs doff soff =
    compile_struct_typed_copy ce dst src dfs sfs doff soff)
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac >> rpt gen_tac >> TRY (DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, FUN_EQ_THM, LET_THM]
  >~ [`is_word_type dt`] >-
    (Cases_on `dt` >> Cases_on `st` >> simp[] >>
     rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> gvs[]))) >>
  rpt (pairarg_tac >> fs[])
QED

Theorem erasure_store[simp,local]:
  compile_store_memory (ce with ce_func_defaults := ds) = compile_store_memory ce
Proof
  simp[FUN_EQ_THM, compile_store_memory_def]
QED

Theorem erasure_unwrap[simp,local]:
  unwrap_value (ce with ce_func_defaults := ds) vv = unwrap_value ce vv
Proof
  Cases_on `vv` >> simp[unwrap_value_def]
QED

Theorem erasure_lower_value[local]:
  (!s. f (ce with ce_func_defaults := ds) ty e s = g ce ty e s) ==>
  lower_value f (ce with ce_func_defaults := ds) ty e = lower_value g ce ty e
Proof
  simp[lower_value_def, comp_bind_def, FUN_EQ_THM]
QED

Theorem erasure_punnable[simp,local]:
  (!ce t u. punnable (ce with ce_func_defaults := ds) t u = punnable ce t u) /\
  (!ce ts us. punnable_list (ce with ce_func_defaults := ds) ts us =
              punnable_list ce ts us)
Proof
  ho_match_mp_tac punnable_ind >>
  rpt conj_tac >> rpt gen_tac >> TRY (DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  once_rewrite_tac[punnable_def] >> fs[]
QED

Theorem erasure_ifexp_arm[simp,local]:
  compile_ifexp_arm (ce with ce_func_defaults := ds) = compile_ifexp_arm ce
Proof
  simp[FUN_EQ_THM, compile_ifexp_arm_def, same_memory_layout_def]
QED

Theorem erasure_snapshot[simp,local]:
  compile_snapshot_vv (ce with ce_func_defaults := ds) b vv = compile_snapshot_vv ce b vv
Proof
  simp[compile_snapshot_vv_def, compile_materialize_vv_def]
QED

Theorem erasure_struct[local]:
  !fields buf off.
    (!name e st. MEM (name,e) fields ==>
        f (ce with ce_func_defaults := ds) (expr_type e) e st = f' ce (expr_type e) e st) ==>
    compile_struct_lit f (ce with ce_func_defaults := ds) ty fields buf off =
    compile_struct_lit f' ce ty fields buf off
Proof
  Induct >- simp[compile_struct_lit_def] >>
  qx_gen_tac `fld` >> PairCases_on `fld` >> rpt gen_tac >> strip_tac >>
  `!st. f (ce with ce_func_defaults := ds) (expr_type fld1) fld1 st =
        f' ce (expr_type fld1) fld1 st` by
    (gen_tac >> qpat_assum `!name e st. MEM _ (_::fields) ==> _`
       (qspecl_then [`fld0`,`fld1`,`st`] mp_tac) >> simp[]) >>
  `!buf off. compile_struct_lit f (ce with ce_func_defaults := ds) ty fields buf off =
             compile_struct_lit f' ce ty fields buf off` by
    (rpt gen_tac >> first_x_assum irule >> rpt strip_tac >>
     qpat_assum `!name e st. MEM _ (_::fields) ==> _`
       (qspecl_then [`name`,`e`,`st`] mp_tac) >> simp[]) >>
  simp[compile_struct_lit_def, comp_bind_def, comp_ignore_bind_def, FUN_EQ_THM]
QED

Theorem erasure_make_array[local]:
  !es elem_ty elem_size has_len buf idx.
    (!e st. MEM e es ==>
      f (ce with ce_func_defaults := ds) (expr_type e) e st = f' ce (expr_type e) e st) ==>
    compile_make_array_elems f (ce with ce_func_defaults := ds) es elem_ty elem_size has_len buf idx =
    compile_make_array_elems f' ce es elem_ty elem_size has_len buf idx
Proof
  Induct >> simp[compile_make_array_elems_def] >> rpt strip_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, LET_THM, FUN_EQ_THM]
QED

Theorem erasure_make_tuple[local]:
  !es tys buf off.
    (!e st. MEM e es ==>
      f (ce with ce_func_defaults := ds) (expr_type e) e st = f' ce (expr_type e) e st) ==>
    compile_make_tuple f (ce with ce_func_defaults := ds) es tys buf off =
    compile_make_tuple f' ce es tys buf off
Proof
  Induct >> simp[compile_make_tuple_def] >> gen_tac >> Cases >>
  simp[compile_make_tuple_def] >> rpt strip_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, LET_THM, FUN_EQ_THM]
QED

Theorem erasure_multi_exprs[local]:
  !es.
    (!e st. MEM e es ==>
      f (ce with ce_func_defaults := ds) (expr_type e) e st = f' ce (expr_type e) e st) ==>
    compile_multi_exprs f (ce with ce_func_defaults := ds) es =
    compile_multi_exprs f' ce es
Proof
  Induct >> simp[compile_multi_exprs_def] >> rpt strip_tac >>
  `lower_value f (ce with ce_func_defaults := ds) (expr_type h) h =
   lower_value f' ce (expr_type h) h` by (irule erasure_lower_value >> simp[]) >>
  simp[comp_bind_def, LET_THM, FUN_EQ_THM]
QED

Theorem erasure_invert[simp,local]:
  compile_invert v ty (ce with ce_func_defaults := ds) = compile_invert v ty ce
Proof
  Cases_on `ty` >> simp[compile_invert_def]
QED

Theorem erasure_var_array_membership[simp,local]:
  compile_var_array_membership (ce with ce_func_defaults := ds) = compile_var_array_membership ce
Proof
  simp[FUN_EQ_THM, compile_var_array_membership_def, LET_THM]
QED

Theorem erasure_acc[local]:
  (!st. lower_value f (ce with ce_func_defaults := ds) (BaseT AddressT) e st =
        lower_value f' ce (BaseT AddressT) e st) ==>
  compile_acc f (ce with ce_func_defaults := ds) e a = compile_acc f' ce e a
Proof
  Cases_on `a` >> simp[compile_acc_def, FUN_EQ_THM, LET_THM]
QED

Theorem erasure_child[local]:
  expr_size e < n /\
  compile_expr (ce with ce_func_defaults := ds) ty e st = compile_expr ce ty e st ==>
  expr_child_callback (n + cenv_defaults_size (ce with ce_func_defaults := ds))
    compile_expr (ce with ce_func_defaults := ds) ty e st =
  expr_child_callback (n + cenv_defaults_size ce) compile_expr ce ty e st
Proof
  simp[expr_child_callback_def]
QED

Theorem erasure_runtime_args[local]:
  (EVERY (runtime_constant_expr mods) es \/ EVERY (constant_expr mods) es) ==>
  EVERY (runtime_constant_expr mods) es
Proof
  simp[EVERY_MEM] >> metis_tac[constant_expr_runtime_constant]
QED

Theorem erasure_args_shape[local]:
  (EVERY (runtime_constant_expr mods) es /\ ~supported_exprs_exists ^bad_builtin_arity es) <=>
  EVERY (\e. runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e) es
Proof
  simp[supported_exprs_exists_every, EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem erasure_default_fields[local]:
  (!ce ty e st. runtime_constant_expr mods e /\
    ~supported_expr_exists ^bad_builtin_arity e ==>
    compile_expr (ce with ce_func_defaults := ds) ty e st = compile_expr ce ty e st) /\
  (!ce rt ty bi args st.
    (runtime_constant_builtin bi \/ constant_builtin bi) /\
    builtin_args_length_ok bi (LENGTH args) /\
    EVERY (runtime_constant_expr mods) args /\
    ~supported_exprs_exists ^bad_builtin_arity args ==>
    compile_builtin_dispatch (ce with ce_func_defaults := ds) rt ty bi args st =
    compile_builtin_dispatch ce rt ty bi args st) /\
  (!ce vt ty tb rt args st.
    constant_type_builtin tb /\ type_builtin_args_length_ok tb (LENGTH args) /\
    EVERY (runtime_constant_expr mods) args /\
    ~supported_exprs_exists ^bad_builtin_arity args ==>
    compile_type_builtin_dispatch (ce with ce_func_defaults := ds) vt ty tb rt args st =
    compile_type_builtin_dispatch ce vt ty tb rt args st)
Proof
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >>
  rpt gen_tac >> disch_tac >> once_rewrite_tac[compile_expr_raw_def] >>
  simp_tac bool_ss [] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
  >~ [`compile_expr_body`] >- suspend "expr"
  >~ [`compile_builtin_dispatch_body`] >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume erasure_default_fields[expr]:
  Cases_on `e` >> fs[runtime_constant_expr_def]
  >~ [`compile_expr_body _ _ _ _ _ (TopLevelName _ _) _`] >-
    (once_rewrite_tac[compile_expr_body_def] >> simp[expr_type_def])
  >~ [`compile_expr_body _ _ _ _ _ (Literal _ _) _`] >-
    (once_rewrite_tac[compile_expr_body_def] >> simp[expr_type_def])
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >- suspend "builtin_node"
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >- suspend "constant_builtin_node"
  >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _`] >- suspend "type_node" >>
  fs[supported_expr_exists_def]
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >- suspend "ifexp"
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >- suspend "ifexp_alt"
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _`] >- suspend "struct"
  >~ [`compile_expr_body _ _ _ _ _ (Subscript _ _ _) _`] >- suspend "subscript"
  >> suspend "attribute"
QED

val erasure_builtin_node_tac =
  rename1 `compile_expr_body _ _ _ _ _ (Builtin ann bi args) _` >>
  `EVERY (runtime_constant_expr mods) args` by (irule erasure_runtime_args >> simp[]) >>
  `!at a bt b mt m. args <> [Name at a; Name bt b; Name mt m]` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_assum `EVERY (runtime_constant_expr mods) _` mp_tac >>
     simp[runtime_constant_expr_def]) >>
  `!at a bt b. args <> [Name at a; Name bt b]` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_assum `EVERY (runtime_constant_expr mods) _` mp_tac >>
     simp[runtime_constant_expr_def]) >>
  simp[compile_expr_body_builtin_default, builtin_child_callback_def] >>
  fs[supported_expr_exists_def, expr_size_def];

Resume erasure_default_fields[builtin_node]:
  erasure_builtin_node_tac
QED

Resume erasure_default_fields[constant_builtin_node]:
  erasure_builtin_node_tac
QED

Resume erasure_default_fields[type_node]:
  once_rewrite_tac[compile_expr_body_def] >>
  fs[supported_expr_exists_def, expr_type_def, type_child_callback_def, expr_size_def]
QED

val erasure_ifexp_tac =
  rename1 `IfExp t c a b` >>
  `!e ty s. (e = c \/ e = a \/ e = b) ==>
    compile_expr (ce with ce_func_defaults := ds) ty e s = compile_expr ce ty e s` by
    (rpt gen_tac >>
     disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
     qpat_assum `!e' ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _` irule >>
     simp[expr_size_def]) >>
  once_rewrite_tac[compile_expr_body_def] >>
  fs[expr_type_def, expr_size_def, lower_value_def, comp_bind_def, LET_THM];

Resume erasure_default_fields[ifexp]:
  erasure_ifexp_tac
QED

Resume erasure_default_fields[ifexp_alt]:
  erasure_ifexp_tac
QED

Resume erasure_default_fields[struct]:
  rename1 `StructLit t nsid fields` >>
  `!name e st. MEM (name,e) fields ==>
    expr_child_callback (expr_size (StructLit t nsid fields) +
      cenv_defaults_size (ce with ce_func_defaults := ds))
      compile_expr (ce with ce_func_defaults := ds) (expr_type e) e st =
    expr_child_callback (expr_size (StructLit t nsid fields) + cenv_defaults_size ce)
      compile_expr ce (expr_type e) e st` by
    (rpt strip_tac >> irule erasure_child >>
     `expr_size e < expr_size (StructLit t nsid fields)` by
       metis_tac[expr_struct_field_bound] >>
     simp[] >> qpat_assum `!e' ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _` irule >>
     fs[supported_fields_exists_every, EVERY_MEM, MEM_MAP] >> metis_tac[SND]) >>
  `!buf. compile_struct_lit
      (expr_child_callback (expr_size (StructLit t nsid fields) +
        cenv_defaults_size (ce with ce_func_defaults := ds)) compile_expr)
      (ce with ce_func_defaults := ds) (StructT nsid) fields buf 0 =
    compile_struct_lit (expr_child_callback
      (expr_size (StructLit t nsid fields) + cenv_defaults_size ce) compile_expr)
      ce (StructT nsid) fields buf 0` by
    (gen_tac >> irule erasure_struct >> first_assum ACCEPT_TAC) >>
  once_rewrite_tac[compile_expr_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  fs[LET_THM, expr_type_def, expr_size_def, Excl "expr_child_callback_def"]
QED

Resume erasure_default_fields[subscript]:
  rename1 `Subscript t b i` >>
  `!e ty st. (e = b \/ e = i) ==>
    expr_child_callback (expr_size (Subscript t b i) +
      cenv_defaults_size (ce with ce_func_defaults := ds))
      compile_expr (ce with ce_func_defaults := ds) ty e st =
    expr_child_callback (expr_size (Subscript t b i) + cenv_defaults_size ce)
      compile_expr ce ty e st` by
    (rpt gen_tac >> disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
     irule erasure_child >> simp[expr_size_def] >>
     qpat_assum `!e' ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _` irule >>
     simp[expr_size_def]) >>
  `!ty. lower_value (expr_child_callback (expr_size (Subscript t b i) +
      cenv_defaults_size (ce with ce_func_defaults := ds)) compile_expr)
      (ce with ce_func_defaults := ds) ty i =
    lower_value (expr_child_callback (expr_size (Subscript t b i) + cenv_defaults_size ce)
      compile_expr) ce ty i` by (gen_tac >> irule erasure_lower_value >> simp[]) >>
  once_rewrite_tac[compile_expr_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  fs[expr_type_def, expr_size_def, compile_subscript_def, copies_subscript_base_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM, Excl "expr_child_callback_def"]
QED

Resume erasure_default_fields[attribute]:
  rename1 `Attribute t e nm` >>
  `!ty st. compile_expr (ce with ce_func_defaults := ds) ty e st = compile_expr ce ty e st` by
    (rpt gen_tac >>
     qpat_assum `!child env typ cs. _ ==> _ ==> compile_expr _ _ child cs = _` irule >>
     simp[expr_size_def]) >>
  once_rewrite_tac[compile_expr_body_def] >>
  simp[expr_type_def, compile_attribute_def, expr_child_callback_def, comp_bind_def, LET_THM]
QED

Resume erasure_default_fields[type_builtin]:
  Cases_on `tb` >> fs[constant_type_builtin_def] >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM]
QED

Resume erasure_default_fields[builtin]:
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qabbrev_tac `f = expr_child_callback
    (list_size expr_size args + cenv_defaults_size (ce with ce_func_defaults := ds)) compile_expr` >>
  qabbrev_tac `g = expr_child_callback (list_size expr_size args + cenv_defaults_size ce) compile_expr` >>
  `!e ty st. expr_size e < list_size expr_size args /\
      runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
    f (ce with ce_func_defaults := ds) ty e st = g ce ty e st` by
    (rpt strip_tac >> simp[Abbr `f`, Abbr `g`] >> irule erasure_child >>
     simp[] >> qpat_assum `!child env typ cs. _ ==> _ ==> compile_expr _ _ child cs = _` irule >>
     simp[]) >>
  `!e. MEM e args ==> runtime_constant_expr mods e /\
                      ~supported_expr_exists ^bad_builtin_arity e` by
    (`EVERY (\e. runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e) args` by
       simp[GSYM erasure_args_shape] >> fs[EVERY_MEM]) >>
  `!e ty st. MEM e args ==>
    f (ce with ce_func_defaults := ds) ty e st = g ce ty e st` by
    (rpt strip_tac >> first_x_assum irule >> simp[expr_list_member_bound]) >>
  `!e ty. MEM e args ==>
    lower_value f (ce with ce_func_defaults := ds) ty e = lower_value g ce ty e` by
    (rpt strip_tac >> irule erasure_lower_value >> simp[]) >>
  `!ts. MAP (type_memory_bytes (ce with ce_func_defaults := ds)) ts =
         MAP (type_memory_bytes ce) ts` by simp[] >>
  `!ann elem b elems. MEM (Builtin ann (MakeArray elem b) elems) args ==>
    compile_multi_exprs f (ce with ce_func_defaults := ds) elems = compile_multi_exprs g ce elems` by
    (rpt strip_tac >> irule erasure_multi_exprs >> rpt strip_tac >>
     qpat_assum `!e ty st. expr_size e < _ /\ _ ==> _` irule >>
     `expr_size (Builtin ann (MakeArray elem b) elems) < list_size expr_size args` by
       simp[expr_list_member_bound] >>
     `expr_size e < list_size expr_size elems` by simp[expr_list_member_bound] >>
     `expr_size e < list_size expr_size args` by (fs[expr_size_def] >> decide_tac) >>
     `runtime_constant_expr mods (Builtin ann (MakeArray elem b) elems) /\
       ~supported_expr_exists ^bad_builtin_arity (Builtin ann (MakeArray elem b) elems)` by
       simp[] >>
     fs[runtime_constant_expr_def, runtime_constant_builtin_def, constant_builtin_def,
        supported_expr_exists_def] >>
     `EVERY (runtime_constant_expr mods) elems` by (irule erasure_runtime_args >> simp[]) >>
     `EVERY (\e. runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e) elems` by
       simp[GSYM erasure_args_shape] >> fs[EVERY_MEM]) >>
  Cases_on `bi` >> fs[runtime_constant_builtin_def, constant_builtin_def] >>
  FIRST [rename1 `compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _ _` >>
         suspend "make_array",
         rename1 `compile_builtin_dispatch_body _ _ _ _ (BoolChain _ _) _ _` >>
         suspend "bool_chain",
         rename1 `compile_builtin_dispatch_body _ _ _ _ (Bop _) _ _` >> suspend "bop",
         rename1 `compile_builtin_dispatch_body _ _ _ _ (Acc _) _ _` >> suspend "acc",
         suspend "simple_builtin"]
QED

Resume erasure_default_fields[make_array]:
  markerLib.RESUME_TAC >>
  `!tys buf off. compile_make_tuple f (ce with ce_func_defaults := ds) args tys buf off =
                 compile_make_tuple g ce args tys buf off` by
    (rpt gen_tac >> irule erasure_make_tuple >> simp[]) >>
  `!et sz has_len buf idx.
    compile_make_array_elems f (ce with ce_func_defaults := ds) args et sz has_len buf idx =
    compile_make_array_elems g ce args et sz has_len buf idx` by
    (rpt gen_tac >> irule erasure_make_array >> simp[]) >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[compile_make_array_def, comp_bind_def, comp_ignore_bind_def]
QED

Resume erasure_default_fields[bool_chain]:
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  rename1 `compile_builtin_dispatch_body f _ rt ty (BoolChain d n) [arg] st` >>
  `EVERY (runtime_constant_expr mods) (bool_chain_operands d (n - 1) arg)` by
    simp[runtime_constant_bool_chain_operands] >>
  `EVERY (\e. ~supported_expr_exists ^bad_builtin_arity e)
       (bool_chain_operands d (n - 1) arg)` by simp[bool_chain_operands_supported] >>
  `!r exit_lbl. compile_bool_chain_ops f (ce with ce_func_defaults := ds) d r exit_lbl
                (bool_chain_operands d (n - 1) arg) =
                compile_bool_chain_ops g ce d r exit_lbl (bool_chain_operands d (n - 1) arg)` by
    (rpt gen_tac >> irule compile_bool_chain_ops_lower_value_cong >>
     qx_gen_tac `e` >> strip_tac >> irule erasure_lower_value >> gen_tac >>
     qpat_assum `!e ty st. expr_size e < _ /\ _ ==> _` irule >>
     `expr_size e <= expr_size arg` by metis_tac[bool_chain_operand_size] >>
     fs[EVERY_MEM, list_size_def]) >>
  simp[compile_builtin_dispatch_body_def, LET_THM]
QED

Resume erasure_default_fields[bop]:
  markerLib.RESUME_TAC >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `h'` >> simp[] >>
  rename1 `Builtin _ bb as'` >>
  Cases_on `bb` >> simp[]
QED

Resume erasure_default_fields[acc]:
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  `compile_acc f (ce with ce_func_defaults := ds) h a = compile_acc g ce h a` by
    (irule erasure_acc >> simp[]) >>
  simp[compile_builtin_dispatch_body_def, LET_THM]
QED

Resume erasure_default_fields[simple_builtin]:
  markerLib.RESUME_TAC >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  simp[compile_builtin_dispatch_body_def, LET_THM]
QED

Finalise erasure_default_fields

Theorem compile_expr_default_erasure_mods:
  runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
  compile_expr (cenv_without_defaults ce tag) ty e si = compile_expr ce ty e si
Proof
  simp[cenv_without_defaults_def] >> strip_tac >>
  irule (cj 1 erasure_default_fields) >> simp[] >> qexists_tac `mods` >> simp[]
QED

Theorem erasure_stage_fields[local]:
  !es flags tys.
    EVERY (\e. runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e) es ==>
    compile_stage_intcall_args compile_expr (ce with ce_func_defaults := ds) es flags tys =
    compile_stage_intcall_args compile_expr ce es flags tys
Proof
  Induct >- simp[compile_stage_intcall_args_def] >>
  qx_genl_tac [`h`,`flags`,`tys`] >>
  simp[EVERY_DEF] >> strip_tac >>
  `!ty. runtime_constant_expr mods h /\ ~supported_expr_exists ^bad_builtin_arity h ==>
       compile_expr (ce with ce_func_defaults := ds) ty h = compile_expr ce ty h` by
    (simp[FUN_EQ_THM] >> rpt strip_tac >> irule (cj 1 erasure_default_fields) >>
     simp[] >> qexists_tac `mods` >> simp[]) >>
  Cases_on `flags`
  >- simp[compile_stage_intcall_args_def, comp_bind_def] >>
  rename1 `compile_stage_intcall_args _ _ _ ((flag:bool)::fs) tys = _` >> Cases_on `tys`
  >- simp[compile_stage_intcall_args_def, comp_bind_def] >>
  Cases_on `flag` >>
  simp[compile_stage_intcall_args_def, LET_THM, comp_bind_def, comp_ignore_bind_def]
QED

Theorem compile_stage_default_erasure_mods:
  EVERY (runtime_constant_expr mods) es /\ ~supported_exprs_exists ^bad_builtin_arity es ==>
  compile_stage_intcall_args compile_expr (cenv_without_defaults ce tag) es flags tys si =
  compile_stage_intcall_args compile_expr ce es flags tys si
Proof
  simp[erasure_args_shape, cenv_without_defaults_def] >> strip_tac >>
  AP_THM_TAC >> irule erasure_stage_fields >> qexists_tac `mods` >> simp[]
QED

Theorem erasure_shadow_arity[local]:
  !e. (^bad_builtin_arity) (gas_shadow_expr e) = (^bad_builtin_arity) e
Proof
  Cases >> simp[gas_shadow_expr_def] >>
  rw[gas_shadow_builtin_def] >> simp[builtin_args_length_ok_def]
QED

(* At the actual shadow default cut, the environment's defaults table is
   shadowed as well as the operand list. Commute erasure with that change,
   then apply the ordinary equation to exactly the list compiled there. *)
Theorem compile_stage_default_erasure_shadow_mods:
  EVERY (runtime_constant_expr mods) es /\ ~supported_exprs_exists ^bad_builtin_arity es ==>
  compile_stage_intcall_args compile_expr (gas_shadow_env T (cenv_without_defaults ce tag))
      (MAP gas_shadow_expr es) flags tys si =
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr es) flags tys si
Proof
  strip_tac >> simp[GSYM gasShadowCompileHelpersTheory.gas_shadow_env_without_defaults] >>
  `supported_exprs_exists ^bad_builtin_arity (MAP gas_shadow_expr es) =
   supported_exprs_exists ^bad_builtin_arity es` by
    (match_mp_tac (cj 3 gas_shadow_expr_exists_invariant) >>
     ACCEPT_TAC erasure_shadow_arity) >>
  irule compile_stage_default_erasure_mods >> simp[] >> qexists_tac `mods` >>
  fs[EVERY_MAP, EVERY_MEM, runtime_constant_expr_gas_shadow]
QED

(* The syntax test is unchanged at the gas-shadow expression seam; the
   statement compiler uses gas_shadow_stmt_compile_expr_env when its
   compilation environment is itself shadowed. *)
Theorem erasure_shadow_expr_check[local]:
  runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
  gas_shadow_compiles (compile_expr (cenv_without_defaults ce tag) ty e)
    (compile_expr ce ty (gas_shadow_expr e)) /\
  gas_shadow_compiles (compile_expr (cenv_without_defaults ce tag) ty e)
    (compile_expr (gas_shadow_env sd ce) ty (gas_shadow_expr e))
Proof
  strip_tac >>
  `compile_expr (cenv_without_defaults ce tag) ty e = compile_expr ce ty e` by
    (simp[FUN_EQ_THM] >> gen_tac >> irule compile_expr_default_erasure_mods >>
     simp[] >> qexists_tac `mods` >> simp[]) >>
  simp[gas_shadow_stmt_compile_expr_env] >>
  qspecl_then [`ce`, `ty`, `e`, `T`] mp_tac (cj 1 gas_shadow_compile_expr) >> simp[]
QED
