(* Runtime constants compile independently of the function's argument slots. *)
Theory runtimeDefaultCompile
Ancestors
  exprLowering exprCallBounds compileEnv vyperTypeContract vyperTypeSystem
  vyperContext vyperValue vyperAST supportedExprTraverse whitelistCheckerConsts
  allocLimitsProps exprCallbackContracts moduleLowering exprLoweringEquations context
  gasShadow gasShadowShape list pair
  boolChainOpsCong runtimeConstBoolChainOperands
  ctorCallFreeBoolChain boolChainOperandsSupported

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem well_typed_expr_builtin_args_length:
  (!env e. well_typed_expr env e ==> ~supported_expr_exists ^bad_builtin_arity e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
     ~supported_expr_exists ^bad_builtin_arity e) /\
  (!env t vt. type_place_target env t = SOME vt ==>
     ~supported_target_exists ^bad_builtin_arity t) /\
  (!env es. well_typed_exprs env es ==> ~supported_exprs_exists ^bad_builtin_arity es) /\
  (!env opt. well_typed_opt env opt ==> ~supported_opt_exists ^bad_builtin_arity opt) /\
  (!env kes. well_typed_named_exprs env kes ==>
     ~supported_fields_exists ^bad_builtin_arity kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  gvs[well_typed_expr_def, supported_expr_exists_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> gvs[] >>
  metis_tac[vyperTypeBuiltinsTheory.well_typed_builtin_app_length,
            vyperTypeBuiltinsTheory.well_typed_type_builtin_args_length, LENGTH_MAP]
QED

Theorem constant_expr_gas_shadow[local]:
  !mods e. constant_expr mods e ==> constant_expr mods (gas_shadow_expr e)
Proof
  ho_match_mp_tac constant_expr_ind >>
  simp[gas_shadow_expr_def, constant_expr_def, EVERY_MAP, MAP_MAP_o, EVERY_MEM,
       combinTheory.o_DEF, pairTheory.FORALL_PROD] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  fs[gas_shadow_builtin_def] >>
  TRY (IF_CASES_TAC >> gvs[constant_builtin_def])
  >~ [`MEM _ kes`] >-
    (rpt strip_tac >>
     qpat_assum `!e. MEM e (MAP SND kes) ==> _` irule >>
     conj_tac
     >- (simp[MEM_MAP] >> qexists_tac `(p_1,p_2)` >> simp[]) >>
     first_x_assum drule >> simp[]) >>
  metis_tac[]
QED

Theorem runtime_constant_expr_gas_shadow:
  !mods e. runtime_constant_expr mods e ==>
    runtime_constant_expr mods (gas_shadow_expr e)
Proof
  `!e. bool_literal_expr e ==> bool_literal_expr (gas_shadow_expr e)` by
    (Cases >> simp[gas_shadow_expr_def, bool_literal_expr_def]) >>
  ho_match_mp_tac runtime_constant_expr_ind >>
  simp[gas_shadow_expr_def, runtime_constant_expr_def, EVERY_MAP, MAP_MAP_o,
       EVERY_MEM, combinTheory.o_DEF, pairTheory.FORALL_PROD] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  fs[gas_shadow_builtin_def] >>
  TRY (IF_CASES_TAC >> gvs[constant_builtin_def, runtime_constant_builtin_def])
  >~ [`MEM _ kes`] >-
    (rpt strip_tac >>
     qpat_assum `!e. MEM e (MAP SND kes) ==> _` irule >>
     conj_tac
     >- (simp[MEM_MAP] >> qexists_tac `(p_1,p_2)` >> simp[]) >>
     first_x_assum drule >> simp[]) >>
  metis_tac[constant_expr_gas_shadow]
QED

Theorem runtime_default_compile_defaults_size[local]:
  cenv_defaults_size (ce with ce_vars := vars) = cenv_defaults_size ce
Proof
  simp[cenv_defaults_size_def]
QED

Theorem runtime_default_value_size[local]:
  type_memory_bytes (ce with ce_vars := vars) ty = type_memory_bytes ce ty /\
  lowered_value_type (ce with ce_vars := vars) e = lowered_value_type ce e /\
  place_type (ce with ce_vars := vars) e = place_type ce e
Proof
  rpt conj_tac
  >- (mp_tac (Q.SPECL [`ce`, `ce with ce_vars := vars`] type_memory_bytes_frame) >>
      simp[FUN_EQ_THM])
  >- (irule lowered_value_type_frame >> simp[])
  >> irule place_type_env_cong >> simp[]
QED

Theorem runtime_default_unwrap_vars[local]:
  unwrap_value (ce with ce_vars := vars) vv = unwrap_value ce vv
Proof
  Cases_on `vv` >> simp[unwrap_value_def, runtime_default_value_size]
QED

Theorem runtime_default_lower_value_vars[local]:
  (!s. f (ce with ce_vars := vars) ty e s = g ce ty e s) ==>
  lower_value f (ce with ce_vars := vars) ty e =
  lower_value g ce ty e
Proof
  simp[lower_value_def, comp_bind_def, FUN_EQ_THM, runtime_default_unwrap_vars]
QED

Theorem runtime_default_typed_copy_vars[local]:
  (!ce dst dt src st. compile_store_memory_typed (ce with ce_vars := vars) dst dt src st =
                      compile_store_memory_typed ce dst dt src st) /\
  (!ce dst src dts sts doff soff.
    compile_typed_copy_fields (ce with ce_vars := vars) dst src dts sts doff soff =
    compile_typed_copy_fields ce dst src dts sts doff soff) /\
  (!ce dst dt src st n.
    compile_copy_sarray_typed (ce with ce_vars := vars) dst dt src st n =
    compile_copy_sarray_typed ce dst dt src st n) /\
  (!ce dst dt n src st.
    compile_copy_dynarray_typed (ce with ce_vars := vars) dst dt n src st =
    compile_copy_dynarray_typed ce dst dt n src st) /\
  (!ce dst src dfs sfs doff soff.
    compile_struct_typed_copy (ce with ce_vars := vars) dst src dfs sfs doff soff =
    compile_struct_typed_copy ce dst src dfs sfs doff soff)
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac >> rpt gen_tac >> TRY (DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
  once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[runtime_default_value_size, comp_bind_def, comp_ignore_bind_def,
       FUN_EQ_THM, LET_THM]
  >~ [`is_word_type dt`] >-
    (Cases_on `dt` >> Cases_on `st` >> simp[] >>
     rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> gvs[]))) >>
  rpt (pairarg_tac >> fs[])
QED

Theorem runtime_default_store_vars[local]:
  compile_store_memory (ce with ce_vars := vars) src dst dst_ty src_ty =
  compile_store_memory ce src dst dst_ty src_ty
Proof
  simp[compile_store_memory_def, runtime_default_typed_copy_vars,
       runtime_default_value_size]
QED

Theorem runtime_default_ifexp_arm_vars[local]:
  compile_ifexp_arm (ce with ce_vars := vars) ty arm vv =
  compile_ifexp_arm ce ty arm vv
Proof
  `(!ce t u. punnable (ce with ce_vars := vars) t u = punnable ce t u) /\
    (!ce ts us. punnable_list (ce with ce_vars := vars) ts us =
                punnable_list ce ts us)` by
    (ho_match_mp_tac punnable_ind >>
     rpt conj_tac >> rpt gen_tac >> TRY (DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
     once_rewrite_tac[punnable_def] >> fs[runtime_default_value_size]) >>
  simp[compile_ifexp_arm_def, same_memory_layout_def,
       runtime_default_value_size, runtime_default_unwrap_vars, runtime_default_store_vars]
QED

Theorem runtime_default_struct_vars[local]:
  !fields buf off.
    (!name e st. MEM (name,e) fields ==>
      f (ce with ce_vars := vars) (expr_type e) e st = f ce (expr_type e) e st) ==>
    compile_struct_lit f (ce with ce_vars := vars) ty fields buf off =
    compile_struct_lit f ce ty fields buf off
Proof
  Induct >- simp[compile_struct_lit_def] >>
  qx_gen_tac `field_pair` >> PairCases_on `field_pair` >>
  rpt gen_tac >> strip_tac >>
  `!st. f (ce with ce_vars := vars) (expr_type field_pair1) field_pair1 st =
        f ce (expr_type field_pair1) field_pair1 st` by
    (gen_tac >> qpat_assum `!name e st. MEM _ (_::fields) ==> _`
       (qspecl_then [`field_pair0`,`field_pair1`,`st`] mp_tac) >> simp[]) >>
  `!buf off. compile_struct_lit f (ce with ce_vars := vars) ty fields buf off =
             compile_struct_lit f ce ty fields buf off` by
    (rpt gen_tac >> first_x_assum irule >> rpt strip_tac >>
     qpat_assum `!name e st. MEM _ (_::fields) ==> _`
       (qspecl_then [`name`,`e`,`st`] mp_tac) >> simp[]) >>
  simp[compile_struct_lit_def, runtime_default_value_size,
       runtime_default_unwrap_vars, runtime_default_store_vars,
       comp_bind_def, comp_ignore_bind_def, FUN_EQ_THM]
QED

Theorem runtime_default_make_array_vars[local]:
  !es elem_ty elem_size has_len buf idx.
    (!e st. MEM e es ==>
      f (ce with ce_vars := vars) (expr_type e) e st = f ce (expr_type e) e st) ==>
    compile_make_array_elems f (ce with ce_vars := vars) es elem_ty elem_size has_len buf idx =
    compile_make_array_elems f ce es elem_ty elem_size has_len buf idx
Proof
  Induct >> simp[compile_make_array_elems_def] >> rpt strip_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, LET_THM, FUN_EQ_THM,
       runtime_default_unwrap_vars, runtime_default_store_vars, runtime_default_value_size]
QED

Theorem runtime_default_make_tuple_vars[local]:
  !es tys buf off.
    (!e st. MEM e es ==>
      f (ce with ce_vars := vars) (expr_type e) e st = f ce (expr_type e) e st) ==>
    compile_make_tuple f (ce with ce_vars := vars) es tys buf off =
    compile_make_tuple f ce es tys buf off
Proof
  Induct >> simp[compile_make_tuple_def] >> gen_tac >> Cases >>
  simp[compile_make_tuple_def] >> rpt strip_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, LET_THM, FUN_EQ_THM,
       runtime_default_unwrap_vars, runtime_default_store_vars, runtime_default_value_size]
QED

Theorem runtime_default_multi_exprs_vars[local]:
  !es.
    (!e st. MEM e es ==>
      f (ce with ce_vars := vars) (expr_type e) e st = f ce (expr_type e) e st) ==>
    compile_multi_exprs f (ce with ce_vars := vars) es =
    compile_multi_exprs f ce es
Proof
  Induct >> simp[compile_multi_exprs_def] >> rpt strip_tac >>
  `lower_value f (ce with ce_vars := vars) (expr_type h) h =
    lower_value f ce (expr_type h) h` by
    (irule runtime_default_lower_value_vars >> simp[]) >>
  simp[comp_bind_def, LET_THM, FUN_EQ_THM]
QED

Theorem runtime_default_builtin_env_vars[local]:
  compile_invert v ty (ce with ce_vars := vars) = compile_invert v ty ce /\
  compile_var_array_membership (ce with ce_vars := vars) v vv ty is_in =
    compile_var_array_membership ce v vv ty is_in
Proof
  conj_tac >- (Cases_on `ty` >> simp[compile_invert_def]) >>
  simp[compile_var_array_membership_def, LET_THM, elem_size_in_location_def,
       runtime_default_value_size]
QED

Theorem runtime_default_acc_vars[local]:
  (!st. lower_value f (ce with ce_vars := vars) (BaseT AddressT) e st =
        lower_value f ce (BaseT AddressT) e st) ==>
  compile_acc f (ce with ce_vars := vars) e a = compile_acc f ce e a
Proof
  Cases_on `a` >> simp[compile_acc_def, FUN_EQ_THM, LET_THM]
QED

Theorem runtime_default_compile_vars:
  (!ce ty e st. runtime_constant_expr mods e /\
    ~supported_expr_exists ^bad_builtin_arity e ==>
    compile_expr (ce with ce_vars := vars) ty e st = compile_expr ce ty e st) /\
  (!ce rt ty bi args st.
    (runtime_constant_builtin bi \/ constant_builtin bi) /\
    builtin_args_length_ok bi (LENGTH args) /\
    EVERY (runtime_constant_expr mods) args /\
    ~supported_exprs_exists ^bad_builtin_arity args ==>
    compile_builtin_dispatch (ce with ce_vars := vars) rt ty bi args st =
      compile_builtin_dispatch ce rt ty bi args st) /\
  (!ce vt ty tb rt args st.
    constant_type_builtin tb /\ type_builtin_args_length_ok tb (LENGTH args) /\
    EVERY (runtime_constant_expr mods) args /\
    ~supported_exprs_exists ^bad_builtin_arity args ==>
    compile_type_builtin_dispatch (ce with ce_vars := vars) vt ty tb rt args st =
      compile_type_builtin_dispatch ce vt ty tb rt args st)
Proof
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >>
  rpt gen_tac >> DISCH_TAC >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[runtime_default_compile_defaults_size] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
  >~ [`compile_expr_body`] >- suspend "expr"
  >~ [`compile_builtin_dispatch_body`] >- suspend "builtin"
  >> suspend "type_builtin"
QED

val runtime_default_ifexp_tac =
  rename1 `IfExp t c a b` >>
  `!e ty s. (e = c \/ e = a \/ e = b) ==>
    compile_expr (ce with ce_vars := vars) ty e s = compile_expr ce ty e s` by
    (rpt gen_tac >>
     disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
     qpat_assum `!e' ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _`
       irule >>
     simp[expr_size_def]) >>
  once_rewrite_tac[compile_expr_body_def] >>
  fs[expr_type_def, expr_size_def, runtime_default_value_size,
    runtime_default_compile_defaults_size, runtime_default_ifexp_arm_vars,
    runtime_default_unwrap_vars, lower_value_def, comp_bind_def, LET_THM];

val runtime_default_builtin_tac =
  rename1 `compile_expr_body _ _ _ _ _ (Builtin ann bi args) _` >>
  `EVERY (runtime_constant_expr mods) args` by
    (fs[EVERY_MEM] >> metis_tac[constant_expr_runtime_constant]) >>
  `!t n. ~MEM (Name t n) args` by
    (fs[EVERY_MEM] >> metis_tac[runtime_constant_expr_def]) >>
  `!at a bt b mt m. args <> [Name at a; Name bt b; Name mt m]` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_assum `EVERY (runtime_constant_expr mods) _` mp_tac >>
     simp[runtime_constant_expr_def]) >>
  `!at a bt b. args <> [Name at a; Name bt b]` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_assum `EVERY (runtime_constant_expr mods) _` mp_tac >>
     simp[runtime_constant_expr_def]) >>
  simp[compile_expr_body_builtin_default, builtin_child_callback_def] >>
  fs[supported_expr_exists_def, expr_size_def, runtime_default_compile_defaults_size];

Resume runtime_default_compile_vars[expr]:
  Cases_on `e` >> fs[runtime_constant_expr_def]
  >~ [`compile_expr_body _ _ _ _ _ (TopLevelName _ _) _`] >-
    (once_rewrite_tac[compile_expr_body_def] >> simp[expr_type_def])
  >~ [`compile_expr_body _ _ _ _ _ (Literal _ _) _`] >-
    (once_rewrite_tac[compile_expr_body_def] >> simp[expr_type_def])
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >-
    suspend "expr_builtin"
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >-
    suspend "expr_builtin_constant"
  >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _`] >-
    suspend "expr_type_builtin" >>
  fs[supported_expr_exists_def] >>
  TRY (PairCases_on `p`) >>
  fs[supported_expr_exists_def]
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >- suspend "expr_if"
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >- suspend "expr_if_alt"
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _`] >- suspend "expr_struct"
  >~ [`compile_expr_body _ _ _ _ _ (Subscript _ _ _) _`] >- suspend "expr_subscript"
  >> suspend "expr_attribute"
QED

Resume runtime_default_compile_vars[expr_if]:
  runtime_default_ifexp_tac
QED

Resume runtime_default_compile_vars[expr_if_alt]:
  runtime_default_ifexp_tac
QED

Resume runtime_default_compile_vars[expr_struct]:
  rename1 `StructLit t (p0,p1) l` >>
  `!name e st. MEM (name,e) l ==>
    compile_expr (ce with ce_vars := vars) (expr_type e) e st =
    compile_expr ce (expr_type e) e st` by
    (rpt strip_tac >>
     qpat_assum `!e' ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _` irule >>
     `expr_size e < expr_size (StructLit t (p0,p1) l)` by
       metis_tac[expr_struct_field_bound] >>
     fs[expr_size_def, supported_fields_exists_every, EVERY_MEM, MEM_MAP] >>
     metis_tac[SND]) >>
  once_rewrite_tac[compile_expr_body_def] >>
  simp_tac bool_ss [runtime_default_compile_defaults_size, LET_THM, ETA_AX] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `expr_child_callback lim compile_expr` >>
  `!name e st. MEM (name,e) l ==>
     expr_child_callback lim compile_expr (ce with ce_vars := vars) (expr_type e) e st =
     expr_child_callback lim compile_expr ce (expr_type e) e st` by
    (rpt strip_tac >>
     `expr_size e < expr_size (StructLit t (p0,p1) l)` by
       metis_tac[expr_struct_field_bound] >>
     qpat_assum `!name e st. MEM _ l ==> _`
       (qspecl_then [`name`,`e`,`st`] mp_tac) >>
     fs[Abbr `lim`, expr_size_def, expr_child_callback_def,
        runtime_default_compile_defaults_size]) >>
  `!buf. compile_struct_lit (expr_child_callback lim compile_expr)
       (ce with ce_vars := vars) (StructT (p0,p1)) l buf 0 =
     compile_struct_lit (expr_child_callback lim compile_expr)
       ce (StructT (p0,p1)) l buf 0` by
    (gen_tac >> irule runtime_default_struct_vars >> first_assum ACCEPT_TAC) >>
  simp[expr_type_def]
QED

Resume runtime_default_compile_vars[expr_subscript]:
  `!e ty st. (e = e' \/ e = e0) ==>
    compile_expr (ce with ce_vars := vars) ty e st = compile_expr ce ty e st` by
    (rpt gen_tac >> disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
     qpat_assum `!e' ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _` irule >>
     simp[expr_size_def]) >>
  `!loc. elem_size_in_location (ce with ce_vars := vars) loc =
    elem_size_in_location ce loc` by
    simp[FUN_EQ_THM, elem_size_in_location_def, runtime_default_value_size] >>
  `!vv. compile_snapshot_vv (ce with ce_vars := vars) T vv =
    compile_snapshot_vv ce T vv` by
    simp[compile_snapshot_vv_def, compile_materialize_vv_def,
      runtime_default_value_size, runtime_default_unwrap_vars, runtime_default_store_vars] >>
  once_rewrite_tac[compile_expr_body_def] >>
  simp[expr_type_def, compile_subscript_def, copies_subscript_base_def,
       runtime_default_value_size, runtime_default_compile_defaults_size, LET_THM] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qabbrev_tac `lim = cenv_defaults_size ce + expr_size (Subscript t e' e0)` >>
  `!e ty st. (e = e' \/ e = e0) ==>
     expr_child_callback lim compile_expr (ce with ce_vars := vars) ty e st =
     expr_child_callback lim compile_expr ce ty e st` by
    (rpt gen_tac >> strip_tac >>
     `expr_size e < expr_size (Subscript t e' e0)` by fs[expr_size_def] >>
     fs[Abbr `lim`, expr_size_def, expr_child_callback_def,
        runtime_default_compile_defaults_size] >> metis_tac[]) >>
  `!ty. lower_value (expr_child_callback lim compile_expr)
     (ce with ce_vars := vars) ty e0 =
     lower_value (expr_child_callback lim compile_expr) ce ty e0` by
    (gen_tac >> irule runtime_default_lower_value_vars >> simp[]) >>
  qpat_assum `Abbrev (lim = _)` (fn th => PURE_REWRITE_TAC
    [GSYM (SIMP_RULE bool_ss [markerTheory.Abbrev_def, expr_size_def] th)]) >>
  simp[comp_bind_def, comp_ignore_bind_def, elem_size_in_location_def,
       runtime_default_value_size, expr_child_callback_def] >>
  fs[Abbr `lim`, expr_size_def, runtime_default_compile_defaults_size]
QED

Resume runtime_default_compile_vars[expr_attribute]:
  `!ty st. compile_expr (ce with ce_vars := vars) ty e' st = compile_expr ce ty e' st` by
    (qx_genl_tac [`ty2`,`st2`] >>
     qpat_assum `!child env typ cs. _ ==> _ ==> compile_expr _ _ child cs = _` irule >>
     simp[expr_size_def]) >>
  once_rewrite_tac[compile_expr_body_def] >>
  simp[expr_type_def, compile_attribute_def, expr_child_callback_def,
    runtime_default_compile_defaults_size, comp_bind_def, LET_THM]
QED

Resume runtime_default_compile_vars[expr_builtin]:
  runtime_default_builtin_tac
QED

Resume runtime_default_compile_vars[expr_builtin_constant]:
  runtime_default_builtin_tac
QED

Resume runtime_default_compile_vars[expr_type_builtin]:
  once_rewrite_tac[compile_expr_body_def] >>
  fs[supported_expr_exists_def, expr_type_def, type_child_callback_def, expr_size_def,
     runtime_default_compile_defaults_size]
QED

Resume runtime_default_compile_vars[builtin]:
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qabbrev_tac `lim = cenv_defaults_size ce + list_size expr_size args` >>
  `!e ty st. MEM e args ==>
     expr_child_callback lim compile_expr (ce with ce_vars := vars) ty e st =
     expr_child_callback lim compile_expr ce ty e st` by
    (rpt strip_tac >> drule expr_list_member_bound >> strip_tac >>
     fs[runtime_default_compile_defaults_size, expr_child_callback_def, Abbr `lim`] >>
     qpat_assum `!e ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _` irule >>
     fs[supported_exprs_exists_every, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  `!e ty. MEM e args ==>
     lower_value (expr_child_callback lim compile_expr) (ce with ce_vars := vars) ty e =
     lower_value (expr_child_callback lim compile_expr) ce ty e` by
    (rpt strip_tac >> irule runtime_default_lower_value_vars >> simp[]) >>
  `!ts. MAP (type_memory_bytes (ce with ce_vars := vars)) ts =
         MAP (type_memory_bytes ce) ts` by simp[MAP_EQ_f, runtime_default_value_size] >>
  `!ann elem b elems.
     MEM (Builtin ann (MakeArray elem b) elems) args ==>
     compile_multi_exprs (expr_child_callback lim compile_expr) (ce with ce_vars := vars) elems =
     compile_multi_exprs (expr_child_callback lim compile_expr) ce elems` by
    (rpt strip_tac >> irule runtime_default_multi_exprs_vars >> rpt strip_tac >>
     `expr_size e < list_size expr_size args` by
       (`expr_size (Builtin ann (MakeArray elem b) elems) <
          list_size expr_size args` by (irule expr_list_member_bound >> simp[]) >>
        `expr_size e < list_size expr_size elems` by (irule expr_list_member_bound >> simp[]) >>
        fs[expr_size_def]) >>
     `runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e` by
       (conj_tac
        >- (qpat_assum `EVERY (runtime_constant_expr mods) args`
              (qspec_then `Builtin ann (MakeArray elem b) elems` mp_tac
                o REWRITE_RULE [EVERY_MEM]) >>
            simp[runtime_constant_expr_def, runtime_constant_builtin_def, constant_builtin_def,
              EVERY_MEM] >> metis_tac[constant_expr_runtime_constant]) >>
        `~supported_expr_exists ^bad_builtin_arity
           (Builtin ann (MakeArray elem b) elems)` by
          (qpat_assum `~supported_exprs_exists _ args`
             (mp_tac o REWRITE_RULE [supported_exprs_exists_every, EXISTS_MEM]) >>
           metis_tac[]) >>
        fs[supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
        metis_tac[]) >>
     simp[expr_child_callback_def, runtime_default_compile_defaults_size, Abbr `lim`] >>
     qpat_assum `!child ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _` irule >>
     fs[Abbr `lim`]) >>
  Cases_on `bi` >> fs[runtime_constant_builtin_def, constant_builtin_def]
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _ _`]
  >- (simp[compile_builtin_dispatch_body_def, LET_THM, runtime_default_value_size] >>
      BasicProvers.TOP_CASE_TAC >>
      simp[compile_make_array_def, comp_bind_def, comp_ignore_bind_def,
        runtime_default_make_array_vars, runtime_default_make_tuple_vars])
  >~ [`compile_builtin_dispatch_body _ _ _ _ NamedConst _ _`]
  >- (gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute, Excl "expr_child_callback_def"] >>
      simp[compile_builtin_dispatch_body_def, LET_THM, Excl "expr_child_callback_def"])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (BoolChain _ _) _ _`]
  >- (gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute, Excl "expr_child_callback_def"] >>
      rename1 `compile_builtin_dispatch_body _ _ _ _ (BoolChain d n) [arg] _` >>
      `~supported_expr_exists ^bad_builtin_arity arg` by
        fs[supported_exprs_exists_every] >>
      `EVERY (runtime_constant_expr mods) (bool_chain_operands d (n - 1) arg)` by
        simp[runtime_constant_bool_chain_operands] >>
      `EVERY (\e. ~supported_expr_exists ^bad_builtin_arity e)
         (bool_chain_operands d (n - 1) arg)` by simp[bool_chain_operands_supported] >>
      `expr_size arg < list_size expr_size [arg]` by simp[expr_list_member_bound] >>
      `!r exit_lbl.
        compile_bool_chain_ops (expr_child_callback lim compile_expr)
          (ce with ce_vars := vars) d r exit_lbl (bool_chain_operands d (n - 1) arg) =
        compile_bool_chain_ops (expr_child_callback lim compile_expr)
          ce d r exit_lbl (bool_chain_operands d (n - 1) arg)` by
        (rpt gen_tac >> irule compile_bool_chain_ops_lower_value_cong >>
         qx_gen_tac `e` >> strip_tac >>
         `expr_size e <= expr_size arg` by metis_tac[bool_chain_operand_size] >>
         `expr_size e < list_size expr_size [arg]` by decide_tac >>
         `runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e` by
           fs[EVERY_MEM] >>
         irule runtime_default_lower_value_vars >> gen_tac >>
         simp[expr_child_callback_def, runtime_default_compile_defaults_size] >>
         IF_CASES_TAC >> simp[] >>
         qpat_assum `!child ce' ty st. _ ==> _ ==> compile_expr _ _ _ _ = _` irule >>
         simp[]) >>
      simp[compile_builtin_dispatch_body_def, LET_THM, Excl "expr_child_callback_def"]) >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute, Excl "expr_child_callback_def"] >>
  asm_simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    runtime_default_value_size, runtime_default_unwrap_vars,
    runtime_default_builtin_env_vars, runtime_default_acc_vars,
    Excl "expr_child_callback_def"]
  >~ [`compile_builtin_len`]
  >- (simp_tac bool_ss [expr_child_callback_def, runtime_default_compile_defaults_size,
          arithmeticTheory.ADD_COMM] >>
      qpat_assum `!ty st. (if _ then _ else _) = _` (fn th =>
        PURE_REWRITE_TAC [SIMP_RULE bool_ss [runtime_default_compile_defaults_size,
          arithmeticTheory.ADD_COMM] th]) >> REFL_TAC) >>
  `!ty st. expr_child_callback lim compile_expr (ce with ce_vars := vars) ty h' st =
          expr_child_callback lim compile_expr ce ty h' st` by
    (qx_genl_tac [`cb_ty`, `cb_st`] >>
     simp_tac bool_ss [expr_child_callback_def, runtime_default_compile_defaults_size] >>
     qpat_assum `!e ty st. (e = h \/ e = h') ==> (if _ then _ else _) = _`
       (qspecl_then [`h'`, `cb_ty`, `cb_st`] mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [runtime_default_compile_defaults_size, arithmeticTheory.ADD_COMM]) >>
  qpat_assum `!ty st. expr_child_callback _ _ _ _ h' _ = _`
    (fn th => PURE_REWRITE_TAC [th]) >>
  Cases_on `h'` >>
  TRY (qpat_assum `runtime_constant_expr mods (Name _ _)`
       (mp_tac o REWRITE_RULE [runtime_constant_expr_def]) >> simp[]) >>
  simp_tac (srw_ss()) [Excl "expr_child_callback_def"] >>
  TRY (rename1 `Builtin _ builtin args'` >> Cases_on `builtin` >>
       asm_simp_tac (srw_ss()) [Excl "expr_child_callback_def"])
QED

Resume runtime_default_compile_vars[type_builtin]:
  Cases_on `tb` >> fs[constant_type_builtin_def, compile_type_builtin_dispatch_body_def,
    runtime_default_value_size, LET_THM]
QED

Finalise runtime_default_compile_vars

Theorem runtime_default_lower_value_vars_frame:
  runtime_constant_expr mods e /\ ~supported_expr_exists ^bad_builtin_arity e ==>
  lower_value compile_expr (ce with ce_vars := vars) ty e =
    lower_value compile_expr ce ty e /\
  lower_value compile_expr (ce with ce_vars := vars) ty (gas_shadow_expr e) =
    lower_value compile_expr ce ty (gas_shadow_expr e)
Proof
  strip_tac >>
  `!e. (^bad_builtin_arity) (gas_shadow_expr e) = (^bad_builtin_arity) e` by
    (Cases >> simp[gas_shadow_expr_def] >>
     rw[gas_shadow_builtin_def] >> simp[builtin_args_length_ok_def]) >>
  `~supported_expr_exists ^bad_builtin_arity (gas_shadow_expr e)` by
    (`supported_expr_exists ^bad_builtin_arity (gas_shadow_expr e) =
      supported_expr_exists ^bad_builtin_arity e` by
       (match_mp_tac (CONJUNCT1 gas_shadow_expr_exists_invariant) >>
        asm_rewrite_tac[]) >>
     asm_rewrite_tac[]) >>
  `runtime_constant_expr mods (gas_shadow_expr e)` by
    metis_tac[runtime_constant_expr_gas_shadow] >>
  conj_tac >>
  irule runtime_default_lower_value_vars >>
  metis_tac[runtime_default_compile_vars]
QED
