(* Compiler cuts of ordinary Slice on a dynamic bytestring. *)
Theory bodySliceOrdinaryDynamicLayoutMods
Ancestors
  bodyFullShared exprSimSliceOrdinaryContext exprSimSliceSource
  exprBopLowering exprSimHypsDefs exprLowering exprLoweringProps
  gasShadow gasShadowCompileBuiltinBytes
  gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowCompileBase

Triviality dynamic_slice_layout:
  ~is_self_code src /\ ~is_extcode src /\ is_bytestring_type (expr_type src) /\
  compile_expr cenv ty (Builtin ann (Slice n) [src;start;len]) sa = (vv,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ?op sm limit data sc x sd y se out.
    lower_value compile_expr cenv (expr_type src) src sa = (op,sm) /\
    compile_bytestring_src op sm = ((limit,data),sc) /\
    lower_value compile_expr cenv ty start sc = (x,sd) /\
    lower_value compile_expr cenv ty len sd = (y,se) /\
    compile_slice_data limit data x y (type_memory_bytes cenv ann) se = (out,sb) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\
    fn_has_code sa sm func /\ fn_has_code sm sc func /\
    fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sb func /\
    local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sc /\
    local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
    ci_mono sa sm /\ ci_mono sm sc /\ ci_mono sc sd /\ ci_mono sd se /\ ci_mono se sb
Proof
  strip_tac >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [src;start;len]` by metis_tac[] >>
  qpat_x_assum `!bt xs. names_builtin bt xs ==> _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       slice_dispatch_bytestring,lower_value_child_call] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qmatch_asmsub_rename_tac `compile_bytestring_src op sm = ((limit,data),sc)` >>
  qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty start sc = (x,sd)` >>
  qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty len sd = (y,se)` >>
  `ci_mono sm sc` by
    (qspecl_then [`op`,`sm`] mp_tac ci_mono_compile_bytestring_src >> simp[]) >>
  drule_all_then strip_assume_tac slice_ordinary_pipeline_context >>
  Cases_on `compile_slice_data limit data x y (type_memory_bytes cenv ann) se` >>
  qmatch_asmsub_rename_tac `compile_slice_data _ _ _ _ _ se = (out,_)` >>
  gvs[as_ptr_val_def] >>
  qexistsl_tac [`op`,`sm`,`limit`,`data`,`sc`,`x`,`sd`,`y`,`se`,`out`] >> simp[]
QED

Theorem slice_ordinary_dynamic_layout_mods:
  ~is_self_code src /\ ~is_extcode src /\ is_bytestring_type (expr_type src) /\
  compile_expr cenv ty (Builtin ann (Slice n) [src;start;len]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (Slice n) [src;start;len])) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa ==>
  ?op sm limit data sc x sd y se out shadow_sm shadow_sc shadow_sd shadow_se.
    lower_value compile_expr cenv (expr_type src) src sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type src)
      (gas_shadow_expr src) shadow_sa = (op,shadow_sm) /\
    compile_bytestring_src op sm = ((limit,data),sc) /\
    compile_bytestring_src op shadow_sm = ((limit,data),shadow_sc) /\
    lower_value compile_expr cenv ty start sc = (x,sd) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr start) shadow_sc = (x,shadow_sd) /\
    lower_value compile_expr cenv ty len sd = (y,se) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr len) shadow_sd = (y,shadow_se) /\
    compile_slice_data limit data x y (type_memory_bytes cenv ann) se = (out,sb) /\
    compile_slice_data limit data x y (type_memory_bytes cenv ann) shadow_se = (out,shadow_sb) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state sc shadow_sc /\
    gas_shadow_state sd shadow_sd /\ gas_shadow_state se shadow_se /\
    gas_shadow_state sb shadow_sb /\
    fn_has_code sa sm func /\ fn_has_code sm sc func /\
    fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_sc shadow_func /\
    fn_has_code shadow_sc shadow_sd shadow_func /\
    fn_has_code shadow_sd shadow_se shadow_func /\
    fn_has_code shadow_se shadow_sb shadow_func /\
    local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sc /\
    local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_sm /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_sc /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_sd /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_se /\
    ci_mono sa sm /\ ci_mono sm sc /\ ci_mono sc sd /\ ci_mono sd se /\ ci_mono se sb /\
    ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sc /\
    ci_mono shadow_sc shadow_sd /\ ci_mono shadow_sd shadow_se /\ ci_mono shadow_se shadow_sb
Proof
  strip_tac >>
  drule_all_then
    (qx_choosel_then [`op`,`sm`,`limit`,`data`,`sc`,`x`,`sd`,`y`,`se`,`out`] strip_assume_tac)
    dynamic_slice_layout >>
  `local_ptrs_reserved (gas_shadow_env T cenv) shadow_sa` by
    (irule local_ptrs_reserved_gas_shadow >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [Once gas_shadow_expr_def,gas_shadow_builtin_def]) >>
  qpat_x_assum `compile_expr (gas_shadow_env T cenv) _ (Builtin _ _ _) _ = _`
    (mp_then Any (qspec_then `shadow_func` mp_tac) dynamic_slice_layout) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then
    [`shop`,`shadow_sm`,`shlimit`,`shdata`,`shadow_sc`,`shx`,`shadow_sd`,`shy`,`shadow_se`,`shout`]
    strip_assume_tac) >>
  RULE_ASSUM_TAC (REWRITE_RULE [gas_shadow_expr_type,type_memory_bytes_gas_shadow_env]) >>
  `shop = op /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ src sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr src) shadow_sa = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `shop = op` SUBST_ALL_TAC >>
  `(shlimit,shdata) = (limit,data) /\ gas_shadow_state sc shadow_sc` by
    (irule gas_shadow_step >>
     qpat_assum `compile_bytestring_src op sm = _` (irule_at Any) >>
     qpat_assum `compile_bytestring_src op shadow_sm = _` (irule_at Any) >>
     simp[gas_shadow_compiles_bytestring_src]) >>
  qpat_x_assum `(shlimit,shdata) = (limit,data)`
    (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  qpat_x_assum `shlimit = limit` SUBST_ALL_TAC >>
  qpat_x_assum `shdata = data` SUBST_ALL_TAC >>
  `shx = x /\ gas_shadow_state sd shadow_sd` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ start sc = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr start) shadow_sc = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `shx = x` SUBST_ALL_TAC >>
  `shy = y /\ gas_shadow_state se shadow_se` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ len sd = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr len) shadow_sd = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `shy = y` SUBST_ALL_TAC >>
  `shout = out /\ gas_shadow_state sb shadow_sb` by
    (irule gas_shadow_step >>
     qpat_assum `compile_slice_data _ _ _ _ _ se = _` (irule_at Any) >>
     qpat_assum `compile_slice_data _ _ _ _ _ shadow_se = _` (irule_at Any) >>
     simp[gas_shadow_compiles_slice_data]) >>
  qpat_x_assum `shout = out` SUBST_ALL_TAC >>
  qexistsl_tac [`op`,`sm`,`limit`,`data`,`sc`,`x`,`sd`,`y`,`se`,`out`,
               `shadow_sm`,`shadow_sc`,`shadow_sd`,`shadow_se`] >> simp[]
QED
