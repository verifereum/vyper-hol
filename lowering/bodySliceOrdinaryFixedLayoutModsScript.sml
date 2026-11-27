(* Compiler cuts of ordinary Slice on a fixed byte word. *)
Theory bodySliceOrdinaryFixedLayoutMods
Ancestors
  bodyFullShared exprSimSliceOrdinaryContext exprSimSliceSource
  exprBopLowering exprSimHypsDefs exprLowering exprLoweringProps
  gasShadow gasShadowCompileBuiltinBytes gasShadowCompileContext
  gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowCompileBase
  gasShadowState fragExec loweringHalt emitHelperProps

Triviality fixed_slice_layout:
  ~is_self_code src /\ ~is_extcode src /\ expr_type src = BaseT (BytesT (Fixed m)) /\
  compile_expr cenv ty (Builtin ann (Slice n) [src;start;len]) sa = (vv,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ?op sm buf salloc sc x sd y se out.
    lower_value compile_expr cenv (expr_type src) src sa = (op,sm) /\
    compile_alloc_buffer 32 sm = (buf,salloc) /\
    emit_void MSTORE [buf.buf_operand;op] salloc = ((),sc) /\
    lower_value compile_expr cenv ty start sc = (x,sd) /\
    lower_value compile_expr cenv ty len sd = (y,se) /\
    compile_slice_data (Lit (n2w m)) buf.buf_operand x y (type_memory_bytes cenv ann) se = (out,sb) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\
    fn_has_code sa sm func /\ fn_has_code sm sc func /\
    fn_has_code sm salloc func /\ fn_has_code salloc sc func /\
    fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sb func /\
    local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv salloc /\
    local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
    ci_mono sa sm /\ ci_mono sm sc /\ ci_mono sm salloc /\ ci_mono salloc sc /\
    ci_mono sc sd /\ ci_mono sd se /\ ci_mono se sb /\
    salloc.cs_next_id = sm.cs_next_id + 1 /\ sc.cs_next_id = salloc.cs_next_id + 1 /\
    sm.cs_next_id < sc.cs_next_id /\
    salloc.cs_next_var = sm.cs_next_var + 1 /\ sc.cs_next_var = salloc.cs_next_var
Proof
  strip_tac >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [src;start;len]` by metis_tac[] >>
  qpat_x_assum `!bt xs. names_builtin bt xs ==> _` kall_tac >>
  `~is_bytestring_type (expr_type src)` by simp[compileEnvTheory.is_bytestring_type_def] >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       slice_dispatch_fixed,lower_value_child_call,fixed_bytes_size_def,
       compileEnvTheory.is_bytestring_type_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qmatch_asmsub_rename_tac `lower_value compile_expr cenv _ src sa = (op,sm)` >>
  qmatch_asmsub_rename_tac `compile_alloc_buffer 32 sm = (buf,salloc)` >>
  qmatch_asmsub_rename_tac `emit_void MSTORE [buf.buf_operand;op] salloc = (u,sc)` >>
  Cases_on `u` >>
  qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty start sc = (x,sd)` >>
  qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty len sd = (y,se)` >>
  `ci_mono sm sc` by (irule slice_fixed_capture_ci_mono >> simp[] >> goal_assum (drule_at Any)) >>
  drule_all_then strip_assume_tac slice_ordinary_pipeline_context >>
  `ci_mono sm salloc` by (qspec_then `32` (qspec_then `sm` mp_tac) ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono salloc sc` by (qspecl_then [`MSTORE`,`[buf.buf_operand;op]`,`salloc`] mp_tac ci_mono_emit_void >> simp[]) >>
  `fn_has_code sm salloc func /\ fn_has_code salloc sc func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv salloc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  drule_then strip_assume_tac compile_alloc_buffer_parts >>
  drule_then strip_assume_tac emitted_insts_emit_void >>
  `sm.cs_next_id < sc.cs_next_id` by decide_tac >>
  Cases_on `compile_slice_data (Lit (n2w m)) buf.buf_operand x y (type_memory_bytes cenv ann) se` >>
  qmatch_asmsub_rename_tac `compile_slice_data _ _ _ _ _ se = (out,_)` >>
  gvs[as_ptr_val_def] >>
  qexistsl_tac [`op`,`sm`,`buf`,`salloc`,`sc`,`x`,`sd`,`y`,`se`,`out`] >> simp[]
QED

Theorem slice_ordinary_fixed_layout_mods:
  ~is_self_code src /\ ~is_extcode src /\ expr_type src = BaseT (BytesT (Fixed m)) /\
  compile_expr cenv ty (Builtin ann (Slice n) [src;start;len]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (Slice n) [src;start;len])) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa ==>
  ?op sm buf salloc sc x sd y se out shadow_sm shadow_alloc shadow_sc shadow_sd shadow_se.
    lower_value compile_expr cenv (expr_type src) src sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type src)
      (gas_shadow_expr src) shadow_sa = (op,shadow_sm) /\
    compile_alloc_buffer 32 sm = (buf,salloc) /\
    compile_alloc_buffer 32 shadow_sm = (buf,shadow_alloc) /\
    emit_void MSTORE [buf.buf_operand;op] salloc = ((),sc) /\
    emit_void MSTORE [buf.buf_operand;op] shadow_alloc = ((),shadow_sc) /\
    lower_value compile_expr cenv ty start sc = (x,sd) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr start) shadow_sc = (x,shadow_sd) /\
    lower_value compile_expr cenv ty len sd = (y,se) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr len) shadow_sd = (y,shadow_se) /\
    compile_slice_data (Lit (n2w m)) buf.buf_operand x y (type_memory_bytes cenv ann) se = (out,sb) /\
    compile_slice_data (Lit (n2w m)) buf.buf_operand x y (type_memory_bytes cenv ann) shadow_se = (out,shadow_sb) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state salloc shadow_alloc /\
    gas_shadow_state sc shadow_sc /\ gas_shadow_state sd shadow_sd /\
    gas_shadow_state se shadow_se /\ gas_shadow_state sb shadow_sb /\
    fn_has_code sa sm func /\ fn_has_code sm sc func /\
    fn_has_code sm salloc func /\ fn_has_code salloc sc func /\
    fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sc shadow_func /\
    fn_has_code shadow_sm shadow_alloc shadow_func /\ fn_has_code shadow_alloc shadow_sc shadow_func /\
    fn_has_code shadow_sc shadow_sd shadow_func /\ fn_has_code shadow_sd shadow_se shadow_func /\
    fn_has_code shadow_se shadow_sb shadow_func /\
    local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv salloc /\
    local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_sm /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_alloc /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_sc /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_sd /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_se /\
    ci_mono sa sm /\ ci_mono sm sc /\ ci_mono sm salloc /\ ci_mono salloc sc /\
    ci_mono sc sd /\ ci_mono sd se /\ ci_mono se sb /\
    ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sc /\
    ci_mono shadow_sm shadow_alloc /\ ci_mono shadow_alloc shadow_sc /\
    ci_mono shadow_sc shadow_sd /\ ci_mono shadow_sd shadow_se /\ ci_mono shadow_se shadow_sb /\
    salloc.cs_next_id = sm.cs_next_id + 1 /\ sc.cs_next_id = salloc.cs_next_id + 1 /\
    sm.cs_next_id < sc.cs_next_id /\
    salloc.cs_next_var = sm.cs_next_var + 1 /\ sc.cs_next_var = salloc.cs_next_var /\
    shadow_alloc.cs_next_id = shadow_sm.cs_next_id + 1 /\
    shadow_sc.cs_next_id = shadow_alloc.cs_next_id + 1 /\
    shadow_sm.cs_next_id < shadow_sc.cs_next_id /\
    shadow_alloc.cs_next_var = shadow_sm.cs_next_var + 1 /\
    shadow_sc.cs_next_var = shadow_alloc.cs_next_var
Proof
  strip_tac >>
  drule_all_then
    (qx_choosel_then [`op`,`sm`,`buf`,`salloc`,`sc`,`x`,`sd`,`y`,`se`,`out`] strip_assume_tac)
    fixed_slice_layout >>
  `local_ptrs_reserved (gas_shadow_env T cenv) shadow_sa` by
    (irule local_ptrs_reserved_gas_shadow >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [Once gas_shadow_expr_def,gas_shadow_builtin_def]) >>
  `~is_self_code (gas_shadow_expr src) /\ ~is_extcode (gas_shadow_expr src) /\
   expr_type (gas_shadow_expr src) = BaseT (BytesT (Fixed m))` by
    simp[gas_shadow_expr_type] >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) sa = _` kall_tac >>
  drule_all_then (qx_choosel_then
    [`shop`,`shadow_sm`,`shbuf`,`shadow_alloc`,`shadow_sc`,`shx`,`shadow_sd`,`shy`,`shadow_se`,`shout`]
    strip_assume_tac) fixed_slice_layout >>
  RULE_ASSUM_TAC (REWRITE_RULE [gas_shadow_expr_type,type_memory_bytes_gas_shadow_env]) >>
  `shop = op /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ src sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr src) shadow_sa = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `shop = op` SUBST_ALL_TAC >>
  `shbuf = buf /\ gas_shadow_state salloc shadow_alloc` by
    (irule gas_shadow_step >>
     qpat_assum `compile_alloc_buffer 32 sm = _` (irule_at Any) >>
     qpat_assum `compile_alloc_buffer 32 shadow_sm = _` (irule_at Any) >>
     simp[gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer]) >>
  qpat_x_assum `shbuf = buf` SUBST_ALL_TAC >>
  `gas_shadow_state sc shadow_sc` by
    (qpat_assum `emit_void MSTORE _ salloc = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ shadow_alloc = _` mp_tac >>
     qpat_assum `gas_shadow_state salloc shadow_alloc` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[gas_shadow_compiles_emit_void,gas_shadow_compiles_def,pairTheory.SND]) >>
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
  qexistsl_tac [`op`,`sm`,`buf`,`salloc`,`sc`,`x`,`sd`,`y`,`se`,`out`,
               `shadow_sm`,`shadow_alloc`,`shadow_sc`,`shadow_sd`,`shadow_se`] >> simp[]
QED
