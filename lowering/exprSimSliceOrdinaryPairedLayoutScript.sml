(* Paired compiler cuts for ordinary Slice, including the capture gap. *)
Theory exprSimSliceOrdinaryPairedLayout
Ancestors
  exprSimSliceOrdinaryContext exprSimSliceSource exprSimHypsDefs exprLowering
  exprBopLowering bodyFullShared gasShadow gasShadowCompilePure
  gasShadowCompileBuiltinBytes gasShadowCompileContext gasShadowCompileStmtHelpers
  gasShadowCompileBase gasShadowState vyperAST exprLoweringProps loweringStateRelDefs

fun shadow_cut real shadow rule =
  irule bodyFullSharedTheory.gas_shadow_step >>
  qpat_assum real (irule_at Any) >>
  qpat_assum shadow (irule_at Any) >> simp[rule]

(* Both capture forms pass the same operands to the common slice tail. *)
Theorem slice_ordinary_paired_layout:
  ~is_self_code src /\ ~is_extcode src /\
  compile_expr cenv ty (Builtin ann (Slice n) [src;start;len]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (Slice n) [src;start;len])) shadow_sa =
    (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa ==>
  ?src_op src_len src_data start_op len_op
   st1 sc sd se shadow_s1 shadow_sc shadow_sd shadow_se.
    lower_value compile_expr cenv (expr_type src) src sa = (src_op,st1) /\
    lower_value compile_expr cenv ty start sc = (start_op,sd) /\
    lower_value compile_expr cenv ty len sd = (len_op,se) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type src)
      (gas_shadow_expr src) shadow_sa = (src_op,shadow_s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr start) shadow_sc = (start_op,shadow_sd) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr len) shadow_sd = (len_op,shadow_se) /\
    (if is_bytestring_type (expr_type src) then
       compile_bytestring_src src_op st1 = ((src_len,src_data),sc) /\
       compile_bytestring_src src_op shadow_s1 = ((src_len,src_data),shadow_sc)
     else
       ?buf sm shadow_sm.
         compile_alloc_buffer 32 st1 = (buf,sm) /\
         compile_alloc_buffer 32 shadow_s1 = (buf,shadow_sm) /\
         gas_shadow_state sm shadow_sm /\
         emit_void MSTORE [buf.buf_operand;src_op] sm = ((),sc) /\
         emit_void MSTORE [buf.buf_operand;src_op] shadow_sm = ((),shadow_sc) /\
         src_len = Lit (n2w (fixed_bytes_size (expr_type src))) /\
         src_data = buf.buf_operand) /\
    as_ptr_val ann LocMemory
      (compile_slice_data src_len src_data start_op len_op (type_memory_bytes cenv ann) se) =
      (vv,sb) /\
    as_ptr_val ann LocMemory
      (compile_slice_data src_len src_data start_op len_op (type_memory_bytes cenv ann) shadow_se) =
      (vv,shadow_sb) /\
    gas_shadow_state st1 shadow_s1 /\ gas_shadow_state sc shadow_sc /\
    gas_shadow_state sd shadow_sd /\ gas_shadow_state se shadow_se /\
    ci_mono sa st1 /\ ci_mono st1 sc /\ ci_mono sc sd /\ ci_mono sd se /\ ci_mono se sb /\
    ci_mono shadow_sa shadow_s1 /\ ci_mono shadow_s1 shadow_sc /\
    ci_mono shadow_sc shadow_sd /\ ci_mono shadow_sd shadow_se /\ ci_mono shadow_se shadow_sb /\
    fn_has_code sa st1 func /\ fn_has_code st1 sc func /\
    fn_has_code sc sd func /\ fn_has_code sd se func /\ fn_has_code se sb func /\
    fn_has_code shadow_sa shadow_s1 shadow_func /\ fn_has_code shadow_s1 shadow_sc shadow_func /\
    fn_has_code shadow_sc shadow_sd shadow_func /\ fn_has_code shadow_sd shadow_se shadow_func /\
    fn_has_code shadow_se shadow_sb shadow_func /\
    local_ptrs_reserved cenv st1 /\ local_ptrs_reserved cenv sc /\
    local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_s1 /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_sc /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_sd /\
    local_ptrs_reserved (gas_shadow_env T cenv) shadow_se
Proof
  strip_tac >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. names_builtin bt xs ==> _` kall_tac >>
  `local_ptrs_reserved cenv shadow_sa` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[gas_shadow_state_def]) >>
  `local_ptrs_reserved (gas_shadow_env T cenv) shadow_sa` by
    (pure_rewrite_tac[local_ptrs_reserved_def,gas_shadow_env_fields] >>
     pure_rewrite_tac[GSYM local_ptrs_reserved_def] >> first_assum ACCEPT_TAC) >>
  Cases_on `is_bytestring_type (expr_type src)` >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    slice_dispatch_bytestring,slice_dispatch_fixed,lower_value_child_call] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def,gas_shadow_builtin_def,compile_expr_builtin_dispatch,
    compile_builtin_dispatch_component_eq,slice_dispatch_bytestring,slice_dispatch_fixed,
    lower_value_child_call] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr cenv (expr_type src) src sa = (src_op,st1)` >>
  qmatch_asmsub_rename_tac
    `lower_value compile_expr _ (expr_type src) (gas_shadow_expr src) shadow_sa =
      (shadow_src,shadow_s1)` >>
  `shadow_src = src_op /\ gas_shadow_state st1 shadow_s1` by
    shadow_cut `lower_value _ _ _ src sa = (src_op,st1)`
      `lower_value _ _ _ (gas_shadow_expr src) shadow_sa = _`
      gas_shadow_stmt_lower_value_env >>
  qpat_assum `shadow_src = src_op` SUBST_ALL_TAC >>
  (FIRST [
    (qpat_assum `is_bytestring_type (expr_type src)` (K ALL_TAC) >>
     qmatch_asmsub_rename_tac
       `compile_bytestring_src src_op st1 = ((src_len,src_data),sc)` >>
     qmatch_asmsub_rename_tac
       `compile_bytestring_src src_op shadow_s1 = ((shadow_len,shadow_data),shadow_sc)` >>
     `(shadow_len,shadow_data) = (src_len,src_data) /\ gas_shadow_state sc shadow_sc` by
       shadow_cut `compile_bytestring_src src_op st1 = _`
         `compile_bytestring_src src_op shadow_s1 = _` gas_shadow_compiles_bytestring_src >>
     fs[pairTheory.PAIR_EQ] >>
     qpat_assum `shadow_len = src_len` SUBST_ALL_TAC >>
     qpat_assum `shadow_data = src_data` SUBST_ALL_TAC >>
     `ci_mono st1 sc /\ ci_mono shadow_s1 shadow_sc` by
       metis_tac[ci_mono_compile_bytestring_src,pairTheory.SND]),
    (qpat_assum `~is_bytestring_type (expr_type src)` (K ALL_TAC) >>
     qmatch_asmsub_rename_tac `compile_alloc_buffer 32 st1 = (buf,sm)` >>
     qmatch_asmsub_rename_tac `compile_alloc_buffer 32 shadow_s1 = (shadow_buf,shadow_sm)` >>
     `shadow_buf = buf /\ gas_shadow_state sm shadow_sm` by
       shadow_cut `compile_alloc_buffer 32 st1 = _`
         `compile_alloc_buffer 32 shadow_s1 = _` gas_shadow_compiles_alloc_buffer >>
     qpat_assum `shadow_buf = buf` SUBST_ALL_TAC >>
     qmatch_asmsub_rename_tac `emit_void MSTORE [buf.buf_operand;src_op] sm = (u,sc)` >>
     qmatch_asmsub_rename_tac
       `emit_void MSTORE [buf.buf_operand;src_op] shadow_sm = (shadow_u,shadow_sc)` >>
     `shadow_u = u /\ gas_shadow_state sc shadow_sc` by
       shadow_cut `emit_void MSTORE _ sm = _`
         `emit_void MSTORE _ shadow_sm = _` gas_shadow_compiles_emit_void >>
     qpat_assum `shadow_u = u` SUBST_ALL_TAC >> Cases_on `u` >>
     `ci_mono st1 sc /\ ci_mono shadow_s1 shadow_sc` by
       (conj_tac >> irule slice_fixed_capture_ci_mono >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any)))]) >>
  qmatch_asmsub_rename_tac `lower_value _ _ ty start sc = (start_op,sd)` >>
  qmatch_asmsub_rename_tac `lower_value _ _ ty len sd = (len_op,se)` >>
  qmatch_asmsub_rename_tac
    `lower_value _ _ ty (gas_shadow_expr start) shadow_sc = (shadow_start,shadow_sd)` >>
  qmatch_asmsub_rename_tac
    `lower_value _ _ ty (gas_shadow_expr len) shadow_sd = (shadow_count,shadow_se)` >>
  `shadow_start = start_op /\ gas_shadow_state sd shadow_sd` by
    shadow_cut `lower_value _ _ _ start sc = _`
      `lower_value _ _ _ (gas_shadow_expr start) shadow_sc = _`
      gas_shadow_stmt_lower_value_env >>
  qpat_assum `shadow_start = start_op` SUBST_ALL_TAC >>
  `shadow_count = len_op /\ gas_shadow_state se shadow_se` by
    shadow_cut `lower_value _ _ _ len sd = _`
      `lower_value _ _ _ (gas_shadow_expr len) shadow_sd = _`
      gas_shadow_stmt_lower_value_env >>
  qpat_assum `shadow_count = len_op` SUBST_ALL_TAC >>
  qpat_assum `as_ptr_val _ _ (compile_slice_data _ _ _ _ _ se) = _`
    (mp_then Any mp_tac slice_ordinary_pipeline_context) >>
  disch_then drule_all >> strip_tac >>
  qpat_assum `as_ptr_val _ _ (compile_slice_data _ _ _ _ _ shadow_se) = _`
    (mp_then Any mp_tac slice_ordinary_pipeline_context) >>
  disch_then drule_all >> strip_tac >>
  simp[]
QED
