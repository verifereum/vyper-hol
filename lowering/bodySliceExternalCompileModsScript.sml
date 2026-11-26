(* Code cuts for the external-code branch of Slice, before any evaluation. *)
Theory bodySliceExternalCompileMods
Ancestors
  exprSimSliceExtcodeContext exprSimSliceExtcode exprSimFullBundleProps
  exprSimHypsDefs exprBopLowering bodyFullShared exprLowering exprLoweringProps
  gasShadow gasShadowCompileBase gasShadowCompilePure gasShadowCompileStmtHelpers

Theorem slice_external_dispatch[local]:
  compile_expr cenv ty (Builtin ann (Slice n)
    [Builtin ct (Acc Code) [addr];start;len]) sa = (vv,sb) ==>
  ~is_self_code (Builtin ct (Acc Code) [addr]) ==>
  ?x s1 y s2 aop s3.
    lower_value compile_expr cenv ty start sa = (x,s1) /\
    lower_value compile_expr cenv ty len s1 = (y,s2) /\
    lower_value compile_expr cenv ty addr s2 = (aop,s3) /\
    as_ptr_val ann LocMemory
      (compile_slice_extcode aop x y (type_memory_bytes cenv ann) s3) = (vv,sb)
Proof
  rpt strip_tac >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Builtin _ (Slice _) _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       lower_value_child_call,is_extcode_def,extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `lower_value _ _ _ start sa = (x,s1)` >>
  rename1 `lower_value _ _ _ len s1 = (y,s2)` >>
  rename1 `lower_value _ _ _ addr s2 = (aop,s3)` >>
  qexistsl_tac [`x`,`s1`,`y`,`s2`,`aop`,`s3`] >> simp[]
QED

Theorem slice_external_child_shadow[local]:
  gas_shadow_state sa sha /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (hop,shb) ==>
  hop = op /\ gas_shadow_state sb shb
Proof
  strip_tac >> irule gas_shadow_step >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ e _ = _` (irule_at Any) >>
  simp[gas_shadow_stmt_lower_value_env]
QED

val child = ``\ty e sa sb sha shb op.
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  sa.cs_next_var <= sb.cs_next_var``;

Theorem slice_external_compile_mods:
  e = Builtin ann (Slice n) [Builtin ct (Acc Code) [addr];start;len] /\
  ann = BaseT (BytesT (Dynamic n)) /\ N = type_memory_bytes cenv ann /\
  ~is_self_code (Builtin ct (Acc Code) [addr]) /\
  compile_expr cenv ty e sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (hvv,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  local_ptrs_reserved cenv sa ==>
  ?s1 s2 s3 sh1 sh2 sh3 x y aop out sc sd se sf src_len dst.
    ^child ty start sa s1 sha sh1 x /\ ^child ty len s1 s2 sh1 sh2 y /\
    ^child ty addr s2 s3 sh2 sh3 aop /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sb /\
    fn_has_code s3 sb func /\
    compile_slice_extcode aop x y N s3 = (out,sb) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\
    emit_op EXTCODESIZE [aop] s3 = (src_len,sc) /\
    compile_assert_slice_bounds x y src_len sc = ((),sd) /\
    compile_slice_out_buf N sd = ((out,dst),se) /\
    emit_void EXTCODECOPY [aop;dst;x;y] se = ((),sf) /\
    emit_void MSTORE [out;y] sf = ((),sb)
Proof
  BETA_TAC >> strip_tac >>
  qpat_x_assum `e = Builtin _ (Slice _) _` SUBST_ALL_TAC >>
  fs[expr_sim_full_code_def] >>
  `hvv = vv` by
    (irule (cj 1 gas_shadow_step) >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` (irule_at Any) >>
     qpat_assum `compile_expr _ _ (Builtin _ (Slice _) _) _ = _` (irule_at Any) >>
     simp[gas_shadow_stmt_compile_expr_env]) >>
  qpat_x_assum `hvv = vv` SUBST_ALL_TAC >>
  drule_all slice_external_dispatch >> strip_tac >>
  drule_all slice_extcode_pipeline_context >> strip_tac >>
  `~is_self_code (Builtin ct (Acc Code) [gas_shadow_expr addr])` by
    (qspec_then `Builtin ct (Acc Code) [addr]` mp_tac (GEN_ALL gas_shadow_is_self_code) >>
     pure_rewrite_tac[gas_shadow_expr_def,gas_shadow_builtin_def,listTheory.MAP] >> simp[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (mp_tac o SIMP_RULE (srw_ss())
       [gas_shadow_expr_def,gas_shadow_builtin_def,listTheory.MAP]) >>
  disch_then
    (drule_then (strip_assume_tac o REWRITE_RULE [type_memory_bytes_gas_shadow_env]) o
      MATCH_MP slice_external_dispatch) >>
  `local_ptrs_reserved (gas_shadow_env T cenv) sha` by
    (irule local_ptrs_reserved_gas_shadow >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `as_ptr_val _ _ (compile_slice_extcode _ _ _ _ _) = (_,shb)`
    (mp_then Any mp_tac slice_extcode_pipeline_context) >>
  disch_then drule_all >> strip_tac >>
  rename1 `lower_value _ cenv _ start sa = (x,s1)` >>
  rename1 `lower_value _ cenv _ len s1 = (y,s2)` >>
  rename1 `lower_value _ cenv _ addr s2 = (aop,s3)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr start) sha = (hx,sh1)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr len) sh1 = (hy,sh2)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr addr) sh2 = (haop,sh3)` >>
  `hx = x /\ gas_shadow_state s1 sh1` by
    (irule slice_external_child_shadow >>
     qpat_assum `lower_value _ cenv _ start _ = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr start) _ = _` (irule_at Any) >> simp[]) >>
  `hy = y /\ gas_shadow_state s2 sh2` by
    (irule slice_external_child_shadow >>
     qpat_assum `lower_value _ cenv _ len _ = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr len) _ = _` (irule_at Any) >> simp[]) >>
  `haop = aop /\ gas_shadow_state s3 sh3` by
    (irule slice_external_child_shadow >>
     qpat_assum `lower_value _ cenv _ addr _ = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr addr) _ = _` (irule_at Any) >> simp[]) >>
  Cases_on `compile_slice_extcode aop x y (type_memory_bytes cenv ann) s3` >>
  rename1 `compile_slice_extcode aop x y _ s3 = (out,scut)` >>
  qpat_x_assum `as_ptr_val _ _ (out,scut) = _`
    (strip_assume_tac o REWRITE_RULE [as_ptr_val_def,pairTheory.PAIR_EQ]) >>
  qpat_x_assum `scut = sb` SUBST_ALL_TAC >>
  drule slice_extcode_decompose >> strip_tac >>
  rename1 `emit_op EXTCODESIZE [aop] s3 = (src_len,sc)` >>
  rename1 `compile_assert_slice_bounds x y src_len sc = ((),sd)` >>
  rename1 `compile_slice_out_buf _ sd = ((out,dst),se)` >>
  rename1 `emit_void EXTCODECOPY _ se = ((),sf)` >>
  qexistsl_tac [`s1`,`s2`,`s3`,`sh1`,`sh2`,`sh3`,`x`,`y`,`aop`,`out`,`sc`,`sd`,`se`,`sf`,`src_len`,`dst`] >>
  gvs[expr_sim_full_code_def,ci_mono_def]
QED
