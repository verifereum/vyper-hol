(* Real and shadow compiler cuts for a Slice of self.code. *)
Theory bodySliceSelfCompileMods
Ancestors
  bodyPtrBytestringBuiltinsExternalSlice exprSimFullBundleProps
  exprBopLowering exprLoweringProps bodyFullShared gasShadowCompileStmtHelpers
  gasShadowCompilePure gasShadowCompileBase exprSimHypsDefs exprLowering
  compileEnv fragExec gasShadow

val cut = ``\cenv ty e sa sb sha shb op.
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  sa.cs_next_var <= sb.cs_next_var``;

Theorem self_slice_layout[local]:
  compile_expr cenv ty (Builtin a (Slice n)
    [Builtin ct (Acc Code) [Builtin at (Env SelfAddr) []];start;len]) sa = (vv,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ?x s1 y s2 out. lower_value compile_expr cenv ty start sa = (x,s1) /\
    lower_value compile_expr cenv ty len s1 = (y,s2) /\
    compile_slice_code x y (type_memory_bytes cenv a) s2 = (out,sb) /\
    vv = LocatedValue a (mk_ptr out LocMemory) /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
    local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2
Proof
  strip_tac >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Builtin _ (Slice _) _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       lower_value_child_call,is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `lower_value compile_expr cenv ty start sa = (x,s1)` >>
  rename1 `lower_value compile_expr cenv ty len s1 = (y,s2)` >>
  Cases_on `compile_slice_code x y (type_memory_bytes cenv a) s2` >>
  rename1 `compile_slice_code x y _ s2 = (out,_)` >> gvs[as_ptr_val_def] >>
  rename1 `compile_slice_code x y _ s2 = (out,sb)` >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[compile_expr_grows,ci_mono_def] >>
  `cs_extends s2 sb` by
    (drule compile_slice_code_stages >> strip_tac >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    (conj_asm1_tac >> irule local_ptrs_reserved_next_var >> fs[ci_mono_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[]
QED

Theorem slice_self_compile_mods:
  compile_expr cenv ty (Builtin a (Slice n)
    [Builtin ct (Acc Code) [Builtin at (Env SelfAddr) []];start;len]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin a (Slice n)
    [Builtin ct (Acc Code) [Builtin at (Env SelfAddr) []];start;len])) sha = (vv,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  local_ptrs_reserved cenv sa ==>
  ?x s1 y s2 sh1 sh2 out sc sd se sf limit data.
    ^cut cenv ty start sa s1 sha sh1 x /\ ^cut cenv ty len s1 s2 sh1 sh2 y /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\
    local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
    vv = LocatedValue a (mk_ptr out LocMemory) /\ fn_has_code s2 sb func /\
    emit_op CODESIZE [] s2 = (limit,sc) /\
    compile_assert_slice_bounds x y limit sc = ((),sd) /\
    compile_slice_out_buf (type_memory_bytes cenv a) sd = ((out,data),se) /\
    emit_void CODECOPY [data;x;y] se = ((),sf) /\
    emit_void MSTORE [out;y] sf = ((),sb)
Proof
  BETA_TAC >> strip_tac >> fs[expr_sim_full_code_def] >>
  drule_all_then (qx_choosel_then [`x`,`s1`,`y`,`s2`,`out`] strip_assume_tac) self_slice_layout >>
  `local_ptrs_reserved (gas_shadow_env T cenv) sha` by
    (irule local_ptrs_reserved_gas_shadow >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def,gas_shadow_builtin_def]) >>
  drule_all_then (qx_choosel_then [`hx`,`sh1`,`hy`,`sh2`,`hout`] strip_assume_tac) self_slice_layout >>
  `hx = x /\ gas_shadow_state s1 sh1` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ cenv _ start _ = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr start) _ = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  `hy = y /\ gas_shadow_state s2 sh2` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ cenv _ len _ = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr len) _ = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_assum `compile_slice_code _ _ _ s2 = _`
    (mp_then Any (qx_choosel_then [`sc`,`sd`,`se`,`sf`,`data`,`limit`] strip_assume_tac) compile_slice_code_stages) >>
  qexistsl_tac [`x`,`s1`,`y`,`s2`,`sh1`,`sh2`,`out`,`sc`,`sd`,`se`,`sf`,`limit`,`data`] >>
  gvs[expr_sim_full_code_def,ci_mono_def]
QED
